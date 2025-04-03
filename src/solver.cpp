//
// Copyright (c) 2006-present Benjamin Kaufmann
//
// This file is part of Clasp. See https://potassco.org/clasp/
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to
// deal in the Software without restriction, including without limitation the
// rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
// sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
// IN THE SOFTWARE.
//
#include <clasp/solver.h>

#include <clasp/clause.h>

#include <potassco/error.h>

#include <unordered_set>
namespace Clasp {
DecisionHeuristic::~DecisionHeuristic() = default;
static SelectFirst g_null_heuristic;
/////////////////////////////////////////////////////////////////////////////////////////
// CCMinRecursive
/////////////////////////////////////////////////////////////////////////////////////////
struct CCMinRecursive {
    enum State { state_open = 0, state_removable = 1, state_poison = 2 };
    [[nodiscard]] uint32_t encodeState(State st) const { return open + static_cast<uint32_t>(st); }
    [[nodiscard]] State    decodeState(uint32_t epoch) const {
        return epoch <= open ? state_open : static_cast<State>(epoch - open);
    }
    void    push(Literal p) { todo.push_back(p); }
    Literal pop() {
        Literal p = todo.back();
        todo.pop_back();
        return p;
    }
    LitVec   todo;
    uint32_t open = 0;
};
/////////////////////////////////////////////////////////////////////////////////////////
// SelectFirst selection strategy
/////////////////////////////////////////////////////////////////////////////////////////
// selects the first free literal
Literal SelectFirst::doSelect(Solver& s) {
    for (auto v : s.vars()) {
        if (s.value(v) == value_free) {
            return selectLiteral(s, v, 0);
        }
    }
    POTASSCO_ASSERT_NOT_REACHED("SelectFirst::doSelect() - precondition violated!\n");
}
/////////////////////////////////////////////////////////////////////////////////////////
// Dirty list
/////////////////////////////////////////////////////////////////////////////////////////
struct Solver::Dirty {
    static constexpr auto min_size = static_cast<std::size_t>(4);
    Dirty()                        = default;
    bool add(Literal p, WatchList& wl, Constraint* c) {
        if (wl.right_size() <= min_size) {
            return false;
        }
        uintptr_t o = wl.left_size() > 0 ? reinterpret_cast<uintptr_t>(wl.left_begin()->head) : 0;
        if (add(wl.right_begin()->con, o, c)) {
            dirty.push_left(p);
        }
        return true;
    }
    bool add(Literal p, WatchList& wl, ClauseHead* c) {
        if (wl.left_size() <= min_size) {
            return false;
        }
        uintptr_t o = wl.right_size() > 0 ? reinterpret_cast<uintptr_t>(wl.right_begin()->con) : 0;
        if (add(wl.left_begin()->head, o, c)) {
            dirty.push_left(p);
        }
        return true;
    }
    bool add(uint32_t dl, ConstraintDB& wl, Constraint* c) {
        if (wl.size() <= min_size) {
            return false;
        }
        if (add(wl[0], 0, c)) {
            dirty.push_right(dl);
        }
        return true;
    }
    template <typename T>
    bool add(T*& list, uintptr_t other, Constraint* c) {
        other |= reinterpret_cast<uintptr_t>(list);
        list   = reinterpret_cast<T*>(Potassco::set_bit(reinterpret_cast<uintptr_t>(list), 0));
        if (c != last) {
            cons.insert(last = c);
        }
        return not Potassco::test_bit(other, 0);
    }
    template <typename T>
    bool test_and_clear(T*& x) const {
        auto old = reinterpret_cast<uintptr_t>(x);
        return Potassco::test_bit(old, 0) && (x = reinterpret_cast<T*>(Potassco::clear_bit(old, 0))) != nullptr;
    }
    template <typename T>
    static constexpr auto getCon(const T& x) -> Constraint* {
        if constexpr (std::is_same_v<T, ClauseWatch>) {
            return x.head;
        }
        else if constexpr (std::is_same_v<T, GenericWatch>) {
            return x.con;
        }
        else {
            return x;
        }
    }
    void cleanup(Watches& watches, DecisionLevels& levels) {
        auto       inCons = [this](const auto& w) { return cons.contains(getCon(w)); };
        const auto maxId  = size32(watches);
        for (auto lit : dirty.left_view()) {
            uint32_t id = lit.id();
            if (id >= maxId) {
                continue;
            }
            WatchList& wl = watches[id];
            if (wl.left_size() && test_and_clear(wl.left_begin()->head)) {
                wl.shrink_left(std::remove_if(wl.left_begin(), wl.left_end(), inCons));
            }
            if (wl.right_size() && test_and_clear(wl.right_begin()->con)) {
                wl.shrink_right(std::remove_if(wl.right_begin(), wl.right_end(), inCons));
            }
        }
        ConstraintDB* db = nullptr;
        for (auto x : dirty.right_view()) {
            if (x < levels.size() && not(db = levels[x].undo)->empty() && test_and_clear(*db->begin())) {
                erase_if(*db, inCons);
            }
        }
        dirty.clear();
        cons.clear();
        last = nullptr;
    }
    using DirtyList     = bk_lib::left_right_sequence<Literal, uint32_t, 0>;
    using ConstraintSet = std::unordered_set<Constraint*>;
    DirtyList     dirty;
    ConstraintSet cons;
    Constraint*   last{nullptr};
};
/////////////////////////////////////////////////////////////////////////////////////////
// Solver: Construction/Destruction/Setup
/////////////////////////////////////////////////////////////////////////////////////////
static PostPropagator* g_sent_list;
Solver::Solver(SharedContext* ctx, uint32_t id)
    : shared_(ctx)
    , heuristic_(&g_null_heuristic)
    , ccMin_(nullptr)
    , postHead_(&g_sent_list)
    , undoHead_(nullptr)
    , enum_(nullptr)
    , memUse_(0)
    , lazyRem_(nullptr)
    , dynLimit_(nullptr)
    , ccInfo_(ConstraintType::conflict)
    , dbIdx_(0)
    , lastSimp_(0)
    , shufSimp_(0)
    , initPost_(0)
    , splitReq_(false) {
    auto trueVar = assign_.addVar();
    assign_.setValue(trueVar, value_true);
    markSeen(trueVar);
    strategy_.id = id;
}

Solver::~Solver() { freeMem(); }

void Solver::freeMem() {
    Clasp::destroyDB(constraints_, nullptr, false);
    Clasp::destroyDB(learnts_, nullptr, false);
    post_.clear();
    if (auto e = std::exchange(enum_, nullptr)) {
        e->destroy();
    }
    resetHeuristic(nullptr);
    PodVector<WatchList>::destruct(watches_);
    // free undo lists
    // first those still in use
    for (auto& level : levels_) { delete level.undo; }
    // then those in the free list
    for (ConstraintDB* x = undoHead_; x;) {
        ConstraintDB* t = x;
        x               = reinterpret_cast<ConstraintDB*>(x->front());
        delete t;
    }
    ccMin_.reset();
    memUse_ = 0;
}

SatPreprocessor*   Solver::satPrepro() const { return shared_->satPrepro.get(); }
const SolveParams& Solver::searchConfig() const { return shared_->configuration()->search(id()); }

void Solver::reset() {
    SharedContext* myCtx = shared_;
    uint32_t       myId  = strategy_.id;
    this->~Solver();
    new (this) Solver(myCtx, myId);
}
void Solver::setHeuristic(DecisionHeuristic* h) {
    POTASSCO_CHECK_PRE(h, "Heuristic must not be null");
    resetHeuristic(this, h);
}
void Solver::resetHeuristic(Solver* s, DecisionHeuristic* h) {
    POTASSCO_ASSERT(heuristic_);
    if (s) {
        heuristic_->detach(*s);
    }
    if (heuristic_ != &g_null_heuristic) {
        delete heuristic_;
    }
    heuristic_ = h ? h : &g_null_heuristic;
}
void Solver::resetConfig() {
    if (strategy_.hasConfig) {
        if (auto* pp = getPost(PostPropagator::priority_reserved_look)) {
            pp->destroy(this, true);
        }
        ccMin_.reset();
    }
    strategy_.hasConfig = 0;
}
void Solver::startInit(uint32_t numConsGuess, const SolverParams& params) {
    assert(not lazyRem_ && decisionLevel() == 0);
    if (watches_.empty()) {
        assign_.trail.reserve(shared_->numVars() + 2);
        watches_.reserve((shared_->numVars() + 2) << 1);
        assign_.reserve(shared_->numVars() + 2);
    }
    updateVars();
    // pre-allocate some memory
    constraints_.reserve(numConsGuess / 2);
    levels_.reserve(25);
    if (undoHead_ == nullptr) {
        for ([[maybe_unused]] auto _ : irange(25u)) { undoFree(new ConstraintDB(10)); }
    }
    if (not popRootLevel(rootLevel())) {
        return;
    }
    if (not strategy_.hasConfig) {
        uint32_t id         = this->id();
        uint32_t hId        = strategy_.heuId; // remember active heuristic
        strategy_           = static_cast<const SolverStrategies&>(params);
        strategy_.id        = id; // keep id
        strategy_.hasConfig = 1;  // strategy is now "up to date"
        if (not params.ccMinRec) {
            ccMin_.reset();
        }
        else if (not ccMin_) {
            ccMin_ = std::make_unique<CCMinRecursive>();
        }
        if (id == params.id || not shared_->seedSolvers()) {
            rng.srand(params.seed);
        }
        else {
            Rng x(14182940);
            for ([[maybe_unused]] auto _ : irange(id)) { x.rand(); }
            rng.srand(x.seed());
        }
        if (hId != params.heuId) { // heuristic has changed
            resetHeuristic(this);
        }
        else if (heuristic_ != &g_null_heuristic) {
            heuristic_->setConfig(params.heuristic);
        }
    }
    if (heuristic_ == &g_null_heuristic) {
        shared_->setHeuristic(*this);
    }
    postHead_ = &g_sent_list; // disable post propagators during setup
    heuristic_->startInit(*this);
}

void Solver::updateVars() {
    if (numVars() > shared_->numVars()) {
        popVars(numVars() - shared_->numVars(), false, nullptr);
    }
    else {
        assign_.resize(shared_->numVars() + 1);
        watches_.resize(assign_.numVars() << 1);
    }
}

bool Solver::cloneDB(const ConstraintDB& db) {
    while (dbIdx_ < size32(db) && not hasConflict()) {
        if (Constraint* c = db[dbIdx_++]->cloneAttach(*this)) {
            constraints_.push_back(c);
        }
    }
    return not hasConflict();
}
bool Solver::preparePost() {
    if (hasConflict()) {
        return false;
    }
    if (initPost_ == 0) {
        initPost_ = 1;
        if (not post_.init(*this)) {
            return false;
        }
    }
    return shared_->addPost(*this);
}

bool Solver::endInit() {
    if (hasConflict()) {
        return false;
    }
    heuristic_->endInit(*this);
    if (strategy_.signFix) {
        for (auto v : vars()) {
            Literal x = DecisionHeuristic::selectLiteral(*this, v, 0);
            setPref(v, ValueSet::user_value, x.sign() ? value_false : value_true);
        }
    }
    postHead_ = post_.head(); // enable all post propagators
    return propagate() && simplify();
}

bool Solver::endStep(uint32_t top, const SolverParams& params) {
    initPost_ = 0; // defer calls to PostPropagator::init()
    if (not popRootLevel(rootLevel())) {
        return false;
    }
    popAuxVar();
    Literal x = shared_->stepLiteral();
    top       = std::min(top, lastSimp_);
    if (PostPropagator* pp = getPost(PostPropagator::priority_reserved_look)) {
        pp->destroy(this, true);
    }
    if ((value(x.var()) != value_free || force(~x)) && simplify() && this != shared_->master() && shared_->ok()) {
        Solver& m = *shared_->master();
        for (auto end = size32(assign_.trail); top < end; ++top) {
            Literal u = assign_.trail[top];
            if (u.var() != x.var() && not m.force(u)) {
                break;
            }
        }
    }
    if (params.forgetLearnts()) {
        reduceLearnts(1.0f);
    }
    if (params.forgetHeuristic()) {
        resetHeuristic(this);
    }
    if (params.forgetSigns()) {
        resetPrefs();
    }
    if (params.forgetActivities()) {
        resetLearntActivities();
    }
    return true;
}

void Solver::add(Constraint* c) { constraints_.push_back(c); }
bool Solver::add(const ClauseRep& c, bool isNew) {
    if (c.prep == 0) {
        return ClauseCreator::create(*this, c, ClauseCreator::clause_force_simplify).ok();
    }
    int added = 0;
    if (c.size > 1) {
        if (allowImplicit(c)) {
            added = shared_->addImp({c.lits, c.size}, c.info.type());
        }
        else {
            return ClauseCreator::create(*this, c, ClauseCreator::clause_explicit).ok();
        }
    }
    else {
        Literal  u  = c.size ? c.lits[0] : lit_false;
        uint32_t ts = numAssignedVars();
        force(u);
        added = static_cast<int>(ts != numAssignedVars());
    }
    if (added > 0 && isNew && c.info.learnt()) {
        stats.addLearnt(c.size, c.info.type());
        distribute(c.literals(), c.info);
    }
    return not hasConflict();
}
bool Solver::addPost(PostPropagator* p, bool init) {
    post_.add(p);
    return not init || p->init(*this);
}
bool     Solver::addPost(PostPropagator* p) { return addPost(p, initPost_ != 0); }
void     Solver::removePost(PostPropagator* p) { post_.remove(p); }
auto     Solver::getPost(uint32_t prio) const -> PostPropagator* { return post_.find(prio); }
uint32_t Solver::receive(SharedLiterals** out, uint32_t maxOut) const {
    if (shared_->distributor.get()) {
        return shared_->distributor->receive(*this, out, maxOut);
    }
    return 0;
}

void Solver::restart() {
    undoUntil(0);
    ++stats.restarts;
    ccInfo_.score().bumpActivity();
}

SharedLiterals* Solver::distribute(LitView lits, const ConstraintInfo& extra) {
    if (not shared_->distributor || extra.aux()) {
        return nullptr;
    }
    if (auto size = size32(lits); shared_->distributor->isCandidate(size, extra)) {
        uint32_t initialRefs =
            shared_->concurrency() - (size <= ClauseHead::max_short_len || not shared_->physicalShare(extra.type()));
        auto* x = SharedLiterals::newShareable(lits, extra.type(), initialRefs);
        shared_->distributor->publish(*this, x);
        stats.addDistributed(extra.lbd(), extra.type());
        return initialRefs == shared_->concurrency() ? x : nullptr;
    }
    return nullptr;
}
void Solver::setEnumerationConstraint(Constraint* c) {
    if (auto prev = std::exchange(enum_, c); prev && prev != c) {
        prev->destroy(this, true);
    }
}

uint32_t Solver::numConstraints() const {
    return size32(constraints_) + (shared_ ? shared_->numBinary() + shared_->numTernary() : 0);
}

Var_t Solver::pushAuxVar() {
    assert(not lazyRem_);
    auto aux = assign_.addVar();
    setPref(aux, ValueSet::def_value, value_false);
    watches_.insert(watches_.end(), 2, WatchList());
    heuristic_->updateVar(*this, aux, 1);
    return aux;
}

void Solver::acquireProblemVar(Var_t var) {
    if (validVar(var) || shared_->frozen() || numProblemVars() <= numVars() || not shared_->ok()) {
        return;
    }
    shared_->startAddConstraints();
}

void Solver::popAuxVar(uint32_t num, ConstraintDB* auxCons) {
    num = numVars() >= shared_->numVars() ? std::min(numVars() - shared_->numVars(), num) : 0;
    if (not num) {
        return;
    }
    shared_->report("removing aux vars", this);
    Dirty dirty;
    lazyRem_ = &dirty;
    popVars(num, true, auxCons);
    lazyRem_ = nullptr;
    shared_->report("removing aux watches", this);
    dirty.cleanup(watches_, levels_);
}
Literal Solver::popVars(uint32_t num, bool popLearnt, ConstraintDB* popAux) {
    Literal  pop = posLit(assign_.numVars() - num);
    uint32_t dl  = decisionLevel() + 1;
    for (const auto& impliedLit : impliedLits_) {
        if (impliedLit.lit >= pop) {
            dl = std::min(dl, impliedLit.level);
        }
    }
    for (auto v = pop.var(), end = pop.var() + num; v != end; ++v) {
        if (value(v) != value_free) {
            dl = std::min(dl, level(v));
        }
    }
    // 1. remove aux vars from assignment and watch lists
    if (dl > rootLevel()) {
        undoUntil(dl - 1, undo_pop_proj_level);
    }
    else {
        popRootLevel((rootLevel() - dl) + 1);
        if (dl == 0) { // top-level has aux vars - cleanup manually
            uint32_t j      = shared_->numUnary();
            uint32_t nUnits = assign_.units(), nFront = assign_.front, nSimps = lastSimp_;
            for (uint32_t i = j, end = size32(assign_.trail), endUnits = nUnits, endFront = nFront,
                          endSimps = lastSimp_;
                 i != end; ++i) {
                if (assign_.trail[i] < pop) {
                    assign_.trail[j++] = assign_.trail[i];
                }
                else {
                    nUnits -= (i < endUnits);
                    nFront -= (i < endFront);
                    nSimps -= (i < endSimps);
                }
            }
            shrinkVecTo(assign_.trail, j);
            assign_.front = nFront;
            assign_.setUnits(nUnits);
            lastSimp_ = nSimps;
        }
    }
    for (uint32_t n = num; n--;) {
        releaseVec(watches_.back());
        watches_.pop_back();
        releaseVec(watches_.back());
        watches_.pop_back();
    }
    // 2. remove learnt constraints over aux
    if (popLearnt) {
        shared_->report("removing aux constraints", this);
        ConstraintDB::size_type os = 0;
        ClauseHead::SmallBuffer buffer;
        for (Constraint* con : learnts_) {
            if (ClauseHead* clause = con->clause(); clause && clause->aux()) {
                auto cc = clause->toLits(buffer);
                if (std::ranges::any_of(cc, [&pop](Literal x) { return x >= pop; })) {
                    con->destroy(this, true);
                    continue;
                }
            }
            learnts_[os++] = con;
        }
        shrinkVecTo(learnts_, os);
    }
    if (popAux) {
        destroyDB(*popAux);
    }
    // 3. remove vars from solver and heuristic
    assign_.resize(assign_.numVars() - num);
    if (not validVar(tag_.var())) {
        tag_ = lit_true;
    }
    heuristic_->updateVar(*this, pop.var(), num);
    return pop;
}

bool Solver::pushRoot(LitView path, bool pushStep) {
    // make sure we are on the current (fully propagated) root level
    if (not popRootLevel(0) || not simplify() || not propagate()) {
        return false;
    }
    // push path
    if (pushStep && not pushRoot(shared_->stepLiteral())) {
        return false;
    }
    stats.addPath(path.size());
    for (auto lit : path) {
        if (not pushRoot(lit)) {
            return false;
        }
    }
    ccInfo_.setActivity(1);
    return true;
}

bool Solver::pushRoot(Literal x) {
    if (hasConflict()) {
        return false;
    }
    if (decisionLevel() != rootLevel()) {
        popRootLevel(0);
    }
    if (queueSize() && not propagate()) {
        return false;
    }
    if (value(x.var()) != value_free) {
        return isTrue(x);
    }
    assume(x);
    --stats.choices;
    pushRootLevel();
    return propagate();
}

bool Solver::popRootLevel(uint32_t n, LitVec* popped, bool aux) {
    clearStopConflict();
    uint32_t newRoot = levels_.root - std::min(n, rootLevel());
    if (popped && newRoot < rootLevel()) {
        for (uint32_t i : irange(newRoot + 1, rootLevel() + 1)) {
            Literal x = decision(i);
            if (aux || not auxVar(x.var())) {
                popped->push_back(x);
            }
        }
    }
    if (n) {
        ccInfo_.setActivity(1);
    }
    levels_.root       = newRoot;
    levels_.flip       = rootLevel();
    levels_.mode       = 0;
    impliedLits_.front = 0;
    bool tagActive     = isTrue(tagLiteral());
    // go back to new root level and re-assert still implied literals
    undoUntil(rootLevel(), undo_pop_proj_level);
    if (tagActive && not isTrue(tagLiteral())) {
        removeConditional();
    }
    return not hasConflict();
}

bool Solver::clearAssumptions() { return popRootLevel(rootLevel()) && simplify(); }

void Solver::clearStopConflict() {
    if (hasStopConflict()) {
        levels_.root  = conflict_[1].rep();
        levels_.flip  = conflict_[2].rep();
        assign_.front = conflict_[3].rep();
        conflict_.clear();
    }
}

void Solver::setStopConflict() {
    if (not hasConflict()) {
        // we use the nogood {FALSE} to represent the unrecoverable conflict -
        // note that {FALSE} can otherwise never be a violated nogood because
        // TRUE is always true in every solver
        conflict_.push_back(lit_false);
        // remember the current root-level
        conflict_.push_back(Literal::fromRep(rootLevel()));
        // remember the current bt-level
        conflict_.push_back(Literal::fromRep(backtrackLevel()));
        // remember the current propagation queue
        conflict_.push_back(Literal::fromRep(assign_.front));
    }
    // artificially increase root level -
    // this way, the solver is prevented from resolving the conflict
    pushRootLevel(decisionLevel());
}

void Solver::copyGuidingPath(LitVec& gpOut) {
    uint32_t aux = rootLevel() + 1;
    gpOut.clear();
    for (uint32_t i : irange(1u, rootLevel() + 1)) {
        Literal x = decision(i);
        if (not auxVar(x.var())) {
            gpOut.push_back(x);
        }
        else if (i < aux) {
            aux = i;
        }
    }
    for (const auto& lit : impliedLits_) {
        if (lit.level <= rootLevel() && (lit.ante.ante().isNull() || lit.level < aux) && not auxVar(lit.lit.var())) {
            gpOut.push_back(lit.lit);
        }
    }
}
bool Solver::splittable() const {
    if (decisionLevel() == rootLevel() || frozenLevel(rootLevel() + 1)) {
        return false;
    }
    if (numAuxVars()) { // check if gp would contain solver local aux var
        uint32_t minAux = rootLevel() + 2;
        for (uint32_t i : irange(1u, minAux)) {
            if (auxVar(decision(i).var()) && decision(i) != tag_) {
                return false;
            }
        }
        for (const auto& lit : impliedLits_) {
            if (lit.ante.ante().isNull() && lit.level < minAux && auxVar(lit.lit.var()) && lit.lit != tag_) {
                return false;
            }
        }
    }
    return true;
}
bool Solver::split(LitVec& out) {
    if (not splittable()) {
        return false;
    }
    copyGuidingPath(out);
    pushRootLevel();
    out.push_back(~decision(rootLevel()));
    splitReq_ = false;
    stats.addSplit();
    return true;
}
bool Solver::requestSplit() {
    splitReq_ = true;
    bool res  = splittable();
    if (not res && decisionLevel() > rootLevel() && not frozenLevel(rootLevel() + 1)) {
        splitReq_ = false; // solver can't split because split would contain aux vars
    }
    return res;
}
bool Solver::clearSplitRequest() { return std::exchange(splitReq_, false); }
/////////////////////////////////////////////////////////////////////////////////////////
// Solver: Watch management
////////////////////////////////////////////////////////////////////////////////////////
uint32_t Solver::numWatches(Literal p) const {
    assert(validVar(p.var()));
    if (not validWatch(p)) {
        return 0;
    }
    auto n = size32(watches_[p.id()]);
    if (not auxVar(p.var())) {
        n += shared_->shortImplications().numEdges(p);
    }
    return n;
}

bool Solver::hasWatch(Literal p, Constraint* c) const { return getWatch(p, c) != nullptr; }

bool Solver::hasWatch(Literal p, ClauseHead* h) const {
    return validWatch(p) && std::ranges::any_of(watches_[p.id()].left_view(), ClauseWatch::EqHead(h));
}

GenericWatch* Solver::getWatch(Literal p, Constraint* c) const {
    if (not validWatch(p)) {
        return nullptr;
    }
    const auto& pList = watches_[p.id()];
    auto        it    = std::find_if(pList.right_begin(), pList.right_end(), GenericWatch::EqConstraint(c));
    return it != pList.right_end() ? &const_cast<GenericWatch&>(*it) : nullptr;
}

void Solver::removeWatch(const Literal& p, Constraint* c) {
    if (not validWatch(p)) {
        return;
    }
    auto& pList = watches_[p.id()];
    if (not lazyRem_ || not lazyRem_->add(p, pList, c)) {
        pList.erase_right(std::find_if(pList.right_begin(), pList.right_end(), GenericWatch::EqConstraint(c)));
    }
}

void Solver::removeWatch(const Literal& p, ClauseHead* h) {
    if (not validWatch(p)) {
        return;
    }
    auto& pList = watches_[p.id()];
    if (not lazyRem_ || not lazyRem_->add(p, pList, h)) {
        pList.erase_left(std::find_if(pList.left_begin(), pList.left_end(), ClauseWatch::EqHead(h)));
    }
}

bool Solver::removeUndoWatch(uint32_t dl, Constraint* c) {
    assert(dl != 0 && dl <= decisionLevel());
    if (levels_[dl - 1].undo) {
        auto& uList = *levels_[dl - 1].undo;
        if (not lazyRem_ || not lazyRem_->add(dl - 1, uList, c)) {
            if (auto it = std::ranges::find(uList, c); it != uList.end()) {
                *it = uList.back();
                uList.pop_back();
                return true;
            }
        }
    }
    return false;
}
void Solver::destroyDB(ConstraintDB& db) {
    if (not db.empty()) {
        Dirty dirty;
        if (not lazyRem_) {
            lazyRem_ = &dirty;
        }
        for (auto* it : db) { it->destroy(this, true); }
        db.clear();
        if (lazyRem_ == &dirty) {
            lazyRem_ = nullptr;
            dirty.cleanup(watches_, levels_);
        }
    }
}
/////////////////////////////////////////////////////////////////////////////////////////
// Solver: Basic DPLL-functions
////////////////////////////////////////////////////////////////////////////////////////

// removes all satisfied binary and ternary clauses as well
// as all constraints for which Constraint::simplify returned true.
bool Solver::simplify() {
    if (decisionLevel() != 0) {
        return true;
    }
    if (hasConflict()) {
        return false;
    }
    if (lastSimp_ != size32(assign_.trail)) {
        uint32_t old = lastSimp_;
        if (not simplifySat()) {
            return false;
        }
        assert(lastSimp_ == size32(assign_.trail) && lastSimp_ >= old);
        heuristic_->simplify(*this, trailView(old));
    }
    if (shufSimp_) {
        simplifySat();
    }
    return true;
}
Var_t Solver::pushTagVar(bool pushToRoot) {
    if (isSentinel(tag_)) {
        tag_ = posLit(pushAuxVar());
    }
    if (pushToRoot) {
        pushRoot(tag_);
    }
    return tag_.var();
}
void Solver::removeConditional() {
    if (Literal p = ~tagLiteral(); isSentinel(p)) {
        return;
    }
    erase_if(learnts_, [&](Constraint* con) {
        if (ClauseHead* clause = con->clause(); clause && clause->tagged()) {
            con->destroy(this, true);
            return true;
        }
        return false;
    });
}

void Solver::strengthenConditional() {
    if (Literal p = ~tagLiteral(); not isSentinel(p)) {
        erase_if(learnts_, [&](Constraint* con) {
            if (ClauseHead* clause = con->clause();
                clause && clause->tagged() && clause->strengthen(*this, p, true).removeClause) {
                assert((decisionLevel() == rootLevel() || not con->locked(*this)) &&
                       "Solver::strengthenConditional(): must not remove locked constraint!");
                con->destroy(this, true);
                return true;
            }
            return false;
        });
    }
}

bool Solver::simplifySat() {
    if (queueSize() > 0 && not propagate()) {
        return false;
    }
    assert(assign_.qEmpty());
    uint32_t start = lastSimp_;
    assign_.front  = start;
    lastSimp_      = size32(assign_.trail);
    for (Literal p; not assign_.qEmpty();) {
        p = assign_.qPop();
        releaseVec(watches_[p.id()]);
        releaseVec(watches_[(~p).id()]);
    }
    bool shuffle = shufSimp_ != 0;
    shufSimp_    = 0;
    if (shuffle) {
        rng.shuffle(constraints_.begin(), constraints_.end());
        rng.shuffle(learnts_.begin(), learnts_.end());
    }
    if (isMaster()) {
        shared_->simplify(trailView(start), shuffle);
    }
    else {
        simplifyDB(*this, constraints_, shuffle);
    }
    simplifyDB(*this, learnts_, shuffle);
    if (postHead_ == post_.head()) {
        post_.simplify(*this, shuffle);
    }
    if (enum_ && enum_->simplify(*this, shuffle)) {
        enum_->destroy(this, false);
        enum_ = nullptr;
    }
    return true;
}

void Solver::setConflict(Literal p, const Antecedent& a, uint32_t data) {
    ++stats.conflicts;
    conflict_.push_back(~p);
    if (searchMode() != SolverStrategies::no_learning && not a.isNull()) {
        if (data == UINT32_MAX) {
            a.reason(*this, p, conflict_);
        }
        else {
            // temporarily replace old data with new data
            uint32_t saved = assign_.data(p.var());
            assign_.setData(p.var(), data);
            // extract conflict using new data
            a.reason(*this, p, conflict_);
            // restore old data
            assign_.setData(p.var(), saved);
        }
    }
}
bool Solver::force(const ImpliedLiteral& p) {
    // Already implied?
    if (isTrue(p.lit)) {
        if (level(p.lit.var()) <= p.level) {
            return true;
        }
        if (auto* x = impliedLits_.find(p.lit); x) {
            if (x->level > p.level) {
                *x = p;
                setReason(p.lit, p.ante.ante(), p.ante.data());
            }
            return true;
        }
    }
    if (undoUntil(p.level) != p.level) {
        // Logically the implication is on level p.level.
        // Store enough information so that p can be re-assigned once we backtrack.
        impliedLits_.add(decisionLevel(), p);
    }
    return (isTrue(p.lit) && setReason(p.lit, p.ante.ante(), p.ante.data())) ||
           force(p.lit, p.ante.ante(), p.ante.data());
}

bool Solver::assume(const Literal& p) {
    if (value(p.var()) == value_free) {
        assert(decisionLevel() != assign_.maxLevel());
        ++stats.choices;
        levels_.push_back(DLevel(numAssignedVars(), nullptr));
        return assign_.assign(p, decisionLevel(), Antecedent());
    }
    return isTrue(p);
}

void Solver::cancelPropagation() {
    assign_.qReset();
    for (auto* r = *postHead_; r; r = r->next) { r->reset(); }
}

bool Solver::propagate() {
    if (unitPropagate() && postPropagate(postHead_, nullptr)) {
        assert(queueSize() == 0);
        return true;
    }
    cancelPropagation();
    return false;
}

bool Solver::propagateFrom(const PostPropagator* p) {
    assert((p && *postHead_) && "OP not allowed during init!");
    assert(queueSize() == 0);
    for (PostPropagator** r = postHead_; *r;) {
        if (*r != p) {
            r = &(*r)->next;
        }
        else if (postPropagate(r, nullptr)) {
            break;
        }
        else {
            cancelPropagation();
            return false;
        }
    }
    assert(queueSize() == 0);
    return true;
}

bool Solver::propagateUntil(PostPropagator* p) {
    assert((not p || *postHead_) && "OP not allowed during init!");
    return unitPropagate() && (p == *postHead_ || postPropagate(postHead_, p));
}

Constraint::PropResult ClauseHead::propagate(Solver& s, Literal p, uint32_t&) {
    Literal* head = head_;
    uint32_t wLit = (head[1] == ~p); // pos of false watched literal
    if (s.isTrue(head[1 - wLit])) {
        return PropResult(true, true);
    }
    if (not s.isFalse(head[2])) {
        assert(not isSentinel(head[2]) && "Invalid ClauseHead!");
        head[wLit] = head[2];
        head[2]    = ~p;
        s.addWatch(~head[wLit], ClauseWatch(this));
        return PropResult(true, false);
    }
    if (updateWatch(s, wLit)) {
        assert(not s.isFalse(head_[wLit]));
        s.addWatch(~head[wLit], ClauseWatch(this));
        return PropResult(true, false);
    }
    return PropResult(s.force(head_[1 ^ wLit], this), true);
}

bool Solver::unitPropagate() {
    assert(not hasConflict());
    uint32_t                      ignore, dl = decisionLevel();
    const ShortImplicationsGraph& btig   = shared_->shortImplications();
    const uint32_t                maxIdx = btig.size();
    while (not assign_.qEmpty()) {
        Literal    p   = assign_.qPop();
        uint32_t   idx = p.id();
        WatchList& wl  = watches_[idx];
        // first: short clause BCP
        if (idx < maxIdx && not btig.propagate(*this, p)) {
            return false;
        }
        // second: clause BCP
        if (wl.left_size() != 0) {
            auto j = wl.left_begin();
            for (auto it = j, end = wl.left_end(); it != end;) {
                ClauseWatch& w   = *it++;
                auto         res = w.head->ClauseHead::propagate(*this, p, ignore);
                if (res.keepWatch) {
                    *j++ = w;
                }
                if (not res.ok) {
                    wl.shrink_left(std::copy(it, end, j));
                    return false;
                }
            }
            wl.shrink_left(j);
        }
        // third: general constraint BCP
        if (wl.right_size() != 0) {
            auto j = wl.right_begin();
            for (auto it = j, end = wl.right_end(); it != end;) {
                GenericWatch& w   = *it++;
                auto          res = w.propagate(*this, p);
                if (res.keepWatch) {
                    *j++ = w;
                }
                if (not res.ok) {
                    wl.shrink_right(std::copy(it, end, j));
                    return false;
                }
            }
            wl.shrink_right(j);
        }
    }
    return dl || assign_.markUnits();
}

bool Solver::postPropagate(PostPropagator** start, PostPropagator* stop) {
    for (PostPropagator **r = start, *t; *r != stop;) {
        t = *r;
        if (not t->propagateFixpoint(*this, stop)) {
            return false;
        }
        assert(queueSize() == 0);
        if (t == *r) {
            r = &t->next;
        }
        // else: t was removed during propagate
    }
    return true;
}

bool Solver::test(Literal p, PostPropagator* c) {
    assert(value(p.var()) == value_free && not hasConflict());
    assume(p);
    --stats.choices;
    uint32_t pLevel = decisionLevel();
    freezeLevel(pLevel); // can't split-off this level
    if (propagateUntil(c)) {
        assert(decisionLevel() == pLevel && "Invalid PostPropagators");
        if (c) {
            c->undoLevel(*this);
        }
        undoUntil(pLevel - 1);
        return true;
    }
    assert(decisionLevel() == pLevel && "Invalid PostPropagators");
    unfreezeLevel(pLevel);
    cancelPropagation();
    return false;
}

bool Solver::resolveConflict() {
    assert(hasConflict());
    if (decisionLevel() > rootLevel()) {
        if (decisionLevel() != backtrackLevel() && searchMode() != SolverStrategies::no_learning) {
            uint32_t uipLevel = analyzeConflict();
            uint32_t dl       = decisionLevel();
            stats.addConflict(dl, uipLevel, backtrackLevel(), ccInfo_.lbd());
            if (dynLimit_) {
                dynLimit_->update(dl, ccInfo_.lbd());
            }
            if (shared_->reportMode()) {
                sharedContext()->report(NewConflictEvent(*this, cc_, ccInfo_));
            }
            undoUntil(uipLevel);
            return ClauseCreator::create(*this, cc_, ClauseCreator::clause_no_prepare, ccInfo_).ok();
        }
        else {
            return backtrack();
        }
    }
    return false;
}

bool Solver::backtrack() {
    Literal lastChoiceInverted;
    do {
        if (decisionLevel() == rootLevel()) {
            setStopConflict();
            return false;
        }
        lastChoiceInverted = ~decision(decisionLevel());
        undoUntil(decisionLevel() - 1, undo_pop_proj_level);
        setBacktrackLevel(decisionLevel(), undo_pop_bt_level);
    } while (hasConflict() || not force(lastChoiceInverted, nullptr));
    // remember flipped literal for copyGuidingPath()
    impliedLits_.add(decisionLevel(), ImpliedLiteral(lastChoiceInverted, decisionLevel(), nullptr));
    return true;
}

bool ImpliedList::assign(Solver& s) {
    assert(front <= size32(lits));
    bool           ok = not s.hasConflict();
    const uint32_t dl = s.decisionLevel();
    auto           j  = lits.begin() + front;
    for (auto x : std::ranges::subrange(j, lits.end())) {
        if (x.level <= dl) {
            ok = ok && s.force(x.lit, x.ante.ante(), x.ante.data());
            if (x.level < dl || x.ante.ante().isNull()) {
                *j++ = x;
            }
        }
    }
    lits.erase(j, lits.end());
    level = dl * static_cast<uint32_t>(not lits.empty());
    front = level > s.rootLevel() ? front : size32(lits);
    return ok;
}
bool     Solver::isUndoLevel() const { return decisionLevel() > backtrackLevel(); }
uint32_t Solver::undoUntilImpl(uint32_t level, bool forceSave) {
    level = std::max(level, backtrackLevel());
    if (level >= decisionLevel()) {
        return decisionLevel();
    }
    uint32_t& n  = (levels_.jump = decisionLevel() - level);
    bool      sp = forceSave || (strategy_.saveProgress > 0 && strategy_.saveProgress <= n);
    bool      ok = conflict_.empty() && levels_.back().freeze == 0;
    conflict_.clear();
    heuristic_->undo(*this, trailView(levels_[level].trailPos));
    undoLevel(sp && ok);
    while (--n) { undoLevel(sp); }
    return level;
}
uint32_t Solver::undoUntil(uint32_t level, uint32_t mode) {
    assert(backtrackLevel() >= rootLevel());
    if (level < backtrackLevel() && mode >= levels_.mode) {
        levels_.flip = std::max(rootLevel(), level);
    }
    level = undoUntilImpl(level, (mode & undo_save_phases) != 0);
    if (impliedLits_.active(level)) {
        impliedLits_.assign(*this);
    }
    return level;
}
uint32_t Solver::estimateBCP(Literal p, int maxRecursionDepth) const {
    if (value(p.var()) != value_free) {
        return 0;
    }
    auto  first = assign_.assigned();
    auto  i     = first;
    auto& self  = const_cast<Solver&>(*this);
    self.assign_.setValue(p.var(), trueValue(p));
    self.assign_.trail.push_back(p);
    const auto&    btig   = shared_->shortImplications();
    const uint32_t maxIdx = btig.size();
    do {
        Literal x = assign_.trail[i++];
        if (x.id() < maxIdx && not btig.propagateBin(self.assign_, x, 0)) {
            break;
        }
    } while (i < assign_.assigned() && maxRecursionDepth-- != 0);
    i = assign_.assigned() - first;
    while (self.assign_.assigned() != first) { self.assign_.undoLast(); }
    return i;
}

uint32_t Solver::inDegree(WeightLitVec& out) {
    if (decisionLevel() == 0) {
        return 1;
    }
    assert(not hasConflict());
    out.reserve((numAssignedVars() - levelStart(1)) / 10);
    uint32_t maxIn = 1;
    uint32_t i = size32(assign_.trail), stop = levelStart(1);
    for (LitVec temp; i-- != stop;) {
        Literal  x    = assign_.trail[i];
        uint32_t xLev = assign_.level(x.var());
        if (auto xAnte = assign_.reason(x.var()); not xAnte.isNull() && xAnte.type() != Antecedent::binary) {
            uint32_t xIn = 0;
            xAnte.reason(*this, x, temp);
            for (auto lit : temp) { xIn += level(lit.var()) != xLev; }
            if (xIn) {
                out.push_back(WeightLiteral{x, static_cast<Weight_t>(std::min<uint32_t>(xIn, weight_max))});
                maxIn = std::max(xIn, maxIn);
            }
            temp.clear();
        }
    }
    return maxIn;
}
void Solver::counterBumpVars(uint32_t bump) {
    bumpAct_.clear();
    auto maxIn = inDegree(bumpAct_);
    heuristic_->bump(*this, bumpAct_, bump / static_cast<double>(maxIn));
    bumpAct_.clear();
}
/////////////////////////////////////////////////////////////////////////////////////////
// Solver: Private helper functions
////////////////////////////////////////////////////////////////////////////////////////
Solver::ConstraintDB* Solver::allocUndo(Constraint* c) {
    if (undoHead_ == nullptr) {
        return new ConstraintDB(1, c);
    }
    assert(undoHead_->size() == 1);
    ConstraintDB* r = undoHead_;
    undoHead_       = reinterpret_cast<ConstraintDB*>(undoHead_->front());
    r->clear();
    r->push_back(c);
    return r;
}
void Solver::undoFree(ConstraintDB* x) {
    // maintain a single-linked list of undo lists
    x->clear();
    x->push_back(reinterpret_cast<Constraint*>(undoHead_));
    undoHead_ = x;
}
// removes the current decision level
void Solver::undoLevel(bool sp) {
    assert(decisionLevel() != 0 && levels_.back().trailPos != size32(assign_.trail) &&
           "Decision Level must not be empty");
    assign_.undoTrail(levels_.back().trailPos, sp);
    if (levels_.back().undo) {
        for (auto* c : *levels_.back().undo) { c->undoLevel(*this); }
        undoFree(levels_.back().undo);
    }
    levels_.pop_back();
}

inline ClauseHead* clause(const Antecedent& ante) {
    return ante.isNull() || ante.type() != Antecedent::generic ? nullptr : ante.constraint()->clause();
}

bool Solver::resolveToFlagged(LitView in, uint8_t vf, LitVec& out, uint32_t& outLbd) const {
    return const_cast<Solver&>(*this).resolveToFlagged(in, vf, out, outLbd);
}
bool Solver::resolveToFlagged(LitView in, const uint8_t vf, LitVec& out, uint32_t& outLbd) {
    const LitVec& trail = assign_.trail;
    LitView       rhs   = in;
    LitVec        temp;
    out.clear();
    bool ok = true, first = true;
    for (uint32_t tp = size32(trail), resolve = 0u;; first = false) {
        Literal p;
        for (auto lit : rhs) {
            p = lit ^ first;
            if (auto v = p.var(); not seen(v)) {
                markSeen(v);
                if (varInfo(v).hasAll(vf)) {
                    markLevel(level(v));
                    out.push_back(~p);
                }
                else if (not reason(p).isNull()) {
                    ++resolve;
                }
                else {
                    clearSeen(v);
                    ok = false;
                    break;
                }
            }
        }
        if (resolve-- == 0) {
            break;
        }
        // find next literal to resolve
        while (not seen(trail[--tp]) || varInfo(trail[tp].var()).hasAll(vf)) { ; }
        clearSeen((p = trail[tp]).var());
        reason(p, temp);
        rhs = temp;
    }
    auto outSize = size32(out);
    if (ok && not first) {
        const uint32_t     ccAct = strategy_.ccMinKeepAct;
        constexpr uint32_t antes = SolverStrategies::all_antes;
        strategy_.ccMinKeepAct   = 1;
        if (ccMin_) {
            ccMinRecurseInit(*ccMin_);
        }
        for (decltype(outSize) i = 0; i != outSize;) {
            if (not ccRemovable(~out[i], antes, ccMin_.get())) {
                ++i;
            }
            else {
                std::swap(out[i], out[--outSize]);
            }
        }
        strategy_.ccMinKeepAct = ccAct;
    }
    POTASSCO_ASSERT(not ok || outSize != 0, "Invalid empty clause - was %u!\n", size32(out));
    outLbd = 0;
    for (uint32_t i = 0, onRoot = 0, rootLev = rootLevel(); auto lit : out) {
        auto v  = lit.var();
        auto dl = level(v);
        clearSeen(v);
        if (dl && hasLevel(dl)) {
            unmarkLevel(dl);
            outLbd += i < outSize && (dl > rootLev || ++onRoot == 1);
        }
        ++i;
    }
    shrinkVecTo(out, outSize);
    return ok;
}
void Solver::resolveToCore(LitVec& out) {
    POTASSCO_CHECK_PRE(hasConflict() && not hasStopConflict(), "Function requires valid conflict");
    // move conflict to cc_
    cc_.clear();
    cc_.swap(conflict_);
    if (searchMode() == SolverStrategies::no_learning) {
        for (uint32_t i : irange(decisionLevel())) { cc_.push_back(decision(i + 1)); }
    }
    const LitVec& trail = assign_.trail;
    const LitVec* r     = &cc_;
    // resolve all-last uip
    for (uint32_t marked = 0, tPos = size32(trail);; r = &conflict_) {
        for (auto p : *r) {
            if (not seen(p.var())) {
                assert(level(p.var()) <= decisionLevel());
                markSeen(p.var());
                ++marked;
            }
        }
        if (marked-- == 0) {
            break;
        }
        // search for the last marked literal
        while (not seen(trail[--tPos].var())) { ; }
        Literal  p  = trail[tPos];
        uint32_t dl = level(p.var());
        assert(dl);
        clearSeen(p.var());
        conflict_.clear();
        if (not reason(p).isNull()) {
            reason(p).reason(*this, p, conflict_);
        }
        else if (p == decision(dl)) {
            out.push_back(p);
        }
    }
    // restore original conflict
    cc_.swap(conflict_);
}

// computes the First-UIP clause and stores it in cc_, where cc_[0] is the asserting literal (inverted UIP)
// and cc_[1] is a literal from the asserting level (if > 0)
// RETURN: asserting level of the derived conflict clause
uint32_t Solver::analyzeConflict() {
    // must be called here, because we unassign vars during analyzeConflict
    heuristic_->undo(*this, trailView(levels_.back().trailPos));
    uint32_t onLevel = 0;      // number of literals from the current DL in resolvent
    uint32_t resSize = 0;      // size of current resolvent
    Literal  p;                // literal to be resolved out next
    cc_.assign(1, p);          // will later be replaced with asserting literal
    Antecedent lhs, rhs, last; // resolve operands
    const bool doOtfs = strategy_.otfs > 0;
    for (bumpAct_.clear();;) {
        uint32_t lhsSize = resSize;
        uint32_t rhsSize = 0;
        heuristic_->updateReason(*this, conflict_, p);
        for (auto q : conflict_) {
            uint32_t cl  = level(q.var());
            rhsSize     += (cl != 0);
            if (not seen(q.var())) {
                ++resSize;
                assert(isTrue(q) && "Invalid literal in reason set!");
                assert(cl > 0 && "Top-Level implication not marked!");
                markSeen(q.var());
                if (cl == decisionLevel()) {
                    ++onLevel;
                }
                else {
                    cc_.push_back(~q);
                    markLevel(cl);
                }
            }
        }
        if (resSize != lhsSize) {
            lhs = nullptr;
        }
        if (rhsSize != resSize) {
            rhs = nullptr;
        }
        if (doOtfs && (not rhs.isNull() || not lhs.isNull())) {
            // resolvent subsumes rhs and possibly also lhs
            otfs(lhs, rhs, p, onLevel == 1);
        }
        assert(onLevel > 0 && "CONFLICT MUST BE ANALYZED ON CONFLICT LEVEL!");
        // search for the last assigned literal that needs to be analyzed...
        while (not seen(assign_.last().var())) { assign_.undoLast(); }
        p   = assign_.last();
        rhs = reason(p);
        clearSeen(p.var());
        if (--onLevel == 0) {
            break;
        }
        --resSize; // p will be resolved out next
        last = rhs;
        reason(p, conflict_);
    }
    cc_[0] = ~p; // store the 1-UIP
    assert(decisionLevel() == level(cc_[0].var()));
    ClauseHead* lastRes = nullptr;
    if (strategy_.otfs > 1 || not lhs.isNull()) {
        if (not lhs.isNull()) {
            lastRes = clause(lhs);
        }
        else if (cc_.size() <= (conflict_.size() + 1)) {
            lastRes = clause(last);
        }
    }
    if (strategy_.bumpVarAct && reason(p).learnt()) {
        bumpAct_.push_back(WeightLiteral{p, static_cast<Weight_t>(reason(p).constraint()->activity().lbd())});
    }
    return simplifyConflictClause(cc_, ccInfo_, lastRes);
}

void Solver::otfs(Antecedent& lhs, const Antecedent& rhs, Literal p, bool final) {
    ClauseHead *cLhs = clause(lhs), *cRhs = clause(rhs);
    if (cLhs) {
        auto x = cLhs->strengthen(*this, ~p, not final);
        if (not x.litRemoved || x.removeClause) {
            cLhs = not x.litRemoved ? nullptr : otfsRemove(cLhs, nullptr);
        }
    }
    lhs = cLhs;
    if (cRhs) {
        auto x = cRhs->strengthen(*this, p, not final);
        if (not x.litRemoved || (x.removeClause && otfsRemove(cRhs, nullptr) == nullptr)) {
            if (x.litRemoved && reason(p) == cRhs) {
                setReason(p, nullptr);
            }
            cRhs = nullptr;
        }
        if (cLhs && cRhs) {
            // lhs and rhs are now equal - only one of them is needed
            if (not cLhs->learnt()) {
                std::swap(cLhs, cRhs);
            }
            otfsRemove(cLhs, nullptr);
        }
        lhs = cRhs;
    }
}

ClauseHead* Solver::otfsRemove(ClauseHead* c, const LitVec* newC) {
    bool remStatic = not newC || (newC->size() <= 3 && shared_->allowImplicit(ConstraintType::conflict));
    if (c->learnt() || remStatic) {
        ConstraintDB& db = (c->learnt() ? learnts_ : constraints_);
        if (auto it = std::ranges::find(db, c); it != db.end()) {
            if (isMaster() && &db == &constraints_) {
                shared_->removeConstraint(static_cast<uint32_t>(it - db.begin()), true);
            }
            else {
                db.erase(it);
                c->destroy(this, true);
            }
            c = nullptr;
        }
    }
    return c;
}

// minimizes the conflict clause in cc w.r.t selected strategies.
// PRE:
//  - cc is a valid conflict clause and cc[0] is the UIP-literal
//  - all literals in cc except cc[0] are marked
//  - all decision levels of literals in cc are marked
//  - rhs is 0 or a clause that might be subsumed by cc
// RETURN: finalizeConflictClause(cc, info)
uint32_t Solver::simplifyConflictClause(LitVec& cc, ConstraintInfo& info, ClauseHead* rhs) {
    // 1. remove redundant literals from conflict clause
    temp_.clear();
    uint32_t onAssert = ccMinimize(cc, temp_, strategy_.ccMinAntes, ccMin_.get());
    uint32_t jl       = cc.size() > 1 ? level(cc[1].var()) : 0;
    // clear seen flags of removed literals - keep levels marked
    for (auto x : temp_) { clearSeen(x.var()); }
    // 2. check for inverse arcs
    if (onAssert == 1 && strategy_.reverseArcs > 0) {
        auto maxN = strategy_.reverseArcs;
        if (maxN > 2) {
            maxN = UINT32_MAX;
        }
        else if (maxN > 1) {
            maxN = size32(cc) >> 1;
        }
        markSeen(cc[0].var());
        if (Antecedent ante = ccHasReverseArc(cc[1], jl, maxN); not ante.isNull()) {
            // resolve with inverse arc
            conflict_.clear();
            ante.reason(*this, ~cc[1], conflict_);
            ccResolve(cc, 1, conflict_);
        }
        clearSeen(cc[0].var());
    }
    // 3. check if final clause subsumes rhs
    if (rhs) {
        ClauseHead::SmallBuffer buffer;
        conflict_.clear();
        markSeen(cc[0].var());
        auto rhsLits = rhs->toLits(buffer);
        auto marked  = std::ssize(cc);
        for (auto maxMissing = std::ssize(rhsLits) - marked; auto lit : rhsLits) {
            // NOTE: at this point the DB might not be fully simplified,
            //       e.g. because of mt or lookahead, hence we must explicitly
            //       check for literals assigned on DL 0
            if (not seen(lit.var()) || level(lit.var()) == 0) {
                if (--maxMissing < 0) {
                    break;
                }
                conflict_.push_back(lit); // potentially redundant literal
            }
            else if (--marked == 0 && otfsRemove(rhs, &cc) == nullptr) {
                rhs = nullptr; // rhs is subsumed by cc and was removed
                break;
            }
        }
        if (rhs && marked <= 0) { // rhs is subsumed by cc but could not be removed.
            // TODO: we could reuse rhs instead of learning cc
            //       but this would complicate the calling code.
            //       For now, we only try to strengthen rhs.
            for (auto lit : conflict_) {
                if (not rhs->strengthen(*this, lit, false).litRemoved) {
                    break;
                }
            }
        }
        clearSeen(cc[0].var());
    }
    // 4. finalize
    uint32_t repMode = cc.size() < std::max(strategy_.compress, decisionLevel() + 1) ? 0 : strategy_.ccRepMode;
    jl               = finalizeConflictClause(cc, info, repMode);
    // 5. bump vars implied by learnt constraints with small lbd
    if (not bumpAct_.empty()) {
        auto j      = bumpAct_.begin();
        auto newLbd = info.lbd();
        for (auto& wl : bumpAct_) {
            if (std::cmp_less(wl.weight, newLbd)) {
                wl.weight = 1 + (wl.weight <= 2);
                *j++      = wl;
            }
        }
        bumpAct_.erase(j, bumpAct_.end());
        heuristic_->bump(*this, bumpAct_, 1.0);
    }
    bumpAct_.clear();
    // 6. clear level flags of redundant literals
    for (auto x : temp_) { unmarkLevel(level(x.var())); }
    temp_.clear();
    return jl;
}

// conflict clause minimization
// PRE:
//  - cc is an asserting clause and cc[0] is the asserting literal
//  - all literals in cc are marked as seen
//  -  if ccMin != 0, all decision levels of literals in cc are marked
// POST:
//  - redundant literals were added to removed
//  - if (cc.size() > 1): cc[1] is a literal from the asserting level
// RETURN
//  - the number of literals from the asserting level
uint32_t Solver::ccMinimize(LitVec& cc, LitVec& removed, uint32_t antes, CCMinRecursive* ccMin) {
    if (ccMin) {
        ccMinRecurseInit(*ccMin);
    }
    // skip the asserting literal
    auto assertLevel = 0u;
    auto assertPos   = 1u;
    auto onAssert    = 0u;
    auto j           = 1u;
    for (auto lit : std::ranges::subrange(cc.begin() + 1, cc.end())) {
        if (antes == SolverStrategies::no_antes || not ccRemovable(~lit, antes, ccMin)) {
            auto varLevel = level(lit.var());
            if (varLevel > assertLevel) {
                assertLevel = varLevel;
                assertPos   = j;
                onAssert    = 0;
            }
            onAssert += (varLevel == assertLevel);
            cc[j++]   = lit;
        }
        else {
            removed.push_back(lit);
        }
    }
    shrinkVecTo(cc, j);
    if (assertPos != 1) {
        std::swap(cc[1], cc[assertPos]);
    }
    return onAssert;
}
void Solver::ccMinRecurseInit(CCMinRecursive& ccMin) { ccMin.open = incEpoch(numVars() + 1, 2) - 2; }
bool Solver::ccMinRecurse(CCMinRecursive& ccMin, Literal p) const {
    switch (ccMin.decodeState(epoch_[p.var()])) {
        case CCMinRecursive::state_poison: return false;
        case CCMinRecursive::state_open  : ccMin.push(p.unflag()); break;
        default                          : break;
    }
    return true;
}

// returns true if p is redundant in current conflict clause
bool Solver::ccRemovable(Literal p, uint32_t antes, CCMinRecursive* ccMin) {
    const Antecedent& ante = reason(p);
    if (ante.isNull() || antes > static_cast<uint32_t>(ante.type())) {
        return false;
    }
    if (not ccMin) {
        return ante.minimize(*this, p, nullptr);
    }
    // recursive minimization
    assert(ccMin->todo.empty());
    CCMinRecursive::State dfsState = CCMinRecursive::state_removable;
    ccMin->push(p.unflag());
    for (Literal x;;) {
        x = ccMin->pop();
        assert(not seen(x.var()) || x == p);
        if (x.flagged()) {
            if (x == p) {
                return dfsState == CCMinRecursive::state_removable;
            }
            epoch_[x.var()] = ccMin->encodeState(dfsState);
        }
        else if (dfsState != CCMinRecursive::state_poison) {
            CCMinRecursive::State temp = ccMin->decodeState(epoch_[x.var()]);
            if (temp == CCMinRecursive::state_open) {
                assert(value(x.var()) != value_free && hasLevel(level(x.var())));
                ccMin->push(x.flag());
                const Antecedent& next = reason(x);
                if (next.isNull() || antes > static_cast<uint32_t>(next.type()) || not next.minimize(*this, x, ccMin)) {
                    dfsState = CCMinRecursive::state_poison;
                }
            }
            else if (temp == CCMinRecursive::state_poison) {
                dfsState = temp;
            }
        }
    }
}

// checks whether there is a valid "inverse arc" for the given literal p that can be used
// to resolve p out of the current conflict clause
// PRE:
//  - all literals in the current conflict clause are marked
//  - p is a literal of the current conflict clause and level(p) == maxLevel
// RETURN
//  - An antecedent that is an "inverse arc" for p or null if no such antecedent exists.
Antecedent Solver::ccHasReverseArc(Literal p, uint32_t maxLevel, uint32_t maxNew) {
    assert(seen(p.var()) && isFalse(p) && level(p.var()) == maxLevel);
    const auto& btig = shared_->shortImplications();
    Antecedent  ante;
    if (p.id() < btig.size() && btig.reverseArc(*this, p, maxLevel, ante)) {
        return ante;
    }
    for (const auto& w : watches_[p.id()].left_view()) {
        if (w.head->isReverseReason(*this, ~p, maxLevel, maxNew)) {
            return w.head;
        }
    }
    return ante;
}

// removes cc[pos] by resolving cc with reason
void Solver::ccResolve(LitVec& cc, uint32_t pos, const LitVec& reason) {
    heuristic_->updateReason(*this, reason, cc[pos]);
    for (auto x : reason) {
        assert(isTrue(x));
        if (not seen(x.var())) {
            markLevel(level(x.var()));
            cc.push_back(~x);
        }
    }
    clearSeen(cc[pos].var());
    unmarkLevel(level(cc[pos].var()));
    cc[pos] = cc.back();
    cc.pop_back();
}

// computes asserting level and lbd of cc and clears flags.
// POST:
//  - literals and decision levels in cc are no longer marked
//  - if cc.size() > 1: cc[1] is a literal from the asserting level
// RETURN: asserting level of conflict clause.
uint32_t Solver::finalizeConflictClause(LitVec& cc, ConstraintInfo& info, uint32_t ccRepMode) {
    // 2. clear flags and compute lbd
    uint32_t lbd         = 1;
    uint32_t onRoot      = 0;
    uint32_t varLevel    = 0;
    uint32_t assertLevel = 0;
    uint32_t assertPos   = 1;
    uint32_t maxVar      = cc[0].var();
    Literal  tagLit      = ~tagLiteral();
    bool     tagged      = false;
    for (uint32_t i : irange(1u, size32(cc))) {
        auto v = cc[i].var();
        clearSeen(v);
        if (cc[i] == tagLit) {
            tagged = true;
        }
        if (v > maxVar) {
            maxVar = v;
        }
        varLevel = level(v);
        if (varLevel > assertLevel) {
            assertLevel = varLevel;
            assertPos   = i;
        }
        if (hasLevel(varLevel)) {
            unmarkLevel(varLevel);
            lbd += (varLevel > rootLevel()) || (++onRoot == 1);
        }
    }
    if (assertPos != 1) {
        std::swap(cc[1], cc[assertPos]);
    }
    if (ccRepMode == SolverStrategies::cc_rep_dynamic) {
        ccRepMode =
            ratio(lbd, decisionLevel()) > .66 ? SolverStrategies::cc_rep_decision : SolverStrategies::cc_rep_uip;
    }
    if (ccRepMode) {
        maxVar = cc[0].var(), tagged = false, lbd = 1;
        if (ccRepMode == SolverStrategies::cc_rep_decision) {
            // replace cc with decision sequence
            cc.resize(assertLevel + 1);
            for (uint32_t i = assertLevel; i;) {
                Literal x = ~decision(i--);
                cc[lbd++] = x;
                if (x == tagLit) {
                    tagged = true;
                }
                if (x.var() > maxVar) {
                    maxVar = x.var();
                }
            }
        }
        else {
            // replace cc with all uip clause
            uint32_t marked = size32(cc) - 1;
            while (cc.size() > 1) {
                markSeen(~cc.back());
                cc.pop_back();
            }
            for (auto tr = assign_.trail.end(); marked;) {
                while (not seen(*--tr)) {}
                bool n = --marked != 0 && not reason(*tr).isNull();
                clearSeen(tr->var());
                auto next = tr;
                if (n) {
                    for (auto stop = assign_.trail.begin() + levelStart(level(tr->var()));
                         next-- != stop && not seen(*next);) {}
                }
                if (not n || level(next->var()) != level(tr->var())) {
                    cc.push_back(~*tr);
                    if (tr->var() == tagLit.var()) {
                        tagged = true;
                    }
                    if (tr->var() > maxVar) {
                        maxVar = tr->var();
                    }
                }
                else {
                    for (reason(*tr, conflict_); not conflict_.empty(); conflict_.pop_back()) {
                        if (not seen(conflict_.back())) {
                            ++marked;
                            markSeen(conflict_.back());
                        }
                    }
                }
            }
            lbd = size32(cc);
        }
    }
    info.setScore(ConstraintScore(ccInfo_.activity(), lbd));
    info.setTagged(tagged);
    info.setAux(auxVar(maxVar));
    return assertLevel;
}

// (inefficient) default implementation
bool Constraint::minimize(Solver& s, Literal p, CCMinRecursive* rec) {
    LitVec temp;
    reason(s, p, temp);
    return std::ranges::all_of(temp, [&](Literal x) { return s.ccMinimize(x, rec); });
}

// Selects next branching literal
bool Solver::decideNextBranch(double f) {
    if (f <= 0.0 || rng.drand() >= f || numFreeVars() == 0) {
        return heuristic_->select(*this);
    }
    // select randomly
    Literal  choice;
    uint32_t maxVar = numVars() + 1;
    for (uint32_t v = rng.irand(maxVar);;) {
        if (value(v) == value_free) {
            choice = DecisionHeuristic::selectLiteral(*this, v, 0);
            break;
        }
        if (++v == maxVar) {
            v = 1;
        }
    }
    return assume(choice);
}
void Solver::resetLearntActivities() {
    for (auto* learnt : learnts_) { learnt->resetActivity(); }
}
// Removes up to remFrac% of the learnt nogoods but
// keeps those that are locked or are highly active.
Solver::DBInfo Solver::reduceLearnts(double remFrac, const ReduceStrategy& rs) {
    auto     oldS = numLearntConstraints();
    auto     remM = static_cast<uint32_t>(oldS * std::clamp(remFrac, 0.0, 1.0));
    DBInfo   r{};
    CmpScore cmp(learnts_, static_cast<ReduceStrategy::Score>(rs.score), rs.glue, rs.protect);
    if (remM >= oldS || not remM || rs.algo == ReduceStrategy::reduce_sort) {
        r = reduceSortInPlace(remM, cmp, false);
    }
    else if (rs.algo == ReduceStrategy::reduce_stable) {
        r = reduceSort(remM, cmp);
    }
    else if (rs.algo == ReduceStrategy::reduce_heap) {
        r = reduceSortInPlace(remM, cmp, true);
    }
    else {
        r = reduceLinear(remM, cmp);
    }
    stats.addDeleted(oldS - r.size);
    shrinkVecTo(learnts_, r.size);
    return r;
}
// Removes up to maxR of the learnt nogoods.
// Keeps those that are locked or have a high activity and
// does not reorder learnts_.
Solver::DBInfo Solver::reduceLinear(uint32_t maxR, const CmpScore& sc) {
    // compute average activity
    uint64_t scoreSum = 0;
    for (const auto* learnt : learnts_) { scoreSum += sc.score(learnt->activity()); }
    double avgAct = ratio(scoreSum, numLearntConstraints());
    // constraints with score > 1.5 times the average are "active"
    double scoreThresh = avgAct * 1.5;
    double scoreMax    = sc.score(ConstraintScore(Clasp::act_max, 1));
    if (scoreThresh > scoreMax) {
        scoreThresh = (scoreMax + ratio(scoreSum, numLearntConstraints())) / 2.0;
    }
    // remove up to maxR constraints but keep "active" and locked once
    DBInfo res{};
    for (Constraint* c : learnts_) {
        bool isLocked = c->locked(*this);
        auto a        = c->activity();
        bool isGlue   = sc.score(a) > scoreThresh || sc.isGlue(a);
        if (maxR == 0 || isLocked || isGlue || sc.isFrozen(a)) {
            res.pinned           += isGlue;
            res.locked           += isLocked;
            learnts_[res.size++]  = c;
            c->decreaseActivity();
        }
        else {
            --maxR;
            c->destroy(this, true);
        }
    }
    return res;
}

// Sorts learnt constraints by score and removes the
// maxR constraints with the lowest score without
// reordering learnts_.
Solver::DBInfo Solver::reduceSort(uint32_t maxR, const CmpScore& sc) {
    using HeapType = PodVector_t<CmpScore::ViewPair>;
    DBInfo   res{};
    HeapType heap;
    heap.reserve(maxR = std::min(maxR, size32(learnts_)));
    bool isGlue, isLocked;
    auto cmp = std::cref(sc);
    for (auto idx = 0u; Constraint * c : learnts_) {
        CmpScore::ViewPair vp(idx++, c->activity());
        res.pinned += (isGlue = sc.isGlue(vp.second));
        res.locked += (isLocked = c->locked(*this));
        if (not isLocked && not isGlue && not sc.isFrozen(vp.second)) {
            if (maxR) { // populate heap with first maxR constraints
                heap.push_back(vp);
                if (--maxR == 0) {
                    std::ranges::make_heap(heap, cmp);
                }
            }
            else if (cmp(vp, heap[0])) { // replace max element in heap
                std::ranges::pop_heap(heap, cmp);
                heap.back() = vp;
                std::ranges::push_heap(heap, cmp);
            }
        }
    }
    // Remove all constraints in heap - those are "inactive".
    for (const auto& [idx, _] : heap) {
        learnts_[idx]->destroy(this, true);
        learnts_[idx] = nullptr;
    }
    // Cleanup db and decrease activity of remaining constraints.
    uint32_t j = 0;
    for (Constraint* c : learnts_) {
        if (c) {
            c->decreaseActivity();
            learnts_[j++] = c;
        }
    }
    res.size = j;
    return res;
}

// Sorts the learnt db by score and removes the first
// maxR constraints (those with the lowest score).
Solver::DBInfo Solver::reduceSortInPlace(uint32_t maxR, const CmpScore& sc, bool partial) {
    DBInfo res{};
    auto   nEnd = learnts_.begin();
    maxR        = std::min(maxR, size32(learnts_));
    bool isGlue, isLocked;
    if (not partial) {
        // sort whole db and remove first maxR constraints
        if (maxR && maxR != learnts_.size()) {
            std::ranges::stable_sort(learnts_, sc);
        }
        for (Constraint* c : learnts_) {
            auto a      = c->activity();
            res.pinned += (isGlue = sc.isGlue(a));
            res.locked += (isLocked = c->locked(*this));
            if (not maxR || isLocked || isGlue || sc.isFrozen(a)) {
                c->decreaseActivity();
                *nEnd++ = c;
            }
            else {
                c->destroy(this, true);
                --maxR;
            }
        }
    }
    else {
        auto hBeg = learnts_.begin();
        auto hEnd = learnts_.begin();
        auto cmp  = std::cref(sc);
        for (auto& learnt : learnts_) {
            Constraint* c  = learnt;
            auto        a  = c->activity();
            res.pinned    += (isGlue = sc.isGlue(a));
            res.locked    += (isLocked = c->locked(*this));
            if (isLocked || isGlue || sc.isFrozen(a)) {
                continue;
            }
            if (maxR) {
                learnt  = *hEnd;
                *hEnd++ = c;
                if (--maxR == 0) {
                    std::make_heap(hBeg, hEnd, cmp);
                }
            }
            else if (cmp(c, learnts_[0])) {
                std::pop_heap(hBeg, hEnd, cmp);
                learnt      = *(hEnd - 1);
                *(hEnd - 1) = c;
                std::push_heap(hBeg, hEnd, cmp);
            }
        }
        // remove all constraints in heap
        for (auto* c : std::ranges::subrange(hBeg, hEnd)) { c->destroy(this, true); }
        // copy remaining constraints down
        for (auto* c : std::ranges::subrange(hEnd, learnts_.end())) {
            c->decreaseActivity();
            *nEnd++ = c;
        }
    }
    res.size = static_cast<uint32_t>(std::distance(learnts_.begin(), nEnd));
    return res;
}
uint32_t Solver::incEpoch(uint32_t size, uint32_t n) {
    if (size > size32(epoch_)) {
        epoch_.resize(size, 0u);
    }
    if ((UINT32_MAX - epoch_[0]) < n) {
        epoch_.assign(epoch_.size(), 0u);
    }
    return epoch_[0] += n;
}
uint32_t Solver::countLevels(LitView lits, uint32_t maxLevel) {
    if (maxLevel < 2) {
        return static_cast<uint32_t>(maxLevel && not lits.empty());
    }
    POTASSCO_ASSERT(not ccMin_ || ccMin_->todo.empty(), "Must not be called during minimization!");
    uint32_t n     = 0;
    uint32_t epoch = incEpoch(size32(levels_) + 1);
    for (auto lit : lits) {
        assert(value(lit.var()) != value_free);
        if (uint32_t& levEpoch = epoch_[level(lit.var())]; levEpoch != epoch) {
            levEpoch = epoch;
            if (++n == maxLevel) {
                break;
            }
        }
    }
    return n;
}

void Solver::updateBranch(uint32_t n) {
    int32_t dl = static_cast<int32_t>(decisionLevel()), xl = static_cast<int32_t>(size32(cflStamp_)) - 1;
    if (xl > dl) {
        do {
            n += cflStamp_.back();
            cflStamp_.pop_back();
        } while (--xl != dl);
    }
    else if (dl > xl) {
        cflStamp_.insert(cflStamp_.end(), static_cast<uint32_t>(dl - xl), 0);
    }
    cflStamp_.back() += n;
}
bool Solver::reduceReached(const SearchLimits& limits) const {
    return numLearntConstraints() > limits.learnts || memUse_ > limits.memory;
}
bool Solver::restartReached(const SearchLimits& limits) const {
    uint64_t n = not limits.restart.local || cflStamp_.empty() ? limits.used : cflStamp_.back();
    return n >= limits.restart.conflicts || (limits.restart.dynamic && limits.restart.dynamic->reached());
}
/////////////////////////////////////////////////////////////////////////////////////////
// The basic DPLL-like search-function
/////////////////////////////////////////////////////////////////////////////////////////
Val_t Solver::search(SearchLimits& limit, double rf) {
    assert(not isFalse(tagLiteral()));
    auto* block = limit.restart.block;
    rf          = std::max(0.0, std::min(1.0, rf));
    if (limit.restart.local && decisionLevel() == rootLevel()) {
        cflStamp_.assign(decisionLevel() + 1, 0);
    }
    dynLimit_ = limit.restart.dynamic;
    POTASSCO_SCOPE_EXIT({ dynLimit_ = nullptr; });
    do {
        for (bool conflict = hasConflict() || not propagate() || not simplify(), local = limit.restart.local;;) {
            if (conflict) {
                uint32_t n = 1, ts;
                do {
                    if (block && block->push(ts = numAssignedVars()) && ts > block->scaled()) {
                        if (limit.restart.dynamic) {
                            limit.restart.dynamic->block();
                        }
                        else {
                            limit.restart.conflicts += block->inc;
                        }
                        block->next = block->n + block->inc;
                        ++stats.blRestarts;
                    }
                } while (resolveConflict() && not propagate() && (++n, true));
                limit.used += n;
                if (local) {
                    updateBranch(n);
                }
                if (hasConflict() || (decisionLevel() == 0 && not simplify())) {
                    return value_false;
                }
                if (numFreeVars()) {
                    if (limit.used >= limit.conflicts) {
                        return value_free;
                    }
                    if (restartReached(limit)) {
                        return value_free;
                    }
                    if (reduceReached(limit)) {
                        return value_free;
                    }
                }
            }
            if (decideNextBranch(rf)) {
                conflict = not propagate();
            }
            else {
                break;
            }
        }
    } while (not isModel());
    return value_true;
}
Val_t Solver::search(uint64_t maxC, uint32_t maxL, bool local, double rp) {
    SearchLimits limit;
    limit.restart.conflicts = maxC;
    limit.restart.local     = local;
    limit.learnts           = maxL;
    return search(limit, rp);
}
bool Solver::isModel() {
    if (hasConflict() || not post_.isModel(*this)) {
        return false;
    }
    return not enumerationConstraint() || enumerationConstraint()->valid(*this);
}
/////////////////////////////////////////////////////////////////////////////////////////
// Free functions
/////////////////////////////////////////////////////////////////////////////////////////
void destroyDB(Solver::ConstraintDB& db, Solver* s, bool detach) {
    if (s && detach) {
        s->destroyDB(db);
        return;
    }
    while (not db.empty()) {
        db.back()->destroy(s, detach);
        db.pop_back();
    }
}
} // namespace Clasp
