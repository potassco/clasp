//
// Copyright (c) 2015-present Benjamin Kaufmann
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
#include <clasp/clingo.h>

#include <clasp/clause.h>
#include <clasp/solver.h>
#include <clasp/weight_constraint.h>

#include <potassco/enum.h>
#include <potassco/error.h>

#include <algorithm>
#include <unordered_map>
namespace Clasp {
/////////////////////////////////////////////////////////////////////////////////////////
// ClingoAssignment
/////////////////////////////////////////////////////////////////////////////////////////
static constexpr uint32_t trail_offset = 1u; // Offset for handling true literal.

ClingoAssignment::ClingoAssignment(const Solver& s) : solver_(&s) {}

auto ClingoAssignment::value(Lit_t lit) const -> ClingoAssignment::Value_t {
    POTASSCO_CHECK_PRE(ClingoAssignment::hasLit(lit), "Invalid literal");
    const uint32_t var = decodeVar(lit);
    switch (solver_->validVar(var) ? solver_->value(var) : value_free) {
        default         : return Value_t::free;
        case value_true : return lit >= 0 ? Value_t::true_ : Value_t::false_;
        case value_false: return lit >= 0 ? Value_t::false_ : Value_t::true_;
    }
}
auto ClingoAssignment::level(Lit_t lit) const -> uint32_t {
    return ClingoAssignment::value(lit) != Value_t::free ? solver_->level(decodeVar(lit)) : UINT32_MAX;
}
auto ClingoAssignment::decision(uint32_t dl) const -> ClingoAssignment::Lit_t {
    POTASSCO_CHECK_PRE(dl <= solver_->decisionLevel(), "Invalid decision level");
    return encodeLit(dl ? solver_->decision(dl) : lit_true);
}
auto ClingoAssignment::trailAt(uint32_t pos) const -> ClingoAssignment::Lit_t {
    POTASSCO_CHECK_PRE(pos < trailSize(), "Invalid trail position");
    return encodeLit(pos != 0 ? solver_->trailLit(pos - trail_offset) : lit_true);
}
auto ClingoAssignment::trailBegin(uint32_t dl) const -> uint32_t {
    POTASSCO_CHECK_PRE(dl <= solver_->decisionLevel(), "Invalid decision level");
    return dl != 0 ? solver_->levelStart(dl) + trail_offset : 0;
}
auto ClingoAssignment::size() const -> uint32_t {
    return std::max(solver_->numVars(), solver_->numProblemVars()) + trail_offset;
}
auto ClingoAssignment::unassigned() const -> uint32_t { return size() - trailSize(); }
bool     ClingoAssignment::hasConflict() const { return solver_->hasConflict(); }
auto ClingoAssignment::level() const -> uint32_t { return solver_->decisionLevel(); }
auto ClingoAssignment::rootLevel() const -> uint32_t { return solver_->rootLevel(); }
bool     ClingoAssignment::hasLit(Lit_t lit) const { return decodeVar(lit) < size(); }
bool     ClingoAssignment::isTotal() const { return unassigned() == 0u; }
auto ClingoAssignment::trailSize() const -> uint32_t { return solver_->numAssignedVars() + trail_offset; }
/////////////////////////////////////////////////////////////////////////////////////////
// ClingoPropagator::CallAdaptor
/////////////////////////////////////////////////////////////////////////////////////////
class ClingoPropagator::CallAdaptor : public Potassco::AbstractPropagator::Control {
public:
    using Propagator = Potassco::AbstractPropagator;
    CallAdaptor(ClingoPropagator& p, Solver& s) : self_(&p), solver_(&s) {}
    // outbound calls to theory propagator
    void attach() { call<&Propagator::attach>("attach", state_init, *this); }
    void propagate(Potassco::LitSpan change) { call<&Propagator::propagate>("propagate", state_prop, *this, change); }
    void check() { call<&Propagator::check>("check", state_prop, *this); }
    void undo(Potassco::LitSpan change) { call<&Propagator::undo>("undo", {}, change); }

    // inbound calls from theory propagator
    bool addClause(Potassco::LitSpan clause, Potassco::ClauseType prop) override {
        POTASSCO_CHECK_PRE(not solver_->hasConflict(), "Invalid addClause() on conflicting assignment");
        self_->toClause(*solver_, clause, prop);
        return self_->addTodo(*solver_, state_);
    }
    bool addWeightConstraint(Potassco::Lit_t con, Potassco::WeightLitSpan lits, Potassco::Weight_t bound,
                             int32_t type) override {
        POTASSCO_CHECK_PRE(not solver_->hasConflict(), "Invalid addWeightConstraint() on conflicting assignment");
        self_->toWeightCon(*solver_, con, lits, bound, type);
        return self_->addTodo(*solver_, state_);
    }
    bool  propagate() override { return self_->propagate(*solver_, state_); }
    Lit_t addVariable(bool) override {
        POTASSCO_CHECK_PRE(not solver_->hasConflict(), "Invalid addVariable() on conflicting assignment");
        return encodeLit(posLit(solver_->pushAuxVar()));
    }
    [[nodiscard]] bool hasWatch(Lit_t lit) const override { return solver_->hasWatch(decodeLit(lit), self_); }

    void addWatch(Lit_t lit) override { self_->addWatch(*solver_, decodeLit(lit), state_); }
    void removeWatch(Lit_t lit) override { solver_->removeWatch(decodeLit(lit), self_); }

private:
    template <auto F, typename... Args>
    void call(const char* call, State st, Args&&... args) {
        POTASSCO_CHECK_PRE(self_->op_ == nullptr, "Invalid call to %s from %s!", call, self_->op_);
        POTASSCO_SCOPE_EXIT({ self_->op_ = nullptr; });
        self_->op_ = call;
        state_     = State{st | state_ctrl};
        (self_->call_->propagator()->*F)(ClingoAssignment{*solver_}, std::forward<Args>(args)...);
    }

    ClingoPropagator* self_;
    Solver*           solver_;
    State             state_{state_ctrl | state_init};
};
/////////////////////////////////////////////////////////////////////////////////////////
// ClingoPropagator
/////////////////////////////////////////////////////////////////////////////////////////
static constexpr uint32_t check_bit      = 31;
static constexpr uint32_t weight_con_bit = 31;
// flags for clauses from propagator
static constexpr ClauseCreator::CreateFlag cc_flags[2] = {
    /* 0: learnt */ ClauseCreator::clause_not_sat | ClauseCreator::clause_int_lbd,
    /* 1: static */ ClauseCreator::clause_no_add | ClauseCreator::clause_explicit};
static constexpr bool isVolatile(Potassco::ClauseType clause) {
    return Potassco::test(clause, Potassco::ClauseType::transient);
}
static constexpr bool isStatic(Potassco::ClauseType clause) {
    return Potassco::test(clause, Potassco::ClauseType::locked);
}
ClingoPropagator::ClingoPropagator(Propagator* p) : call_(p) {}
auto ClingoPropagator::priority() const -> uint32_t { return static_cast<uint32_t>(prio); }
bool     ClingoPropagator::matches(ClingoPropagatorInit* init) const { return call_ == init; }
void     ClingoPropagator::destroy(Solver* s, bool detach) {
    if (s && detach) {
        for (auto v : s->vars()) {
            s->removeWatch(posLit(v), this);
            s->removeWatch(negLit(v), this);
        }
    }
    destroyDB(db_, s, detach);
    PostPropagator::destroy(s, detach);
}

bool ClingoPropagator::init(Solver& s) {
    POTASSCO_CHECK_PRE(s.decisionLevel() == 0 && prop_ <= size32(trail_), "Invalid init");
    s.acquireProblemVars();
    if (s.isMaster() && not call_->frozen()) {
        call_->init();
    }
    CallAdaptor ctrl(*this, s);
    myGen_   = call_->initWatches(myGen_, ctrl);
    front_   = Potassco::test(call_->checkMode(), CheckMode::fixpoint) ? -1 : INT32_MAX;
    propRes_ = state_init;
    return true;
}

bool ClingoPropagator::inTrail(Literal p) const { return contains(trail_, encodeLit(p)); }

void ClingoPropagator::registerUndo(Solver& s, uint32_t data) {
    if (uint32_t dl = s.decisionLevel(); dl != level_) {
        POTASSCO_CHECK_PRE(dl > level_, "Stack property violated");
        // first time we see this level
        s.addUndoWatch(level_ = dl, this);
        undo_.push_back(data);
    }
    else if (not undo_.empty() && data < undo_.back()) {
        POTASSCO_ASSERT(Potassco::test_bit(undo_.back(), check_bit));
        // first time a watched literal is processed on this level
        undo_.back() = data;
    }
}

void ClingoPropagator::registerUndoCheck(Solver& s) {
    if (uint32_t dl = s.decisionLevel()) {
        registerUndo(s, Potassco::set_bit(s.decision(dl).var(), check_bit));
    }
}

auto ClingoPropagator::propagate(Solver& s, Literal p, uint32_t&) -> Constraint::PropResult {
    registerUndo(s, size32(trail_));
    trail_.push_back(encodeLit(p));
    return PropResult(true, true);
}

void ClingoPropagator::undoLevel(Solver& s) {
    POTASSCO_CHECK_PRE(s.decisionLevel() == level_, "Invalid undo");
    uint32_t beg = undo_.back();
    undo_.pop_back();
    CallAdaptor call(*this, s);
    if (Potassco::test_bit(beg, check_bit) && call_->undoMode() == UndoMode::always) {
        assert(beg >= prop_);
        call.undo(Potassco::LitSpan{});
    }

    if (prop_ > beg) {
        Potassco::LitSpan change{trail_.data() + beg, prop_ - beg};
        call.undo(change);
        prop_ = beg;
    }

    if (front_ != INT32_MAX) {
        front_ = -1;
    }

    if (not Potassco::test_bit(beg, check_bit)) {
        trail_.resize(beg);
    }

    if (not undo_.empty()) {
        uint32_t prev = undo_.back();
        if (Potassco::test_bit(prev, check_bit)) {
            prev = Potassco::clear_bit(prev, check_bit);
        }
        else {
            POTASSCO_ASSERT(prev < size32(trail_));
            prev = decodeLit(trail_[prev]).var();
        }
        level_ = s.level(prev);
    }
    else {
        level_ = 0;
    }
}

bool ClingoPropagator::propagateFixpoint(Solver& s, PostPropagator*) {
    POTASSCO_CHECK_PRE(prop_ <= size32(trail_), "Invalid propagate");
    if (not s.sharedContext()->frozen()) {
        return true;
    }
    for (CallAdaptor call(*this, s);;) {
        if (propRes_ == state_init) [[unlikely]] {
            POTASSCO_CHECK_PRE(s.decisionLevel() == 0, "propagate not called on top-level");
            propRes_ = value_true;
            call.attach();
        }
        else if (prop_ != size32(trail_)) {
            // create copy because trail might change during call to user propagation
            temp_.assign(trail_.begin() + static_cast<std::ptrdiff_t>(prop_), trail_.end());
            POTASSCO_CHECK_PRE(s.level(decodeLit(temp_[0]).var()) == s.decisionLevel(),
                               "Propagate must be called on each level");
            prop_ = size32(trail_);
            call.propagate(temp_);
        }
        else if (std::cmp_less(front_, s.numAssignedVars())) {
            registerUndoCheck(s);
            front_ = static_cast<int32_t>(s.numAssignedVars());
            call.check();
        }
        else {
            return true;
        }
        auto pp = std::exchange(propRes_, value_true);
        if (not addTodo(s, state_prop) || ((pp == value_free || s.queueSize()) && not s.propagateUntil(this))) {
            return false;
        }
    }
}

void ClingoPropagator::toClause(Solver& s, const Potassco::LitSpan& clause, Potassco::ClauseType prop) {
    POTASSCO_CHECK_PRE(todo_.empty(), "Assignment not propagated");
    Literal max;
    LitVec& mem = todo_.lits;
    mem.clear();
    for (auto lit : clause) {
        Literal p = decodeLit(lit);
        if (max < p) {
            max = p;
        }
        mem.push_back(p);
    }
    if (aux_ < max) {
        aux_ = max;
    }
    if ((isVolatile(prop) || s.auxVar(max.var())) && not isSentinel(s.sharedContext()->stepLiteral())) {
        mem.push_back(~s.sharedContext()->stepLiteral());
        POTASSCO_CHECK_PRE(s.value(mem.back().var()) != value_free || s.decisionLevel() == 0,
                           "Step literal must be assigned on level 1");
    }
    todo_.clause = ClauseCreator::prepare(s, mem, ClauseCreator::clause_force_simplify, ConstraintType::other);
    todo_.flags  = cc_flags[static_cast<int>(isStatic(prop))];
    if (mem.empty()) {
        mem.push_back(lit_false);
    }
    assert(not todo_.empty());
}
void ClingoPropagator::toWeightCon(Solver& s, Potassco::Lit_t con, const Potassco::WeightLitSpan& lits, Weight_t bound,
                                   int32_t type) {
    POTASSCO_CHECK_PRE(todo_.empty(), "Assignment not propagated");
    todo_.lits.clear();
    todo_.wLits.clear();
    auto flags = WeightConstraint::create_no_add | WeightConstraint::create_no_freeze |
                 WeightConstraint::create_no_share | WeightConstraint::create_no_imp |
                 WeightConstraint::create_conflicting;
    if (type != 0) {
        flags |= type < 0 ? WeightConstraint::create_only_bfb : WeightConstraint::create_only_btb;
    }
    WeightLitVec& mem = todo_.wLits;
    mem.reserve(size32(lits) + 1);
    auto conLit = decodeLit(con);
    for (const auto& [lit, w] : lits) {
        mem.push_back({decodeLit(lit), w});
        if (mem.back().lit > aux_) {
            aux_ = mem.back().lit;
        }
    }
    aux_        = std::max(aux_, conLit);
    auto rep    = WeightLitsRep::create(s, todo_.wLits, bound);
    auto imp    = std::min(WeightConstraint::implicationLevel(s, conLit, rep, flags), s.decisionLevel());
    todo_.flags = Potassco::set_bit(todo_.flags, weight_con_bit) | static_cast<uint32_t>(flags);
    todo_.wLits.resize(rep.size);
    Literal data[4] = {Literal::fromRep(imp), conLit, Literal::fromRep(static_cast<uint32_t>(rep.bound)),
                       Literal::fromRep(static_cast<uint32_t>(rep.reach))};
    todo_.lits.assign(std::begin(data), std::end(data));
}

bool ClingoPropagator::prepareAdd(Solver& s, uint32_t dl, State st) {
    if (dl < s.decisionLevel() && s.isUndoLevel()) {
        if (Potassco::test(st, state_ctrl)) {
            return false;
        }
        if (Potassco::test(st, state_prop)) {
            ClingoPropagator::reset();
            cancelPropagation();
        }
        s.undoUntil(dl);
    }
    return true;
}
bool ClingoPropagator::addTodo(Solver& s, State st) {
    if (s.hasConflict()) {
        POTASSCO_CHECK_PRE(todo_.empty(), "Assignment not propagated");
        return false;
    }
    if (todo_.empty()) {
        return true;
    }
    if (not Potassco::test_bit(todo_.flags, weight_con_bit)) {
        const auto& clause = todo_.clause;
        auto        w0     = clause.size > 0 ? clause.lits[0] : lit_false;
        auto        w1     = clause.size > 1 ? clause.lits[1] : lit_false;
        auto        flags  = ClauseCreator::CreateFlag{todo_.flags};
        bool        local  = Potassco::test(flags, ClauseCreator::clause_no_add);
        if (auto cs = ClauseCreator::status(s, clause); unitOrUnsat(cs)) {
            auto dl =
                Potassco::test(cs, ClauseCreator::status_unsat) && not local ? s.level(w0.var()) : s.level(w1.var());
            if (not prepareAdd(s, dl, st)) {
                return false;
            }
        }
        if (not s.isFalse(w0) || local || s.force(w0, this)) {
            if (auto res = ClauseCreator::create(s, clause, flags); res.local && local) {
                db_.push_back(res.local);
            }
        }
    }
    else {
        POTASSCO_ASSERT(todo_.lits.size() == 4, "expected [imp, con, bound, reach]");
        if (auto imp = todo_.lits[0].rep(); not prepareAdd(s, imp, st)) {
            return false;
        }
        auto lit   = todo_.lits[1];
        auto flags = static_cast<WeightConstraint::CreateFlag>(Potassco::clear_bit(todo_.flags, weight_con_bit));
        auto rep   = WeightLitsRep{.lits  = todo_.wLits.data(),
                                   .size  = size32(todo_.wLits),
                                   .bound = static_cast<Weight_t>(todo_.lits[2].rep()),
                                   .reach = static_cast<Weight_t>(todo_.lits[3].rep())};
        if (auto res = WeightConstraint::create(s, lit, rep, flags); res.local) {
            db_.push_back(res.local);
        }
    }
    todo_.clear();
    return not s.hasConflict();
}
void ClingoPropagator::addWatch(Solver& s, Literal p, State state) {
    POTASSCO_CHECK_PRE(s.validVar(p.var()), "Invalid literal");
    if (not s.hasWatch(p, this)) {
        POTASSCO_CHECK_PRE(not s.sharedContext()->validVar(p.var()) || not s.sharedContext()->eliminated(p.var()),
                           "Watched literal not frozen");
        s.addWatch(p, this);
        if (Potassco::test(state, state_init) && s.isTrue(p)) {
            // are we too late?
            if (not contains(s.trailView(s.assignment().front), p) && not inTrail(p)) {
                uint32_t ignore = 0;
                ClingoPropagator::propagate(s, p, ignore);
            }
        }
    }
}

bool ClingoPropagator::propagate(Solver& s, State state) {
    if (s.hasConflict()) {
        return false;
    }
    if (s.queueSize() == 0 || not Potassco::test(state, state_prop)) {
        propRes_ = value_true;
        return true;
    }
    propRes_ = s.propagateUntil(this, priority_reserved_ufs + 1);
    return propRes_ != value_false;
}

void ClingoPropagator::reason(Solver&, Literal p, LitVec& r) {
    if (not todo_.empty() && todo_.lits[0] == p) {
        std::ranges::transform(todo_.lits.begin() + 1, todo_.lits.end(), std::back_inserter(r), &Literal::operator~);
    }
}

bool ClingoPropagator::simplify(Solver& s, bool) {
    if (not s.validVar(aux_.var())) {
        aux_ = lit_true;
        erase_if(db_, [&](Constraint* con) {
            Var_t mx = 0;
            assert(con);
            if (auto* clause = con->clause(); clause) {
                if (clause->aux()) {
                    auto cc = clause->toLits();
                    mx      = std::ranges::max_element(cc)->var();
                }
            }
            else if (auto* wc = static_cast<WeightConstraint*>(con); wc) {
                mx = wc->maxVar();
            }
            if (not s.validVar(mx)) {
                con->destroy(&s, true);
                return true;
            }
            if (aux_.var() < mx) {
                aux_ = posLit(mx);
            }
            return false;
        });
    }
    simplifyDB(s, db_, false);
    return false;
}

bool ClingoPropagator::isModel(Solver& s) {
    POTASSCO_CHECK_PRE(prop_ == size32(trail_), "Assignment not propagated");
    if (Potassco::test(call_->checkMode(), CheckMode::total)) {
        front_ = -1;
        s.propagateFrom(this);
        front_ = Potassco::test(call_->checkMode(), CheckMode::fixpoint) ? front_ : INT32_MAX;
        return not s.hasConflict() && s.numFreeVars() == 0;
    }
    return true;
}
/////////////////////////////////////////////////////////////////////////////////////////
// ClingoPropagatorInit
/////////////////////////////////////////////////////////////////////////////////////////
struct ClingoPropagatorInit::WatchList {
    enum class State { add, remove, freeze };
    using WatchSet   = std::unordered_map<Potassco::Lit_t, State>;
    using ChangeList = PodVector_t<Potassco::Lit_t>;

    void incGen() {
        if (not changes.empty()) {
            discardVec(changes);
            ++gen;
        }
    }
    void freezeGen(SharedContext& ctx) {
        for (auto c : changes) {
            auto it = watches.find(c);
            POTASSCO_ASSERT(it != watches.end());
            if (it->second == State::add) {
                it->second = State::freeze;
                ctx.setFrozen(decodeVar(it->first), true);
            }
            else {
                watches.erase(it);
            }
        }
    }
    void addChange(Lit_t lit, State state) {
        if (auto [it, added] = watches.try_emplace(lit, state); added || it->second != state) {
            if (added || it->second == State::freeze) {
                changes.push_back(lit);
            }
            it->second = state;
        }
    }
    auto apply(const SharedContext& ctx, Potassco::AbstractPropagator::Control& s, uint32_t solverGen) const -> uint32_t {
        if (gen - solverGen <= 1 || (gen == 1 && solverGen == UINT32_MAX)) {
            // Solver has all but the latest changes.
            for (auto c : changes) {
                if (watches.contains(c)) {
                    s.addWatch(c);
                }
                else {
                    s.removeWatch(c);
                }
            }
        }
        else if (solverGen == 0) {
            // Solver is new and missed previous changes.
            for (auto [lit, g] : watches) {
                POTASSCO_ASSERT(g == WatchList::State::freeze);
                s.addWatch(lit);
            }
        }
        else {
            // Solver skipped at least one generation. This should not happen!
            for (auto v : ctx.vars()) {
                auto lit = encodeLit(posLit(v));
                do {
                    if (watches.contains(lit)) {
                        s.addWatch(lit);
                    }
                    else {
                        s.removeWatch(lit);
                    }
                } while (std::exchange(lit, -lit) > 0);
            }
        }
        return gen;
    }

    ChangeList changes;
    WatchSet   watches;
    uint32_t   gen{1};
};

ClingoPropagatorInit::ClingoPropagatorInit(SharedContext& ctx, Potassco::AbstractPropagator& cb, MapLitCb mapLit,
                                           CheckMode check)
    : ctx_(ctx)
    , prop_(cb)
    , mapLit_(std::move(mapLit))
    , watches_(std::make_unique<WatchList>())
    , check_(check)
    , undo_(UndoMode::def)
    , frozen_(false) {}
ClingoPropagatorInit::~ClingoPropagatorInit() = default;
bool ClingoPropagatorInit::addPropagator(Solver& s) {
    auto* prop = s.getPost<ClingoPropagator>([&](const ClingoPropagator* p) { return p->matches(this); });
    return prop || s.addPost(new ClingoPropagator(this));
}
void ClingoPropagatorInit::init() {
    if (not frozen()) {
        POTASSCO_CHECK_PRE(not ctx_.frozen(), "context already frozen");
        if (ctx_.ok() && ctx_.propagate()) {
            prop_.init(ClingoAssignment{*ctx_.master()}, *this);
        }
        watches_->freezeGen(ctx_);
        frozen_ = true;
    }
}
void ClingoPropagatorInit::unfreeze() {
    if (frozen()) {
        watches_->incGen();
        frozen_ = false;
    }
}
bool ClingoPropagatorInit::frozen() const { return frozen_; }
bool ClingoPropagatorInit::hasConflict() const { return ctx_.master()->hasConflict(); }
void ClingoPropagatorInit::freezeVariable(Lit_t lit) { ctx_.setFrozen(decodeLit(lit).var(), true); }

bool ClingoPropagatorInit::hasWatch(Lit_t lit) const {
    auto it = watches_->watches.find(lit);
    return it != watches_->watches.end() && it->second != WatchList::State::remove;
}
void ClingoPropagatorInit::addWatch(Lit_t lit) { watches_->addChange(lit, WatchList::State::add); }
void ClingoPropagatorInit::removeWatch(Lit_t lit) { watches_->addChange(lit, WatchList::State::remove); }

auto ClingoPropagatorInit::addVariable(bool freeze) -> Lit_t {
    POTASSCO_CHECK_PRE(not ctx_.frozen(), "program already frozen");
    auto var = ctx_.addVar(VarType::atom);
    if (freeze) {
        ctx_.setFrozen(var, true);
    }
    return encodeLit(posLit(var));
}
bool ClingoPropagatorInit::addClause(Potassco::LitSpan clause, Potassco::ClauseType type) {
    POTASSCO_CHECK_PRE(not ctx_.frozen(), "program already frozen");
    if (hasConflict()) {
        return false;
    }
    mem_.clear();
    for (const auto& lit : clause) { mem_.push_back(decodeLit(lit)); }
    if (isVolatile(type)) {
        mem_.push_back(~ctx_.requireStepVar());
    }
    return ClauseCreator::create(*ctx_.master(), mem_, ClauseCreator::clause_force_simplify).ok();
}
bool ClingoPropagatorInit::addWeightConstraint(Lit_t con, Potassco::WeightLitSpan lits, Weight_t bound, int32_t type) {
    POTASSCO_CHECK_PRE(not ctx_.frozen(), "program already frozen");
    if (hasConflict()) {
        return false;
    }
    WeightLitVec clits;
    clits.reserve(size32(lits));
    for (const auto& [lit, w] : lits) { clits.push_back({decodeLit(lit), w}); }
    auto flags = WeightConstraint::CreateFlag{};
    if (type != 0) {
        flags |= type < 0 ? WeightConstraint::create_only_bfb : WeightConstraint::create_only_btb;
    }
    return WeightConstraint::create(*ctx_.master(), decodeLit(con), clits, bound, flags).ok();
}
void ClingoPropagatorInit::addMinimize(Weight_t prio, Potassco::WeightLit lit) {
    POTASSCO_CHECK_PRE(not ctx_.frozen(), "program already frozen");
    if (hasConflict()) {
        return;
    }
    ctx_.addMinimize({decodeLit(lit.lit), lit.weight}, prio);
}
bool ClingoPropagatorInit::propagate() { return not hasConflict() && ctx_.propagate(); }

auto ClingoPropagatorInit::initWatches(uint32_t gen, Potassco::AbstractPropagator::Control& s) -> uint32_t {
    return watches_->apply(ctx_, s, gen);
}

void ClingoPropagatorInit::setCheckMode(CheckMode m) { check_ = m; }
void ClingoPropagatorInit::setUndoMode(UndoMode m) { undo_ = m; }
auto ClingoPropagatorInit::numSolver() const -> uint32_t { return ctx_.concurrency(); }
auto ClingoPropagatorInit::solverLiteral(Lit_t lit) const -> Lit_t { return mapLit_ ? mapLit_(lit) : lit; }

/////////////////////////////////////////////////////////////////////////////////////////
// ClingoHeuristic
/////////////////////////////////////////////////////////////////////////////////////////
ClingoHeuristic::ClingoHeuristic(Potassco::AbstractHeuristic& clingoHeuristic, DecisionHeuristic* claspHeuristic)
    : clingo_(&clingoHeuristic)
    , clasp_(claspHeuristic) {}

auto ClingoHeuristic::doSelect(Solver& s) -> Literal {
    auto decision = clasp_->doSelect(s);
    if (not s.hasConflict()) {
        ClingoAssignment assignment(s);
        auto             lit = clingo_->decide(assignment, encodeLit(decision));
        if (Literal user; lit != 0 && s.validVar((user = decodeLit(lit)).var()) && not s.isFalse(user)) {
            decision = user;
        }
    }
    return decision;
}

void ClingoHeuristic::startInit(const Solver& s) { clasp_->startInit(s); }
void ClingoHeuristic::endInit(Solver& s) { clasp_->endInit(s); }
void ClingoHeuristic::detach(Solver& s) {
    if (clasp_) {
        clasp_->detach(s);
    }
}
void ClingoHeuristic::setConfig(const HeuParams& p) { clasp_->setConfig(p); }
void ClingoHeuristic::newConstraint(const Solver& s, LitView lits, ConstraintType t) {
    clasp_->newConstraint(s, lits, t);
}

void    ClingoHeuristic::updateVar(const Solver& s, Var_t v, uint32_t n) { clasp_->updateVar(s, v, n); }
void    ClingoHeuristic::simplify(const Solver& s, LitView sp) { clasp_->simplify(s, sp); }
void    ClingoHeuristic::undo(const Solver& s, LitView undo) { clasp_->undo(s, undo); }
void    ClingoHeuristic::updateReason(const Solver& s, LitView x, Literal r) { clasp_->updateReason(s, x, r); }
bool    ClingoHeuristic::bump(const Solver& s, WeightLitView w, double d) { return clasp_->bump(s, w, d); }
auto ClingoHeuristic::selectRange(Solver& s, LitView range) -> Literal { return clasp_->selectRange(s, range); }

auto ClingoHeuristic::fallback() const -> DecisionHeuristic* { return clasp_.get(); }

} // namespace Clasp
