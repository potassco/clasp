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

#include <potassco/enum.h>

#include <algorithm>
#include <unordered_map>
namespace Clasp {
namespace {
template <class O, class L, void (L::*Enter)(), void (L::*Exit)(), class Op>
struct Scoped {
    Scoped(L* lk, O* ptr, const Op& o = Op()) : lock(lk), obj(ptr), op(o) {
        if (lock) {
            (lock->*Enter)();
        }
    }
    ~Scoped() {
        if (lock) {
            (lock->*Exit)();
        }
    }
    O* operator->() const {
        op();
        return obj;
    }
    L* lock;
    O* obj;
    Op op;
};
struct Nop {
    constexpr void operator()() const {}
};
struct Inc {
    explicit Inc(uint32_t& e) : epoch(&e) {}
    constexpr void operator()() const { ++*epoch; }
    uint32_t*      epoch;
};
using ScopedLock = Scoped<Potassco::AbstractPropagator, ClingoPropagatorLock, &ClingoPropagatorLock::lock,
                          &ClingoPropagatorLock::unlock, Inc>;
using ScopedUnlock =
    Scoped<ClingoPropagator, ClingoPropagatorLock, &ClingoPropagatorLock::unlock, &ClingoPropagatorLock::lock, Nop>;
} // namespace
ClingoPropagatorLock::~ClingoPropagatorLock() = default;
/////////////////////////////////////////////////////////////////////////////////////////
// ClingoAssignment
/////////////////////////////////////////////////////////////////////////////////////////
static constexpr uint32_t trail_offset = 1u; // Offset for handling true literal.

ClingoAssignment::ClingoAssignment(const Solver& s) : solver_(&s) {}

ClingoAssignment::Value_t ClingoAssignment::value(Lit_t lit) const {
    POTASSCO_CHECK_PRE(ClingoAssignment::hasLit(lit), "Invalid literal");
    const uint32_t var = decodeVar(lit);
    switch (solver_->validVar(var) ? solver_->value(var) : value_free) {
        default         : return Value_t::free;
        case value_true : return lit >= 0 ? Value_t::true_ : Value_t::false_;
        case value_false: return lit >= 0 ? Value_t::false_ : Value_t::true_;
    }
}
uint32_t ClingoAssignment::level(Lit_t lit) const {
    return ClingoAssignment::value(lit) != Value_t::free ? solver_->level(decodeVar(lit)) : UINT32_MAX;
}
ClingoAssignment::Lit_t ClingoAssignment::decision(uint32_t dl) const {
    POTASSCO_CHECK_PRE(dl <= solver_->decisionLevel(), "Invalid decision level");
    return encodeLit(dl ? solver_->decision(dl) : lit_true);
}
ClingoAssignment::Lit_t ClingoAssignment::trailAt(uint32_t pos) const {
    POTASSCO_CHECK_PRE(pos < trailSize(), "Invalid trail position");
    return encodeLit(pos != 0 ? solver_->trailLit(pos - trail_offset) : lit_true);
}
uint32_t ClingoAssignment::trailBegin(uint32_t dl) const {
    POTASSCO_CHECK_PRE(dl <= solver_->decisionLevel(), "Invalid decision level");
    return dl != 0 ? solver_->levelStart(dl) + trail_offset : 0;
}
uint32_t ClingoAssignment::size() const {
    return std::max(solver_->numVars(), solver_->numProblemVars()) + trail_offset;
}
uint32_t ClingoAssignment::unassigned() const { return size() - trailSize(); }
bool     ClingoAssignment::hasConflict() const { return solver_->hasConflict(); }
uint32_t ClingoAssignment::level() const { return solver_->decisionLevel(); }
uint32_t ClingoAssignment::rootLevel() const { return solver_->rootLevel(); }
bool     ClingoAssignment::hasLit(Lit_t lit) const { return decodeVar(lit) < size(); }
bool     ClingoAssignment::isTotal() const { return unassigned() == 0u; }
uint32_t ClingoAssignment::trailSize() const { return solver_->numAssignedVars() + trail_offset; }
/////////////////////////////////////////////////////////////////////////////////////////
// ClingoPropagator::Control
/////////////////////////////////////////////////////////////////////////////////////////
class ClingoPropagator::Control : public Potassco::AbstractSolver {
public:
    Control(ClingoPropagator& ctx, const Solver& s, State st = {})
        : ctx_(&ctx)
        , assignment_(s)
        , state_{st | state_ctrl} {}
    [[nodiscard]] const Potassco::AbstractAssignment& assignment() const override { return assignment_; }

    // Potassco::AbstractSolver
    [[nodiscard]] Potassco::Id_t id() const override { return solver().id(); }
    bool                         addClause(Potassco::LitSpan clause, Potassco::ClauseType prop) override;
    bool                         propagate() override;
    Lit_t                        addVariable() override;
    [[nodiscard]] bool           hasWatch(Lit_t lit) const override;
    void                         addWatch(Lit_t lit) override;
    void                         removeWatch(Lit_t lit) override;

private:
    using State = ClingoPropagator::State;
    [[nodiscard]] ClingoPropagatorLock* lock() const {
        return not Potassco::test(state_, state_init) ? ctx_->call_->lock() : nullptr;
    }
    [[nodiscard]] Solver& solver() const { return const_cast<Solver&>(assignment_.solver()); }
    ClingoPropagator*     ctx_;
    ClingoAssignment      assignment_;
    State                 state_;
};
bool ClingoPropagator::Control::addClause(Potassco::LitSpan clause, Potassco::ClauseType prop) {
    POTASSCO_CHECK_PRE(not assignment_.hasConflict(), "Invalid addClause() on conflicting assignment");
    ScopedUnlock pp(lock(), ctx_);
    pp->toClause(solver(), clause, prop);
    return pp->addClause(solver(), state_);
}
bool ClingoPropagator::Control::propagate() {
    ScopedUnlock unlocked(lock(), ctx_);
    if (solver().hasConflict()) {
        return false;
    }
    if (solver().queueSize() == 0) {
        return true;
    }

    auto epoch = ctx_->epoch_;
    ctx_->registerUndoCheck(solver());
    ctx_->propL_ = solver().decisionLevel();
    const bool result =
        Potassco::test(state_, state_prop) && solver().propagateUntil(unlocked.obj) && epoch == ctx_->epoch_;
    ctx_->propL_ = UINT32_MAX;
    return result;
}
Potassco::Lit_t ClingoPropagator::Control::addVariable() {
    POTASSCO_CHECK_PRE(not assignment_.hasConflict(), "Invalid addVariable() on conflicting assignment");
    ScopedUnlock unlocked(lock(), ctx_);
    return encodeLit(posLit(solver().pushAuxVar()));
}
bool ClingoPropagator::Control::hasWatch(Lit_t lit) const {
    ScopedUnlock unlocked(lock(), ctx_);
    return assignment_.hasLit(lit) && solver().hasWatch(decodeLit(lit), ctx_);
}
void ClingoPropagator::Control::addWatch(Lit_t lit) {
    ScopedUnlock unlocked(lock(), ctx_);
    POTASSCO_CHECK_PRE(assignment_.hasLit(lit), "Invalid literal");
    Literal p = decodeLit(lit);
    Solver& s = solver();
    if (not s.hasWatch(p, ctx_)) {
        POTASSCO_CHECK_PRE(not s.sharedContext()->validVar(p.var()) || not s.sharedContext()->eliminated(p.var()),
                           "Watched literal not frozen");
        s.addWatch(p, ctx_);
        if (Potassco::test(state_, state_init) && s.isTrue(p)) {
            // are we too late?
            if (not contains(s.trailView(s.assignment().front), p) && not ctx_->inTrail(p)) {
                uint32_t ignore = 0;
                ctx_->propagate(s, p, ignore);
            }
        }
    }
}
void ClingoPropagator::Control::removeWatch(Lit_t lit) {
    ScopedUnlock unlocked(lock(), ctx_);
    if (assignment_.hasLit(lit)) {
        solver().removeWatch(decodeLit(lit), ctx_);
    }
}
/////////////////////////////////////////////////////////////////////////////////////////
// ClingoPropagator
/////////////////////////////////////////////////////////////////////////////////////////
static constexpr uint32_t check_bit = 31;
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
uint32_t ClingoPropagator::priority() const { return static_cast<uint32_t>(priority_class_general); }

void ClingoPropagator::destroy(Solver* s, bool detach) {
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
    Control ctrl(*this, s, state_init);
    s.acquireProblemVars();
    if (s.isMaster() && not s.sharedContext()->frozen()) {
        call_->prepare(const_cast<SharedContext&>(*s.sharedContext()));
    }
    init_  = call_->init(init_, ctrl);
    front_ = Potassco::test(call_->checkMode(), ClingoPropagatorCheckType::fixpoint) ? -1 : INT32_MAX;
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

Constraint::PropResult ClingoPropagator::propagate(Solver& s, Literal p, uint32_t&) {
    registerUndo(s, size32(trail_));
    trail_.push_back(encodeLit(p));
    return PropResult(true, true);
}

void ClingoPropagator::undoLevel(Solver& s) {
    POTASSCO_CHECK_PRE(s.decisionLevel() == level_, "Invalid undo");
    uint32_t beg = undo_.back();
    undo_.pop_back();

    if (Potassco::test_bit(beg, check_bit) && call_->undoMode() == ClingoPropagatorUndoType::always) {
        assert(beg >= prop_);
        Potassco::LitSpan change;
        ScopedLock(call_->lock(), call_->propagator(), Inc(epoch_))->undo(Control(*this, s), change);
    }

    if (prop_ > beg) {
        Potassco::LitSpan change{trail_.data() + beg, prop_ - beg};
        ScopedLock(call_->lock(), call_->propagator(), Inc(epoch_))->undo(Control(*this, s), change);
        prop_ = beg;
    }
    else if (level_ == propL_) {
        propL_ = UINT32_MAX;
        ++epoch_;
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
    for (Control ctrl(*this, s, state_prop); prop_ != size32(trail_) || std::cmp_less(front_, s.numAssignedVars());) {
        if (prop_ != size32(trail_)) {
            // create copy because trail might change during call to user propagation
            temp_.assign(trail_.begin() + static_cast<std::ptrdiff_t>(prop_), trail_.end());
            POTASSCO_CHECK_PRE(s.level(decodeLit(temp_[0]).var()) == s.decisionLevel(),
                               "Propagate must be called on each level");
            prop_ = size32(trail_);
            ScopedLock(call_->lock(), call_->propagator(), Inc(epoch_))->propagate(ctrl, temp_);
        }
        else {
            registerUndoCheck(s);
            front_ = static_cast<int32_t>(s.numAssignedVars());
            ScopedLock(call_->lock(), call_->propagator(), Inc(epoch_))->check(ctrl);
        }
        if (not addClause(s, state_prop) || (s.queueSize() && not s.propagateUntil(this))) {
            return false;
        }
    }
    return true;
}

void ClingoPropagator::toClause(Solver& s, const Potassco::LitSpan& clause, Potassco::ClauseType prop) {
    POTASSCO_CHECK_PRE(todo_.empty(), "Assignment not propagated");
    Literal max;
    LitVec& mem = todo_.mem;
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
    todo_.clause = ClauseCreator::prepare(s, mem, Clasp::ClauseCreator::clause_force_simplify, ConstraintType::other);
    todo_.flags  = cc_flags[static_cast<int>(isStatic(prop))];
    if (mem.empty()) {
        mem.push_back(lit_false);
    }
}
bool ClingoPropagator::addClause(Solver& s, State st) {
    if (s.hasConflict()) {
        POTASSCO_CHECK_PRE(todo_.empty(), "Assignment not propagated");
        return false;
    }
    if (todo_.empty()) {
        return true;
    }
    const ClauseRep& clause = todo_.clause;
    Literal          w0     = clause.size > 0 ? clause.lits[0] : lit_false;
    Literal          w1     = clause.size > 1 ? clause.lits[1] : lit_false;
    auto             flags  = ClauseCreator::CreateFlag{todo_.flags};
    bool             local  = Potassco::test(flags, ClauseCreator::clause_no_add);
    if (auto cs = ClauseCreator::status(s, clause); unitOrUnsat(cs)) {
        auto dl = Potassco::test(cs, ClauseCreator::status_unsat) && not local ? s.level(w0.var()) : s.level(w1.var());
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
    }
    if (not s.isFalse(w0) || local || s.force(w0, this)) {
        if (auto res = ClauseCreator::create(s, clause, flags); res.local && local) {
            db_.push_back(res.local);
        }
    }
    todo_.clear();
    return not s.hasConflict();
}

void ClingoPropagator::reason(Solver&, Literal p, LitVec& r) {
    if (not todo_.empty() && todo_.mem[0] == p) {
        std::ranges::transform(todo_.mem.begin() + 1, todo_.mem.end(), std::back_inserter(r), &Literal::operator~);
    }
}

bool ClingoPropagator::simplify(Solver& s, bool) {
    if (not s.validVar(aux_.var())) {
        ClauseHead::SmallBuffer buffer;
        aux_ = lit_true;
        erase_if(db_, [&](Constraint* con) {
            if (ClauseHead* clause = con->clause(); clause && clause->aux()) {
                auto cc = clause->toLits(buffer);
                if (Literal x = *std::ranges::max_element(cc); not s.validVar(x.var())) {
                    clause->destroy(&s, true);
                    return true;
                }
                else if (aux_ < x) {
                    aux_ = x;
                }
            }
            return false;
        });
    }
    simplifyDB(s, db_, false);
    return false;
}

bool ClingoPropagator::isModel(Solver& s) {
    POTASSCO_CHECK_PRE(prop_ == size32(trail_), "Assignment not propagated");
    if (Potassco::test(call_->checkMode(), ClingoPropagatorCheckType::total)) {
        front_ = -1;
        s.propagateFrom(this);
        front_ = Potassco::test(call_->checkMode(), ClingoPropagatorCheckType::fixpoint) ? front_ : INT32_MAX;
        return not s.hasConflict() && s.numFreeVars() == 0;
    }
    return true;
}
/////////////////////////////////////////////////////////////////////////////////////////
// ClingoPropagatorInit
/////////////////////////////////////////////////////////////////////////////////////////
struct ClingoPropagatorInit::Change::Less {
    bool operator()(const Change& lhs, const Change& rhs) const {
        auto x = std::abs(lhs.lit) <=> std::abs(rhs.lit);
        return x != std::strong_ordering::equal ? x == std::strong_ordering::less : lhs.lit < rhs.lit;
    }
};
ClingoPropagatorInit::Change::Change(Lit_t p, Action a) : lit(p), sId(-1), action(static_cast<int16_t>(a)) {}
ClingoPropagatorInit::Change::Change(Lit_t p, Action a, uint32_t s)
    : lit(p)
    , sId(static_cast<int16_t>(s))
    , action(static_cast<int16_t>(a)) {}
uint64_t ClingoPropagatorInit::Change::solverMask() const {
    return static_cast<uint32_t>(sId) > 63 ? UINT64_MAX : Potassco::nth_bit<uint64_t>(static_cast<uint32_t>(sId));
}
void ClingoPropagatorInit::Change::apply(Potassco::AbstractSolver& s) const {
    switch (action) {
        case add_watch   : s.addWatch(lit); break;
        case remove_watch: s.removeWatch(lit); break;
        default          : break;
    }
}

struct ClingoPropagatorInit::History : std::unordered_map<Potassco::Lit_t, uint64_t> {
    void add(const Change& change) {
        if (auto sm = change.solverMask(); change.action == add_watch) {
            auto [it, _] = emplace(change.lit, 0);
            Potassco::store_set_mask(it->second, sm);
        }
        else if (change.action == remove_watch) {
            if (auto it = find(change.lit); it != end() && Potassco::store_clear_mask(it->second, sm) == 0) {
                erase(it);
            }
        }
    }
};

ClingoPropagatorInit::ClingoPropagatorInit(Potassco::AbstractPropagator& cb, ClingoPropagatorLock* lock, CheckType m)
    : prop_(&cb)
    , lock_(lock)
    , history_(nullptr)
    , step_(1)
    , check_(m)
    , undo_(ClingoPropagatorUndoType::def) {}
ClingoPropagatorInit::~ClingoPropagatorInit() = default;
bool ClingoPropagatorInit::applyConfig(Solver& s) { return s.addPost(new ClingoPropagator(this)); }
void ClingoPropagatorInit::prepare(SharedContext& ctx) {
    std::ranges::stable_sort(changes_, Change::Less{});
    for (auto it = changes_.begin(), end = changes_.end(); it != end;) {
        Lit_t    lit      = it->lit;
        uint64_t addWatch = 0;
        bool     freeze   = false;
        do {
            switch (it->action) {
                case add_watch   : Potassco::store_set_mask(addWatch, it->solverMask()); break;
                case remove_watch: Potassco::store_clear_mask(addWatch, it->solverMask()); break;
                case freeze_lit  : freeze = true; break;
                default          : break;
            }
        } while (++it != end && it->lit == lit);
        if (freeze || addWatch) {
            ctx.setFrozen(decodeVar(lit), true);
        }
    }
}
void ClingoPropagatorInit::unfreeze(SharedContext&) {
    if (history_) {
        for (const auto& change : changes_) { history_->add(change); }
    }
    discardVec(changes_);
    ++step_;
}

void ClingoPropagatorInit::freezeLit(Literal lit) { changes_.push_back(Change(encodeLit(lit), freeze_lit, 64)); }

Potassco::Lit_t ClingoPropagatorInit::addWatch(Literal lit) {
    changes_.push_back(Change(encodeLit(lit), add_watch));
    return changes_.back().lit;
}

Potassco::Lit_t ClingoPropagatorInit::addWatch(uint32_t sId, Literal lit) {
    POTASSCO_CHECK_PRE(sId < 64, "Invalid solver id");
    changes_.push_back(Change(encodeLit(lit), add_watch, sId));
    return changes_.back().lit;
}

void ClingoPropagatorInit::removeWatch(Literal lit) { changes_.push_back(Change(encodeLit(lit), remove_watch)); }

void ClingoPropagatorInit::removeWatch(uint32_t sId, Literal lit) {
    POTASSCO_CHECK_PRE(sId < 64, "Invalid solver id");
    changes_.push_back(Change(encodeLit(lit), remove_watch, sId));
}

uint32_t ClingoPropagatorInit::init(uint32_t lastStep, Potassco::AbstractSolver& s) {
    POTASSCO_CHECK_PRE(s.id() < 64, "Invalid solver id");
    auto sId = s.id();
    if (history_ && (step_ - lastStep) > 1) {
        for (const auto& [lit, mask] : *history_) {
            if (Potassco::test_bit(mask, sId)) {
                Change(lit, add_watch, sId).apply(s);
            }
        }
    }
    ChangeList changesForSolver;
    bool       isSorted = true;
    auto       lessLit  = Change::Less{};
    for (const auto& change : changes_) {
        if (change.sId < 0 || std::cmp_equal(change.sId, sId)) {
            isSorted = isSorted && (changesForSolver.empty() || not lessLit(change, changesForSolver.back()));
            changesForSolver.push_back(change);
        }
    }
    if (not isSorted) {
        std::ranges::stable_sort(changesForSolver, lessLit);
    }
    for (auto it = changesForSolver.begin(), end = changesForSolver.end(); it != end; ++it) {
        auto lit = it->lit;
        // skip all but the last change for a given literal
        while ((it + 1) != end && (it + 1)->lit == lit) { ++it; }
        it->apply(s);
    }
    return step_;
}

void ClingoPropagatorInit::enableClingoPropagatorCheck(CheckType checkMode) { check_ = checkMode; }

void ClingoPropagatorInit::enableClingoPropagatorUndo(UndoType undoMode) { undo_ = undoMode; }

void ClingoPropagatorInit::enableHistory(bool b) {
    if (not b) {
        history_.reset();
    }
    else if (not history_) {
        history_ = std::make_unique<History>();
    }
}

/////////////////////////////////////////////////////////////////////////////////////////
// ClingoHeuristic
/////////////////////////////////////////////////////////////////////////////////////////
ClingoHeuristic::ClingoHeuristic(Potassco::AbstractHeuristic& clingoHeuristic, DecisionHeuristic* claspHeuristic,
                                 ClingoPropagatorLock* lock)
    : clingo_(&clingoHeuristic)
    , clasp_(claspHeuristic)
    , lock_(lock) {}

Literal ClingoHeuristic::doSelect(Solver& s) {
    using LockT = Scoped<Potassco::AbstractHeuristic, ClingoPropagatorLock, &ClingoPropagatorLock::lock,
                         &ClingoPropagatorLock::unlock, Nop>;

    auto decision = clasp_->doSelect(s);
    if (not s.hasConflict()) {
        ClingoAssignment assignment(s);
        auto             lit = LockT(lock_, clingo_)->decide(s.id(), assignment, encodeLit(decision));
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
Literal ClingoHeuristic::selectRange(Solver& s, LitView range) { return clasp_->selectRange(s, range); }

DecisionHeuristic* ClingoHeuristic::fallback() const { return clasp_.get(); }

BasicSatConfig::HeuristicCreator ClingoHeuristic::creator(Potassco::AbstractHeuristic& clingoHeuristic,
                                                          ClingoPropagatorLock*        lock) {
    return [heu = &clingoHeuristic, lock](HeuristicType t, const HeuParams& p) {
        return new ClingoHeuristic(*heu, createHeuristic(t, p), lock);
    };
}

} // namespace Clasp
