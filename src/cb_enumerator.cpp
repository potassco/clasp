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
#include <clasp/cb_enumerator.h>
#include <clasp/clause.h>
#include <clasp/solver.h>
namespace Clasp {
/////////////////////////////////////////////////////////////////////////////////////////
// CBConsequences::ModelFinder
/////////////////////////////////////////////////////////////////////////////////////////
class CBConsequences::ModelFinder : public EnumerationConstraint {
public:
    explicit ModelFinder(SharedConstraint* shared) : shared_(shared) {}

private:
    [[nodiscard]] auto fetchShared() const -> SharedLiterals* {
        auto* val = shared_->lock();
        auto* ret = val && val != last_ ? val->share() : nullptr;
        shared_->store_unlock(val);
        return ret;
    }
    auto clone() -> ConPtr override { return new ModelFinder(shared_); }
    void doCommitModel(Enumerator& ctx, Solver& s) override {
        auto& cb = static_cast<CBConsequences&>(ctx); // NOLINT
        updateModel(cb.type_, cb.candidates_, s);
        if (shared_) {
            cb.setShared(SharedLiterals::newShareable(current_, ConstraintType::other, 1));
        }
    }
    bool doExtractModel(Solver&, ValueVec& out, bool sat) override {
        if (sat && not lastM_.empty()) {
            out = std::move(lastM_);
            return true;
        }
        return false;
    }
    void destroy(Solver* s, bool detach) override;
    bool doUpdate(Solver& s) override;
    void pushLocked(Solver& s, ClauseHead* c);
    void updateModel(CBConsequences::Type type, LitVec& candidates, const Solver& s);

    SharedConstraint* shared_{nullptr};
    SharedLiterals*   last_{nullptr};
    LitVec            current_;
    ConstraintVec     locked_;
    ValueVec          lastM_;
};
void CBConsequences::ModelFinder::destroy(Solver* s, bool detach) {
    destroyDB(locked_, s, detach);
    if (last_) {
        last_->release();
    }
    EnumerationConstraint::destroy(s, detach);
}
void CBConsequences::ModelFinder::pushLocked(Solver& s, ClauseHead* c) {
    for (ClauseHead* h; not locked_.empty() && not(h = static_cast<ClauseHead*>(locked_.back()))->locked(s);) {
        h->destroy(&s, true);
        locked_.pop_back();
    }
    locked_.push_back(c);
}
void CBConsequences::ModelFinder::updateModel(CBConsequences::Type type, LitVec& candidates, const Solver& s) {
    // reset state of variables
    lastM_.assign(s.numVars() + 1, value_free);
    auto root = rootLevel();
    current_.assign(1, ~s.sharedContext()->stepLiteral());
    // let M be all lits p with p.watch() == true
    for (auto& p : candidates) {
        auto dl  = s.level(p.var());
        auto ost = dl > root ? Model::estMask(p) : 0u;
        if (type == brave) {
            // brave: extend M with true literals and force a literal not in M to true
            if (p.flagged() || s.isTrue(p)) {
                p.flag();
                ost = 0u;
            }
            else if (dl) {
                current_.push_back(p);
            }
        }
        else {
            // cautious: intersect M with true literals and force a literal in M to false
            if (not p.flagged() || s.isFalse(p)) {
                p.unflag();
                ost = 0u;
            }
            else if (dl) {
                current_.push_back(~p);
            }
        }
        // set output state
        if (p.flagged()) {
            ost |= trueValue(p);
        }
        lastM_[p.var()] |= ost;
    }
}
bool CBConsequences::ModelFinder::doUpdate(Solver& s) {
    auto ret   = ClauseCreator::Result{};
    auto flags = ClauseCreator::clause_explicit | ClauseCreator::clause_no_add;
    lastM_.clear();
    if (not shared_) {
        ret = not current_.empty() ? ClauseCreator::create(s, current_, flags, ConstraintInfo(ConstraintType::other))
                                   : ClauseCreator::Result();
    }
    else if (auto* x = fetchShared(); x) {
        if (auto* prev = std::exchange(last_, x); prev) {
            prev->release();
        }
        ret = ClauseCreator::integrate(s, x, flags | ClauseCreator::clause_no_release);
    }
    if (ret.local) {
        pushLocked(s, ret.local);
    }
    current_.clear();
    return ret.ok();
}
/////////////////////////////////////////////////////////////////////////////////////////
// CBConsequences::QueryFinder
/////////////////////////////////////////////////////////////////////////////////////////
class CBConsequences::QueryFinder : public EnumerationConstraint {
public:
    using QueryType = CBConsequences::Type;
    // Maintains query state for each (relevant) variable v in 4-bits, 2-bits per literal:
    // - answer-bits: bits 0 and 1 store whether v and/or ~v are a consequence so far
    // - open-bits  : bits 2 and 3 store whether v or ~v are still in the estimate
    // Invariants before first model
    //  - all bits are zero
    // Invariants after first model (initEstimate has been called):
    //  - at most 2 of the 4-bits are set at the same time
    //  - open-bits are never both set at the same time, i.e. at most one literal of v is in the estimate
    //  - for cautious, answer-bits are never both set, i.e. at most one literal of v can be a cautious consequence
    //  - for cautious, open-bit set for literal l implies l's answer-bit is set
    //  - for brave, open-bit set for literal l implies l's answer-bit is not set
    // Together, the two bits for a literal l encode the possible states for l:
    //      O A
    //  - common
    //    - 0 0: l is known not to be a brave/cautious consequence
    //    - 0 1: l is known to be a brave/cautious consequence
    //  - cautious:
    //    - 1 0: invalid, not used
    //    - 1 1: l is estimated to be a cautious consequence (undecided, but l has been true in all models so far)
    //  - brave:
    //    - 1 0: l is not yet a brave consequence (undecided, l has beem false in all models so far)
    //    - 1 1: invalid, not used
    class State {
    public:
        static constexpr auto     invalid = static_cast<uint8_t>(Model::estMask(lit_true) | Model::estMask(lit_false));
        [[nodiscard]] static bool open(Literal p, Val_t xs) { return Potassco::test_any(xs, Model::estMask(p)); }
        [[nodiscard]] static auto openMask(Literal p) -> Val_t { return Model::estMask(p); }
        explicit State(QueryType t, bool shared, uint32_t nVars)
            : value_(std::make_unique<ValueType[]>(nVars))
            , size_(nVars)
            , cautious_(t == cautious)
            , refs_(1) {
            if (shared) {
                ro_ = mt::memory_order_acquire;
                wo_ = mt::memory_order_release;
            }
        }
        auto share() -> State* {
            assert(ro_ == mt::memory_order_acquire && wo_ == mt::memory_order_release);
            refs_.add();
            return this;
        }
        void release() {
            if (refs_.release()) {
                delete this;
            }
        }
        [[nodiscard]] auto type() const -> QueryType { return cautious_ ? cautious : brave; }
        [[nodiscard]] bool open(Literal p) const { return open(p, get(p)); }
        [[nodiscard]] auto get(Literal p) const -> Val_t { return value_[p.var()].load(ro_); }
        [[nodiscard]] bool hasModel() const { return value_[0].load(ro_) == value_true; }
        void               getModel(ValueVec& m) const { m.assign(value_.get(), value_.get() + size_); }

        void set(Literal p, Val_t val) {
            assert(val < invalid);
            value_[p.var()].store(val, wo_);
        }

    private:
        using ValueType = mt::ThreadSafe<Val_t>;
        using ValueVec  = std::unique_ptr<ValueType[]>;
        using MemOrder  = mt::MemoryOrder;
        ValueVec value_;
        uint32_t size_     : 31u;
        uint32_t cautious_ : 1u;
        RefCount refs_;
        MemOrder ro_{mt::memory_order_relaxed};
        MemOrder wo_{mt::memory_order_relaxed};
    };
    explicit QueryFinder(QueryType t, bool shared, LitVec&& c, uint32_t nVars)
        : open_(std::move(c))
        , state_(new State(t, shared, nVars))
        , query_(lit_false) {
        POTASSCO_ASSERT(not state_->hasModel());
    }
    explicit QueryFinder(LitVec c, State* st) : open_(std::move(c)), state_(st), query_(lit_false) {}
    ~QueryFinder() override { state_->release(); }
    auto clone() -> ConPtr override {
        POTASSCO_ASSERT(query_ == lit_false && not state_->hasModel());
        return new QueryFinder(open_, state_->share());
    }
    bool doUpdate(Solver& s) override;
    void doCommitModel(Enumerator&, Solver&) override;
    void doCommitUnsat(Enumerator&, Solver&) override;
    bool doExtractModel(Solver& s, ValueVec& out, bool sat) override;
    void initEstimate(const Solver& s);
    void updateEstimate(const Solver& s);
    bool simplifyOpen(const Solver& s);
    void reason(Solver& s, Literal p, LitVec& out) override {
        for (uint32_t i = 1, end = s.level(p.var()); i <= end; ++i) {
            if (Literal q = s.decision(i); q != p) {
                out.push_back(q);
            }
        }
    }
    bool popQuery(Solver& s) { // NOLINT(readability-make-member-function-const)
        if (query_ != lit_false && s.value(query_.var()) != value_free) {
            auto diff = s.rootLevel() - s.level(query_.var());
            return s.popRootLevel(diff + 1);
        }
        return s.popRootLevel(0);
    }

private:
    bool    model_{false};
    LitVec  open_;
    State*  state_;
    Literal query_;
};
// Initializes state with the first model (implicitly stored in s).
// Let M be the current model stored in s and F \subseteq M the set of facts wrt the global root level.
// Cautious: Est = M \ F;    Def = F.
// Brave   : Est = all false literals from DL > Root; Def = F.
void CBConsequences::QueryFinder::initEstimate(const Solver& s) {
    const auto type = state_->type();
    auto       j    = open_.begin();
    auto       root = rootLevel();
    for (auto x : open_) {
        auto xs = state_->get(x);
        assert(s.value(x.var()) != value_free && not State::open(x, xs));
        if (auto lev = s.level(x.var()); s.isTrue(x)) {
            xs |= trueValue(x);
            if (type == cautious && lev > root) {
                xs |= State::openMask(x);
            }
        }
        else if (type == brave && lev > root) {
            xs |= State::openMask(x);
        }
        if (State::open(x, xs)) {
            *j++ = x;
        }
        state_->set(x, xs);
    }
    truncateVec(open_, j);
}

// Updates state with the current model (implicitly stored in s).
// PRE: initEstimate() has been called.
// Cautious: Est = Est \cap (M \ F);  Def = Def \cup F.
// Brave   : Def = Def \cup M; Est = Est \ (M \cup all fixed false literals).
void CBConsequences::QueryFinder::updateEstimate(const Solver& s) {
    assert(state_->hasModel());
    const auto type = state_->type();
    auto       root = s.level(query_.var());
    auto       j    = open_.begin();
    for (auto x : open_) {
        if (auto xs = state_->get(x); State::open(x, xs)) {
            assert(s.value(x.var()) != value_free && not State::open(~x, xs));
            auto lev    = s.level(x.var());
            auto fix    = lev < root;
            auto defVal = type == cautious ? falseValue(x) : trueValue(x);
            if (auto isDef = s.value(x.var()) == defVal; isDef || fix) {
                if (type == cautious) {
                    // Definite answer - either false and therefore not cautious consequence or strictly true
                    // NOTE: We don't need a RMW-op here since at this point ~x can't be a cautious consequence
                    xs = isDef ? value_free : trueValue(x);
                }
                else {
                    // Definite answer - either true and therefore a brave consequence or strictly false
                    // NOTE: ~x's bits are final once x is open, so a plain load/store suffices
                    xs &= 3u; // clear open state
                    xs |= isDef ? trueValue(x) : value_free;
                }
                state_->set(x, xs);
            }
            else {
                *j++ = x; // still open
            }
        }
    }
    truncateVec(open_, j);
}
// Removes assigned and no longer open literals from the local candidate list and updates state accordingly.
// PRE: s.decisionLevel() == s.rootLevel()
// POST: all literals in the local candidate list are valid query candidates (unassigned and open)
bool CBConsequences::QueryFinder::simplifyOpen(const Solver& s) {
    assert(s.decisionLevel() == s.rootLevel());
    const bool brave = state_->type() == CBConsequences::brave;
    for (auto i = 0u, end = size32(open_);;) {
        for (; i != end && s.value(open_[i].var()) == value_free && state_->open(open_[i]); ++i) {}
        if (i == end) {
            return not open_.empty();
        }
        auto x  = open_[i];
        auto xs = state_->get(x);
        if (State::open(x, xs)) {
            xs -= State::openMask(x); // no longer open
            if (s.isTrue(x)) {
                xs |= trueValue(x);
                POTASSCO_ASSERT((xs & 3u) == trueValue(x) || brave, "cautious cons can't have complementary lits");
            }
            state_->set(x, xs);
        }
        POTASSCO_DEBUG_ASSERT(not s.isFalse(x) || (xs & trueValue(x)) == 0u, "false literal can't be a consequence");
        open_[i] = open_[--end];
        open_.pop_back();
    }
}
// Query produced a model.
// - cautious: query is not a consequence, reduce overestimate
// - brave   : query is a consequence, increase underestimate
void CBConsequences::QueryFinder::doCommitModel(Enumerator&, Solver& s) {
    assert(s.value(query_.var()) != value_free);
    if (not state_->hasModel()) {
        initEstimate(s);
        state_->set(lit_true, value_true);
    }
    else {
        updateEstimate(s);
    }
    assert(not state_->open(query_) && state_->hasModel());
    model_ = true;
}
// Returns the current (model) state in out.
bool CBConsequences::QueryFinder::doExtractModel(Solver&, ValueVec& out, bool) {
    if (std::exchange(model_, false)) {
        state_->getModel(out);
        return true;
    }
    return false;
}
// Query failed.
// - cautious: ~query failed, query is a cautious consequence - add to underestimate
// - brave   :  query failed, query is not a consequence - remove from overestimate
void CBConsequences::QueryFinder::doCommitUnsat(Enumerator&, Solver& s) {
    assert(s.value(query_.var()) != value_free);
    bool commit = query_ != lit_false && not disjointPath() && s.hasConflict() && not s.hasStopConflict();
    if (popQuery(s) && commit && state_->open(query_)) {
        auto x = query_ ^ (state_->type() == brave);
        assert(s.decisionLevel() == s.rootLevel() && not s.isFalse(x));
        s.force(x, this);
        simplifyOpen(s);
        model_ = true;
        assert(not state_->open(query_));
    }
    query_ = lit_false;
}
bool CBConsequences::QueryFinder::doUpdate(Solver& s) {
    if (not state_->hasModel() || s.value(query_.var()) == value_free) {
        // trivial/unexpected call to update
        return true;
    }
    model_ = false;
    if (not state_->open(query_)) {
        if (s.inSearch()) {
            // don't mess with the root level of an active search - force termination and update afterwards
            s.setStopConflict();
            return false;
        }
        // query was SAT/UNSAT or solved by other thread
        if (not popQuery(s) || (s.queueSize() && not s.propagate())) {
            query_ = lit_false;
            return false;
        }
        // select next query candidate if any
        if (simplifyOpen(s)) {
            query_ = s.heuristic()->selectRange(s, open_);
            // Cautious: solve(~query), i.e. find a witness for query not being a cautious consequence
            // Brave   : solve( query), i.e. find a witness for query being a brave consequence
            return s.pushRoot(state_->type() == cautious ? ~query_ : query_);
        }
        // nothing left to do - force termination
        return s.force(query_ = lit_false, this);
    }
    return true;
}
/////////////////////////////////////////////////////////////////////////////////////////
// CBConsequences
/////////////////////////////////////////////////////////////////////////////////////////
CBConsequences::CBConsequences(Type type, Strategy strat) : type_(type), strategy_(strat) {}

auto EnumOptions::createConsEnumerator(const EnumOptions& opts) -> EnumPtr {
    return std::make_unique<CBConsequences>(opts.enumMode == enum_brave ? CBConsequences::brave
                                                                        : CBConsequences::cautious,
                                            static_cast<ConsStrategy>(opts.consStrat));
}
CBConsequences::~CBConsequences() { setShared(nullptr); }
void CBConsequences::setShared(SharedLiterals* lits) {
    auto* prev = shared_.lock();
    shared_.store_unlock(lits);
    if (prev) {
        prev->release();
    }
}
bool CBConsequences::supportsSplitting(const SharedContext& problem) const {
    return strategy_ == EnumOptions::cons_model && Enumerator::supportsSplitting(problem);
}
int CBConsequences::unsatType() const {
    return strategy_ == EnumOptions::cons_model ? Enumerator::unsatType() : unsat_cont;
}
auto CBConsequences::doInit(SharedContext& ctx, SharedMinimizeData* m, int) -> EnumerationConstraint* {
    candidates_.clear();
    setShared(nullptr);
    POTASSCO_CHECK_PRE(strategy_ != EnumOptions::cons_query || not m || not m->optimize(),
                       "Query algorithm does not support optimization");
    // For cautious reasoning, all candidate literals start in the over-approximation?
    const auto  flagLit = type_ == cautious && strategy_ == EnumOptions::cons_model;
    const auto& out     = ctx.output;
    if (out.projectMode() == ProjectMode::output) {
        for (const auto& pred : out.pred_range()) { addLit(ctx, pred.cond, flagLit); }
        for (auto v : out.vars_range()) { addLit(ctx, posLit(v), flagLit); }
    }
    else {
        for (auto lit : out.proj_range()) { addLit(ctx, lit, flagLit); }
    }
    for (auto& lit : candidates_) { ctx.unmark(lit.var()); }
    setIgnoreSymmetric(true);
    auto shared = ctx.concurrency() > 1;
    if (strategy_ == EnumOptions::cons_model) {
        return new ModelFinder(shared ? &shared_ : nullptr);
    }
    return new QueryFinder(type_, shared, std::move(candidates_), ctx.numVars() + 1);
}
void CBConsequences::addLit(SharedContext& ctx, Literal p, bool flag) {
    if (not ctx.marked(p) && not ctx.eliminated(p.var())) {
        candidates_.push_back(flag ? p.flag() : p.unflag());
        ctx.setFrozen(p.var(), true);
        if (not ctx.varInfo(p.var()).nant()) {
            ctx.master()->setPref(p.var(), ValueSet::def_value, type_ == cautious ? falseValue(p) : trueValue(p));
        }
        ctx.mark(p);
    }
}
} // namespace Clasp
