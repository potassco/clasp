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
// CBConsequences::SharedConstraint
/////////////////////////////////////////////////////////////////////////////////////////
class CBConsequences::SharedConstraint {
public:
    SharedConstraint() = default;
    ~SharedConstraint() { release(nullptr); }
    SharedLiterals* fetch_if_neq(const SharedLiterals* last) {
        auto* val = current.lock();
        auto* ret = val && val != last ? val->share() : nullptr;
        current.store_unlock(val);
        return ret;
    }
    void release(SharedLiterals* newLits) {
        auto* prev = current.lock();
        current.store_unlock(newLits);
        if (prev) {
            prev->release();
        }
    }
    LockedValue<SharedLiterals*> current;
};
/////////////////////////////////////////////////////////////////////////////////////////
// CBConsequences::CBFinder
/////////////////////////////////////////////////////////////////////////////////////////
class CBConsequences::CBFinder : public EnumerationConstraint {
public:
    using SharedCon    = SharedConstraint;
    using ConstraintDB = Solver::ConstraintDB;
    using SharedLits   = SharedLiterals;
    explicit CBFinder(SharedCon* sh) : shared(sh) {}
    ConPtr clone() override { return new CBFinder(shared); }
    void   doCommitModel(Enumerator& ctx, Solver& s) override {
        static_cast<CBConsequences&>(ctx).addCurrent(s, current, lastM, rootLevel());
    }
    bool doExtractModel(Solver&, ValueVec& out, bool sat) override {
        if (sat && not lastM.empty()) {
            out = std::move(lastM);
            return true;
        }
        return false;
    }
    void         destroy(Solver* s, bool detach) override;
    bool         doUpdate(Solver& s) override;
    void         pushLocked(Solver& s, ClauseHead* c);
    LitVec       current;
    SharedCon*   shared;
    SharedLits*  last{nullptr};
    ConstraintDB locked;
    ValueVec     lastM;
};
/////////////////////////////////////////////////////////////////////////////////////////
// CBConsequences::QueryFinder
/////////////////////////////////////////////////////////////////////////////////////////
class CBConsequences::QueryFinder : public EnumerationConstraint {
public:
    class State {
    public:
        explicit State(uint32_t nVars) : value_(std::make_unique<ValueType[]>(nVars)), size_(nVars), refs_(1) {}
        State* share() {
            refs_.add();
            return this;
        }
        void release() {
            if (refs_.release()) {
                delete this;
            }
        }
        [[nodiscard]] uint32_t size() const { return size_; }
        [[nodiscard]] bool     open(Literal p) const {
            return Potassco::test_any(value_[p.var()].load(), Model::estMask(p));
        }
        void setModel(ValueVec& m) { m.assign(value_.get(), value_.get() + size_); }
        void push(Literal p) { value_[p.var()].store(Model::estMask(p) | trueValue(p)); }
        void pop(Literal p) { value_[p.var()].store(value_free); }
        void fix(Literal p) { value_[p.var()].store(trueValue(p)); }

    private:
        using ValueType = mt::ThreadSafe<Val_t>;
        using ValueVec  = std::unique_ptr<ValueType[]>;
        ValueVec value_;
        uint32_t size_;
        RefCount refs_;
    };
    explicit QueryFinder(LitVec c, uint32_t nVars) : open(std::move(c)), state(new State(nVars)), query(lit_false) {
        state->push(query); // start with true as initial query
    }
    explicit QueryFinder(LitVec c, State* st) : open(std::move(c)), state(st), query(lit_false) {}
    ~QueryFinder() override { state->release(); }
    ConPtr clone() override { return new QueryFinder(open, state->share()); }
    bool   doUpdate(Solver& s) override;
    void   doCommitModel(Enumerator&, Solver&) override;
    void   doCommitUnsat(Enumerator&, Solver&) override;
    bool   doExtractModel(Solver& s, ValueVec& out, bool sat) override;
    void   initUpper(const Solver& s);
    void   updateUpper(const Solver& s, uint32_t root);
    void   updateOpen(const Solver& s);
    bool   addQuery(Solver& s);
    void   reason(Solver& s, Literal p, LitVec& out) override {
        for (uint32_t i = 1, end = s.level(p.var()); i <= end; ++i) {
            if (Literal q = s.decision(i); q != p) {
                out.push_back(q);
            }
        }
    }
    bool popQuery(Solver& s) { // NOLINT(readability-make-member-function-const)
        if (s.isFalse(query) && query != lit_false) {
            auto diff = s.rootLevel() - s.level(query.var());
            return s.popRootLevel(diff + 1);
        }
        return s.popRootLevel(0);
    }
    LitVec  open;
    State*  state;
    Literal query;
    bool    model = false;
};
// Init overestimate to current model stored in s.
void CBConsequences::QueryFinder::initUpper(const Solver& s) {
    auto j = open.begin();
    for (auto x : open) {
        if (s.isTrue(x)) {
            if (s.level(x.var())) {
                state->push(*j++ = x);
            }
            else {
                state->fix(x);
            }
        }
    }
    open.erase(j, open.end());
}
// Reduce the overestimate by computing c = c \cap M, where M is the current model stored in s.
void CBConsequences::QueryFinder::updateUpper(const Solver& s, uint32_t root) {
    auto j = open.begin();
    for (auto x : open) {
        if (state->open(x)) {
            if (not s.isTrue(x)) {
                state->pop(x);
            }
            else if (s.level(x.var()) < root) {
                state->fix(x);
            }
            else {
                *j++ = x;
            }
        }
    }
    open.erase(j, open.end());
}
// Removes no longer open literals from estimate.
void CBConsequences::QueryFinder::updateOpen(const Solver& s) {
    assert(s.decisionLevel() == s.rootLevel());
    for (auto i = 0u, end = size32(open);;) {
        for (; i != end && s.value(open[i].var()) == value_free && state->open(open[i]); ++i) { ; }
        if (i == end) {
            break;
        }
        if (auto q = open[i]; s.isTrue(q)) {
            state->fix(q);
        }
        else if (state->open(q)) {
            state->pop(q);
        }
        open[i] = open.back();
        open.pop_back();
        --end;
    }
}
bool CBConsequences::QueryFinder::addQuery(Solver& s) {
    updateOpen(s);
    if (not open.empty()) {
        query = s.heuristic()->selectRange(s, open);
        return s.pushRoot(~query);
    }
    return s.force(query = lit_false);
}
// solve(~query) produced a model - query is not a cautious consequence, update overestimate
void CBConsequences::QueryFinder::doCommitModel(Enumerator&, Solver& s) {
    assert(s.isFalse(query));
    if (isSentinel(query)) {
        state->fix(~query);
        initUpper(s);
    }
    else {
        state->pop(query);
        updateUpper(s, s.level(query.var()));
    }
    model = true;
}
bool CBConsequences::QueryFinder::doExtractModel(Solver&, ValueVec& out, bool) {
    if (std::exchange(model, false)) {
        state->setModel(out);
        return true;
    }
    return false;
}
// solve(~query) failed - query is a cautious consequence
void CBConsequences::QueryFinder::doCommitUnsat(Enumerator&, Solver& s) {
    assert(s.isFalse(query));
    bool commit = not isSentinel(query) && not disjointPath() && s.hasConflict() && not s.hasStopConflict();
    if (popQuery(s) && commit && state->open(query)) {
        assert(s.decisionLevel() == s.rootLevel());
        state->fix(query);
        updateOpen(s);
        model = true;
    }
}
bool CBConsequences::QueryFinder::doUpdate(Solver& s) {
    model = false;
    if (not state->open(query) || s.value(query.var()) == value_free) {
        // query was SAT/UNSAT or solved by other thread
        return popQuery(s) && addQuery(s);
    }
    return true;
}
/////////////////////////////////////////////////////////////////////////////////////////
// CBConsequences
/////////////////////////////////////////////////////////////////////////////////////////
CBConsequences::CBConsequences(Type type, Algo algo) : shared_(nullptr), type_(type), algo_(algo) {
    if (type_ != cautious) {
        algo_ = def;
    }
}

Enumerator* EnumOptions::createConsEnumerator(const EnumOptions& opts) {
    return new CBConsequences(opts.enumMode == enum_brave ? CBConsequences::brave : CBConsequences::cautious,
                              opts.enumMode != enum_query ? CBConsequences::def : CBConsequences::query);
}
CBConsequences::~CBConsequences() = default;
bool CBConsequences::supportsSplitting(const SharedContext& problem) const {
    return algo_ == def && Enumerator::supportsSplitting(problem);
}
int CBConsequences::unsatType() const { return algo_ == def ? Enumerator::unsatType() : Enumerator::unsat_sync; }
EnumerationConstraint* CBConsequences::doInit(SharedContext& ctx, SharedMinimizeData* m, int) {
    cons_.clear();
    const auto& out = ctx.output;
    if (out.projectMode() == ProjectMode::output) {
        for (const auto& pred : out.pred_range()) { addLit(ctx, pred.cond); }
        for (auto v : out.vars_range()) { addLit(ctx, posLit(v)); }
    }
    else {
        for (auto lit : out.proj_range()) { addLit(ctx, lit); }
    }
    if (m && m->optimize() && algo_ == query) {
        ctx.warn("Query algorithm does not support optimization!");
        algo_ = def;
    }
    // init M to either cons or {} depending on whether we compute cautious or brave cons.
    const uint32_t fMask = (type_ == cautious && algo_ != query);
    const uint32_t vMask = (type_ == cautious) ? 3u : 0u;
    for (auto& lit : cons_) {
        lit.rep() |= fMask;
        ctx.unmark(lit.var());
        if (not ctx.varInfo(lit.var()).nant()) {
            ctx.master()->setPref(lit.var(), ValueSet::def_value, static_cast<Val_t>(trueValue(lit) ^ vMask));
        }
    }
    shared_.reset();
    setIgnoreSymmetric(true);
    if (type_ != cautious || algo_ != query) {
        shared_ = ctx.concurrency() > 1 ? std::make_unique<SharedConstraint>() : nullptr;
        return new CBFinder(shared_.get());
    }
    return new QueryFinder(cons_, ctx.numVars() + 1);
}
void CBConsequences::addLit(SharedContext& ctx, Literal p) {
    if (not ctx.marked(p) && not ctx.eliminated(p.var())) {
        cons_.push_back(p);
        ctx.setFrozen(p.var(), true);
        ctx.mark(p);
    }
}
void CBConsequences::addCurrent(const Solver& s, LitVec& con, ValueVec& m, uint32_t root) {
    con.assign(1, ~s.sharedContext()->stepLiteral());
    // reset state of variables
    m.assign(s.numVars() + 1, value_free);
    // let M be all lits p with p.watch() == true
    for (auto& p : cons_) {
        auto dl  = s.level(p.var());
        auto ost = dl > root ? Model::estMask(p) : 0u;
        if (type_ == brave) {
            // brave: extend M with true literals and force a literal not in M to true
            if (p.flagged() || s.isTrue(p)) {
                p.flag();
                ost = 0u;
            }
            else if (dl) {
                con.push_back(p);
            }
        }
        else if (type_ == cautious) {
            // cautious: intersect M with true literals and force a literal in M to false
            if (not p.flagged() || s.isFalse(p)) {
                p.unflag();
                ost = 0u;
            }
            else if (dl) {
                con.push_back(~p);
            }
        }
        // set output state
        if (p.flagged()) {
            ost |= trueValue(p);
        }
        m[p.var()] |= ost;
    }
    if (shared_) {
        shared_->release(SharedLiterals::newShareable(con, ConstraintType::other, 1));
    }
}
/////////////////////////////////////////////////////////////////////////////////////////
// CBConsequences::CBFinder implementation
/////////////////////////////////////////////////////////////////////////////////////////
void CBConsequences::CBFinder::destroy(Solver* s, bool detach) {
    Clasp::destroyDB(locked, s, detach);
    if (last) {
        last->release();
    }
    EnumerationConstraint::destroy(s, detach);
}
void CBConsequences::CBFinder::pushLocked(Solver& s, ClauseHead* c) {
    for (ClauseHead* h; not locked.empty() && not(h = static_cast<ClauseHead*>(locked.back()))->locked(s);) {
        h->destroy(&s, true);
        locked.pop_back();
    }
    locked.push_back(c);
}
bool CBConsequences::CBFinder::doUpdate(Solver& s) {
    ClauseCreator::Result ret;
    auto                  flags = ClauseCreator::clause_explicit | ClauseCreator::clause_no_add;
    lastM.clear();
    if (not shared) {
        ret = not current.empty() ? ClauseCreator::create(s, current, flags, ConstraintInfo(ConstraintType::other))
                                  : ClauseCreator::Result();
    }
    else if (SharedLiterals* x = shared->fetch_if_neq(last)) {
        if (last) {
            last->release();
        }
        last = x;
        ret  = ClauseCreator::integrate(s, x, flags | ClauseCreator::clause_no_release);
    }
    if (ret.local) {
        pushLocked(s, ret.local);
    }
    current.clear();
    return ret.ok();
}
} // namespace Clasp
