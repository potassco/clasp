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
#include <clasp/enumerator.h>

#include <clasp/clause.h>
#include <clasp/solver.h>
#include <clasp/util/multi_queue.h>

#include <potassco/error.h>

namespace Clasp {
auto Model::numConsequences(const OutputTable& out) const -> std::pair<uint32_t, uint32_t> {
    uint32_t low = 0, est = 0;
    auto     count = [&](Literal p) {
        auto c  = isCons(p);
        low    += c == value_true;
        est    += c == value_free;
    };
    if (out.projectMode() == ProjectMode::output) {
        low += out.numFacts();
        for (const auto& pred : out.pred_range()) { count(pred.cond); }
        for (auto v : out.vars_range()) { count(posLit(v)); }
    }
    else {
        for (auto lit : out.proj_range()) { count(lit); }
    }
    assert(est == 0 || not def);
    return {low, def ? 0 : est};
}
auto Model::numConsequences(const SharedContext& problem) const -> std::pair<uint32_t, uint32_t> {
    return numConsequences(problem.output);
}
/////////////////////////////////////////////////////////////////////////////////////////
// Enumerator - Shared Queue
/////////////////////////////////////////////////////////////////////////////////////////
class Enumerator::SharedQueue {
public:
    using SharedLitsPtr = std::unique_ptr<SharedLiterals, ReleaseObject>;
    using QueueType     = mt::MultiQueue<SharedLitsPtr>;
    using IdType        = QueueType::ThreadId;

    explicit SharedQueue(uint32_t m) : queue(m) { queue.reserve(m + 1); }
    IdType addSolver() { return queue.addThread(); }
    bool   pushRelaxed(SharedLiterals* clause) {
        queue.unsafePublish(SharedLitsPtr(clause));
        return true;
    }
    SharedLiterals* pop(IdType& qId) {
        auto* x = queue.tryConsume(qId);
        return x ? (*x).get() : nullptr;
    }
    QueueType queue;
};
/////////////////////////////////////////////////////////////////////////////////////////
// EnumerationConstraint
/////////////////////////////////////////////////////////////////////////////////////////
struct EnumerationConstraint::QueueReader {
    explicit QueueReader(QueuePtr q) : queue(q), id(q->addSolver()) {}
    SharedLiterals*                 pop() { return queue->pop(id); }
    QueuePtr                        queue;
    Enumerator::SharedQueue::IdType id;
};
EnumerationConstraint::EnumerationConstraint()  = default;
EnumerationConstraint::~EnumerationConstraint() = default;
void EnumerationConstraint::init(Solver& s, SharedMinimizeData* m, QueuePtr p) {
    mini_      = nullptr;
    queue_     = p ? std::make_unique<QueueReader>(p) : nullptr;
    heuristic_ = 0;
    if (m) {
        OptParams opt = s.sharedContext()->configuration()->solver(s.id()).opt;
        mini_         = m->attach(s, opt);
        if (optimize()) {
            if (opt.type != OptParams::type_bb) {
                s.strategies().resetOnModel = 1;
            }
            else {
                heuristic_ |= 1;
            }
        }
        if (opt.hasOption(OptParams::heu_sign)) {
            for (const auto& wl : *m) { s.setPref(wl.lit.var(), ValueSet::pref_value, falseValue(wl.lit)); }
        }
        if (opt.hasOption(OptParams::heu_model)) {
            heuristic_ |= 2;
        }
    }
}
bool EnumerationConstraint::valid(Solver& s) { return not optimize() || mini_->valid(s); }
void EnumerationConstraint::add(Constraint* c) {
    if (c) {
        nogoods_.push_back(c);
    }
}
bool        EnumerationConstraint::integrateBound(Solver& s) { return not mini_ || mini_->integrate(s); }
bool        EnumerationConstraint::optimize() const { return mini_ && mini_->shared()->optimize(); }
void        EnumerationConstraint::setDisjoint(bool x) { disjoint_ = x; }
Constraint* EnumerationConstraint::cloneAttach(Solver& s) {
    EnumerationConstraint* c = clone();
    POTASSCO_CHECK_PRE(c != nullptr, "Cloning not supported by Enumerator");
    auto sharedQ = queue_ ? queue_->queue : nullptr;
    c->init(s, mini_ ? const_cast<SharedMinimizeData*>(mini_->shared()) : nullptr, sharedQ);
    return c;
}
void EnumerationConstraint::end(Solver& s) {
    if (mini_) {
        mini_->relax(s, disjointPath());
    }
    state_ = value_free;
    setDisjoint(false);
    next_.clear();
    if (s.rootLevel() > root_) {
        s.popRootLevel(s.rootLevel() - root_);
    }
}
bool EnumerationConstraint::start(Solver& s, LitView path, bool disjoint) {
    state_ = value_free;
    root_  = s.rootLevel();
    setDisjoint(disjoint);
    if (s.pushRoot(path, true)) {
        integrateBound(s);
        integrateNogoods(s);
        return true;
    }
    return false;
}
bool EnumerationConstraint::update(Solver& s) {
    auto st = state();
    if (st == value_true) {
        if (s.restartOnModel()) {
            s.undoUntil(0);
        }
        if (optimize()) {
            s.strengthenConditional();
        }
    }
    else if (st == value_false && not s.pushRoot(next_)) {
        if (not s.hasConflict()) {
            s.setStopConflict();
        }
        return false;
    }
    state_ = value_free;
    next_.clear();
    do {
        if (not s.hasConflict() && doUpdate(s) && integrateBound(s) && integrateNogoods(s)) {
            if (st == value_true) {
                modelHeuristic(s);
            }
            return true;
        }
    } while (st != value_free && s.hasConflict() && s.resolveConflict());
    return false;
}
bool EnumerationConstraint::integrateNogoods(Solver& s) {
    if (not queue_ || s.hasConflict()) {
        return not s.hasConflict();
    }
    constexpr auto f = ClauseCreator::clause_no_add | ClauseCreator::clause_no_release | ClauseCreator::clause_explicit;
    while (SharedLiterals* clause = queue_->pop()) {
        ClauseCreator::Result res = ClauseCreator::integrate(s, clause, f);
        if (res.local) {
            add(res.local);
        }
        if (not res.ok()) {
            return false;
        }
    }
    return true;
}
void EnumerationConstraint::destroy(Solver* s, bool x) {
    if (mini_) {
        mini_->destroy(s, x);
        mini_ = nullptr;
    }
    queue_ = nullptr;
    destroyDB(nogoods_, s, x);
    Constraint::destroy(s, x);
}
bool EnumerationConstraint::simplify(Solver& s, bool reinit) {
    if (mini_) {
        mini_->simplify(s, reinit);
    }
    simplifyDB(s, nogoods_, reinit);
    return false;
}

bool EnumerationConstraint::commitModel(Enumerator& ctx, Solver& s) {
    if (mini_ && not mini_->handleModel(s)) {
        return false;
    }
    if (not ctx.tentative()) {
        doCommitModel(ctx, s);
    }
    POTASSCO_ASSERT(state_ != value_false);
    state_ = value_true;
    return true;
}
bool EnumerationConstraint::extractModel(Solver& s, ValueVec& out) {
    return doExtractModel(s, out, state() == value_true);
}
bool EnumerationConstraint::doExtractModel(Solver&, ValueVec&, bool) { return false; }
bool EnumerationConstraint::commitUnsat(Enumerator& ctx, Solver& s) {
    next_.clear();
    POTASSCO_ASSERT(state_ != value_true);
    state_ = value_false;
    if (mini_) {
        mini_->handleUnsat(s, not disjointPath(), next_);
    }
    if (not ctx.tentative()) {
        doCommitUnsat(ctx, s);
    }
    return not s.hasConflict() || s.decisionLevel() != s.rootLevel();
}
void EnumerationConstraint::modelHeuristic(Solver& s) {
    const bool full      = heuristic_ > 1;
    const bool heuristic = full || (heuristic_ == 1 && s.queueSize() == 0 && s.decisionLevel() == s.rootLevel());
    if (optimize() && heuristic && s.propagate()) {
        for (const auto& [lit, _] : *mini_->shared()) {
            if (s.value(lit.var()) == value_free) {
                s.assume(~lit);
                if (not full || not s.propagate()) {
                    break;
                }
            }
        }
    }
}
/////////////////////////////////////////////////////////////////////////////////////////
// Enumerator
/////////////////////////////////////////////////////////////////////////////////////////
static auto enumCon(const Solver& s) -> EnumerationConstraint& {
    auto* c = static_cast<EnumerationConstraint*>(s.enumerationConstraint()); // NOLINT(*-pro-type-static-cast-downcast)
    POTASSCO_CHECK_PRE(c, "Solver not attached");
    return *c;
}
Enumerator::Enumerator()  = default;
Enumerator::~Enumerator() = default;
void Enumerator::setDisjoint(Solver& s, bool b) const { enumCon(s).setDisjoint(b); }
void Enumerator::setIgnoreSymmetric(bool b) { model_.sym = static_cast<uint32_t>(b == false); }
void Enumerator::clearUpdate() { model_.up = 0; }
void Enumerator::end(Solver& s) const { enumCon(s).end(s); }
void Enumerator::doReset() {}
void Enumerator::reset() {
    mini_ = nullptr;
    queue_.reset();
    model_      = {};
    model_.ctx  = this;
    model_.sym  = 1;
    model_.type = static_cast<uint32_t>(modelType());
    model_.sId  = 0;
    doReset();
}
int Enumerator::init(SharedContext& ctx, OptMode opt, int limit) {
    ctx.master()->setEnumerationConstraint(nullptr);
    reset();
    if (opt != MinimizeMode::ignore) {
        mini_ = ctx.minimize();
    }
    limit = limit >= 0 ? limit : 1 - static_cast<int>(exhaustive());
    if (limit != 1) {
        ctx.setPreserveModels(true);
    }
    queue_  = std::make_unique<SharedQueue>(ctx.concurrency());
    auto* c = doInit(ctx, mini_, limit);
    if (tentative()) {
        model_.type = Model::sat;
    }
    else if (model_.consequences() && optimize()) {
        ctx.warn("Optimization: Consequences may depend on enumeration order.");
    }
    c->init(*ctx.master(), mini_, queue_.get());
    ctx.master()->setEnumerationConstraint(c);
    return limit;
}
LowerBound Enumerator::lowerBound() const { return optimize() ? mini_->lowerBound() : LowerBound{}; }
bool       Enumerator::start(Solver& s, LitView path, bool disjointPath) const {
    return enumCon(s).start(s, path, disjointPath);
}
Val_t Enumerator::commit(Solver& s) {
    if (s.hasConflict() && s.decisionLevel() == s.rootLevel()) {
        return commitUnsat(s) ? value_free : value_false;
    }
    if (s.numFreeVars() == 0 && s.queueSize() == 0 && not s.hasConflict()) {
        return commitModel(s) ? value_true : value_free;
    }
    return value_free;
}
bool Enumerator::commitModel(Solver& s) {
    assert(s.numFreeVars() == 0 && not s.hasConflict() && s.queueSize() == 0);
    if (enumCon(s).commitModel(*this, s)) {
        s.stats.addModel(s.decisionLevel());
        if (model_.fin) {
            model_.num  = 0;
            model_.type = static_cast<uint32_t>(modelType());
            model_.fin  = 0;
        }
        if (model_.type == Model::sat) {
            s.values(values_);
        }
        else {
            enumCon(s).extractModel(s, values_);
        }
        ++model_.num;
        model_.sId    = s.id();
        model_.values = values_;
        model_.costs  = {};
        sym_.clear();
        if (minimizer()) {
            costs_.resize(minimizer()->numRules());
            std::transform(minimizer()->adjust(), minimizer()->adjust() + costs_.size(), minimizer()->sum(),
                           costs_.begin(), std::plus{});
            model_.costs = costs_;
        }
        if (model_.sym && not optimize() && s.satPrepro()) {
            s.satPrepro()->extendModel(values_, sym_);
        }
        return true;
    }
    return false;
}
bool Enumerator::hasSymmetric(const Solver& s) const { return not sym_.empty() && s.satPrepro(); }
bool Enumerator::commitSymmetric(Solver& s) {
    if (hasSymmetric(s)) {
        s.satPrepro()->extendModel(values_, sym_);
        s.stats.addModel(s.decisionLevel());
        ++model_.num;
        return true;
    }
    return false;
}
bool Enumerator::commitUnsat(Solver& s) {
    auto& c  = enumCon(s);
    bool  ok = c.commitUnsat(*this, s);
    if (ok && not model_.values.empty() && model_.type != Model::sat && c.extractModel(s, values_)) {
        model_.up = 1;
    }
    sym_.clear();
    return ok;
}
bool Enumerator::commitClause(LitView clause) const {
    return queue_ && queue_->pushRelaxed(SharedLiterals::newShareable(clause, ConstraintType::other));
}
bool Enumerator::commitComplete() {
    if (enumerated()) {
        model_.fin = 1;
        if (tentative()) {
            mini_->markOptimal();
            model_.opt = 1;
            return false;
        }
        model_.opt |= static_cast<uint32_t>(optimize());
        model_.def |= static_cast<uint32_t>(model_.consequences());
    }
    return true;
}
bool Enumerator::update(Solver& s) const { return enumCon(s).update(s); }
bool Enumerator::supportsSplitting(const SharedContext& ctx) const {
    if (not optimize()) {
        return true;
    }
    const auto* config = ctx.configuration();
    return std::ranges::all_of(irange(ctx.concurrency()), [&](auto idx) {
        if (const Solver* s = ctx.hasSolver(idx) ? ctx.solver(idx) : nullptr; s && s->enumerationConstraint()) {
            return enumCon(*s).minimizer()->supportsSplitting();
        }
        return not config || idx >= config->numSolver() || config->solver(idx).opt.supportsSplitting();
    });
}
int Enumerator::unsatType() const { return not optimize() ? unsat_stop : unsat_cont; }
/////////////////////////////////////////////////////////////////////////////////////////
// EnumOptions
/////////////////////////////////////////////////////////////////////////////////////////
Enumerator* EnumOptions::createEnumerator(const EnumOptions& opts) {
    if (opts.models()) {
        return createModelEnumerator(opts);
    }
    if (opts.consequences()) {
        return createConsEnumerator(opts);
    }
    return nullEnumerator();
}
Enumerator* EnumOptions::nullEnumerator() {
    struct NullEnum : Enumerator {
        ConPtr doInit(SharedContext&, SharedMinimizeData*, int) override {
            struct NullCon : EnumerationConstraint {
                NullCon() = default;
                ConPtr clone() override { return new NullCon(); }
                bool   doUpdate(Solver&) override { return true; }
            };
            return new NullCon();
        }
    };
    return new NullEnum;
}

const char* modelType(const Model& m) {
    switch (m.type) {
        case Model::sat     : return "Model";
        case Model::brave   : return "Brave";
        case Model::cautious: return "Cautious";
        case Model::user    : return "User";
        default             : return nullptr;
    }
}

} // namespace Clasp
