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
#include <clasp/model_enumerators.h>

#include <clasp/clause.h>
#include <clasp/dependency_graph.h>
#include <clasp/minimize_constraint.h>
#include <clasp/solver.h>

#include <potassco/basic_types.h>
#include <potassco/error.h>

#include <algorithm>
#include <cstdlib>

namespace Clasp {
class ModelEnumerator::ModelFinder : public EnumerationConstraint {
protected:
    ModelFinder() = default;
    [[nodiscard]] bool hasModel() const { return not solution.empty(); }
    LitVec             solution{}; // NOLINT
};
/////////////////////////////////////////////////////////////////////////////////////////
// strategy_record
/////////////////////////////////////////////////////////////////////////////////////////
class ModelEnumerator::RecordFinder final : public ModelFinder {
public:
    RecordFinder() = default;
    ConPtr clone() override { return new RecordFinder(); }
    void   doCommitModel(Enumerator&, Solver&) override;
    bool   doUpdate(Solver& s) override;
    void   addDecisionNogood(const Solver& s);
    void   addProjectNogood(const ModelEnumerator& ctx, const Solver& s, bool domain);
};

bool ModelEnumerator::RecordFinder::doUpdate(Solver& s) {
    if (hasModel()) {
        auto e   = ConstraintInfo(ConstraintType::other);
        auto ret = ClauseCreator::create(s, solution, ClauseCreator::clause_no_add, e);
        solution.clear();
        if (ret.local) {
            add(ret.local);
        }
        if (not ret.ok()) {
            return false;
        }
    }
    return true;
}
void ModelEnumerator::RecordFinder::addDecisionNogood(const Solver& s) {
    for (uint32_t x = s.decisionLevel(); x != 0; --x) {
        if (auto d = s.decision(x); not s.auxVar(d.var())) {
            solution.push_back(~d);
        }
        else if (d != s.tagLiteral()) {
            // Todo: set of vars could be reduced to those having the aux var in their reason set.
            for (auto level = s.levelLits(x); Literal lit : level.subspan(1)) {
                if (not s.auxVar(lit.var())) {
                    solution.push_back(~lit);
                }
            }
        }
    }
}
void ModelEnumerator::RecordFinder::addProjectNogood(const ModelEnumerator& ctx, const Solver& s, bool domain) {
    for (auto v : s.problemVars()) {
        if (ctx.project(v)) {
            auto p = Literal(v, s.pref(v).sign());
            if (not domain || not s.pref(v).has(ValueSet::user_value)) {
                solution.push_back(~s.trueLit(v));
            }
            else if (p != s.trueLit(v)) {
                solution.push_back(p);
            }
        }
    }
    solution.push_back(~s.sharedContext()->stepLiteral());
}
void ModelEnumerator::RecordFinder::doCommitModel(Enumerator& en, Solver& s) {
    auto& ctx = static_cast<ModelEnumerator&>(en);
    assert(solution.empty() && "Update not called!");
    solution.clear();
    if (ctx.trivial()) {
        return;
    }
    if (not ctx.projectionEnabled()) {
        addDecisionNogood(s);
    }
    else {
        addProjectNogood(ctx, s, ctx.domRec());
    }
    if (solution.empty()) {
        solution.push_back(lit_false);
    }
    if (s.sharedContext()->concurrency() > 1) {
        // parallel solving active - share solution nogood with other solvers
        std::ignore = en.commitClause(solution);
        solution.clear();
    }
}
/////////////////////////////////////////////////////////////////////////////////////////
// strategy_backtrack
/////////////////////////////////////////////////////////////////////////////////////////
class ModelEnumerator::BacktrackFinder final : public ModelFinder {
public:
    explicit BacktrackFinder(uint32_t projOpts) : opts(projOpts) {}
    // EnumerationConstraint interface
    ConPtr clone() override { return new BacktrackFinder(opts); }
    void   doCommitModel(Enumerator& ctx, Solver& s) override;
    bool   doUpdate(Solver& s) override;
    // Constraint interface
    PropResult propagate(Solver&, Literal, uint32_t&) override;
    void       reason(Solver& s, Literal p, LitVec& x) override {
        for (uint32_t i = 1, end = s.level(p.var()); i <= end; ++i) { x.push_back(s.decision(i)); }
    }
    bool simplify(Solver& s, bool reinit) override {
        for (auto& [watch, con] : projNogoods) {
            if (con && con->simplify(s, false)) {
                s.removeWatch(watch, this);
                con->destroy(&s, false);
                con = nullptr;
            }
        }
        while (not projNogoods.empty() && projNogoods.back().second == nullptr) { projNogoods.pop_back(); }
        return ModelFinder::simplify(s, reinit);
    }
    void destroy(Solver* s, bool detach) override {
        while (not projNogoods.empty()) {
            if (auto& [watch, con] = projNogoods.back(); con) {
                if (s) {
                    s->removeWatch(watch, this);
                }
                con->destroy(s, detach);
            }
            projNogoods.pop_back();
        }
        ModelFinder::destroy(s, detach);
    }
    using NogoodPair = std::pair<Literal, Constraint*>;
    using ProjectDB  = PodVector_t<NogoodPair>;
    ProjectDB projNogoods;
    uint32_t  opts;
};

Constraint::PropResult ModelEnumerator::BacktrackFinder::propagate(Solver& s, Literal, uint32_t& pos) {
    assert(pos < projNogoods.size() && projNogoods[pos].second != nullptr);
    auto* c = static_cast<ClauseHead*>(projNogoods[pos].second);
    if (not c->locked(s)) {
        c->destroy(&s, true);
        projNogoods[pos].second = (c = nullptr);
        while (not projNogoods.empty() && not projNogoods.back().second) { projNogoods.pop_back(); }
    }
    return PropResult(true, c != nullptr);
}
bool ModelEnumerator::BacktrackFinder::doUpdate(Solver& s) {
    if (hasModel()) {
        bool     ok = true;
        uint32_t sp = Potassco::test_any(opts, project_save_progress) ? Solver::undo_save_phases : Solver::undo_default;
        s.undoUntil(s.backtrackLevel(), sp | Solver::undo_pop_bt_level);
        auto rep = ClauseCreator::prepare(s, solution, {}, ConstraintType::conflict);
        if (rep.size == 0 || s.isFalse(rep.lits[0])) { // The decision stack is already ordered.
            ok = s.backtrack();
        }
        else if (rep.size == 1 || s.isFalse(rep.lits[1])) { // The projection nogood is unit. Force the single remaining
                                                            // literal from the current DL.
            ok = s.force(rep.lits[0], this);
        }
        else if (not s.isTrue(rep.lits[0])) { // Shorten the projection nogood by assuming one of its literals to false.
            auto f =
                std::stable_partition(rep.lits + 2, rep.lits + rep.size, [&](Literal x) { return not s.isFalse(x); }) -
                rep.lits;

            auto  x = (opts & project_use_heuristic) != 0 ? s.heuristic()->selectRange(s, {rep.lits, rep.lits + f})
                                                          : rep.lits[0];
            auto* c = Clause::newContractedClause(s, rep, static_cast<uint32_t>(f), true);
            POTASSCO_CHECK_PRE(c, "Invalid constraint!");
            s.assume(~x);
            // Remember that we must backtrack the current decision
            // level in order to guarantee a different projected solution.
            s.setBacktrackLevel(s.decisionLevel(), Solver::undo_pop_proj_level);
            // Attach nogood to the current decision literal.
            // Once we backtrack to x, the then obsolete nogood is destroyed
            // keeping the number of projection nogoods linear in the number of (projection) atoms.
            s.addWatch(x, this, size32(projNogoods));
            projNogoods.push_back(NogoodPair(x, c));
            ok = true;
        }
        solution.clear();
        return ok;
    }
    if (optimize() || s.sharedContext()->concurrency() == 1 || disjointPath()) {
        return true;
    }
    s.setStopConflict();
    return false;
}

void ModelEnumerator::BacktrackFinder::doCommitModel(Enumerator& ctx, Solver& s) {
    auto&    en = static_cast<ModelEnumerator&>(ctx);
    uint32_t dl = s.decisionLevel();
    solution.assign(1, dl ? ~s.decision(dl) : lit_false);
    if (en.projectionEnabled()) {
        // Remember the current projected assignment as a nogood.
        solution.clear();
        for (auto v : s.problemVars()) {
            if (en.project(v)) {
                solution.push_back(~s.trueLit(v));
            }
        }
        // Tag solution
        solution.push_back(~s.sharedContext()->stepLiteral());
        // Remember initial decisions that are projection vars.
        for (dl = s.rootLevel(); dl < s.decisionLevel(); ++dl) {
            if (not en.project(s.decision(dl + 1).var())) {
                break;
            }
        }
        s.setBacktrackLevel(dl, Solver::undo_pop_proj_level);
    }
    else {
        s.setBacktrackLevel(dl);
    }
}
/////////////////////////////////////////////////////////////////////////////////////////
// class ModelEnumerator
/////////////////////////////////////////////////////////////////////////////////////////
ModelEnumerator::ModelEnumerator(Strategy st) { setStrategy(st); }

Enumerator* EnumOptions::createModelEnumerator(const EnumOptions& opts) {
    auto* e = new ModelEnumerator();
    auto  s = ModelEnumerator::strategy_auto;
    if (opts.enumMode && opts.models()) {
        s = opts.enumMode == enum_bt ? ModelEnumerator::strategy_backtrack : ModelEnumerator::strategy_record;
    }
    e->setStrategy(s, opts.project | (opts.enumMode == enum_dom_record ? ModelEnumerator::project_dom_lits : 0));
    return e;
}

ModelEnumerator::~ModelEnumerator() = default;

void ModelEnumerator::setStrategy(Strategy st, uint32_t projection, char filter) {
    opts_.algo = st;
    opts_.proj = projection;
    filter_    = filter;
    if (Potassco::test_any(projection, 7u)) {
        opts_.proj |= static_cast<uint32_t>(project_enable_simple);
    }
    saved_ = opts_;
}

EnumerationConstraint* ModelEnumerator::doInit(SharedContext& ctx, SharedMinimizeData* opt, int numModels) {
    opts_ = saved_;
    initProjection(ctx);
    if (ctx.concurrency() > 1 && not ModelEnumerator::supportsParallel()) {
        opts_.algo = strategy_auto;
    }
    bool optOne  = opt && opt->mode() == MinimizeMode::optimize;
    bool trivial = (optOne && not domRec()) || std::abs(numModels) == 1;
    if (optOne && projectionEnabled()) {
        for (const auto& [lit, _] : *minimizer()) {
            if (trivial = trivial && project(lit.var()); not trivial) {
                break;
            }
        }
        if (not trivial) {
            ctx.warn("Projection: Optimization may depend on enumeration order.");
        }
    }
    if (opts_.algo == strategy_auto) {
        opts_.algo = trivial || (projectionEnabled() && ctx.concurrency() > 1) ? strategy_record : strategy_backtrack;
    }
    trivial_ = trivial;
    auto* c  = opts_.algo == strategy_backtrack ? static_cast<ConPtr>(new BacktrackFinder(projectOpts()))
                                                : static_cast<ConPtr>(new RecordFinder());
    if (projectionEnabled()) {
        setIgnoreSymmetric(true);
    }
    return c;
}

void ModelEnumerator::initProjection(SharedContext& ctx) {
    project_.clear();
    if (domRec() && initDomRec(ctx)) {
        return;
    }
    if (projectionEnabled()) {
        if (const auto& out = ctx.output; out.projectMode() == ProjectMode::output) {
            // Mark all relevant output variables.
            for (const auto& p : out.pred_range()) {
                if (*p.name.c_str() != filter_) {
                    addProject(ctx, p.cond.var());
                }
            }
            for (auto v : out.vars_range()) { addProject(ctx, v); }
        }
        else {
            // Mark explicitly requested variables only.
            for (auto lit : out.proj_range()) { addProject(ctx, lit.var()); }
        }
    }
}
bool ModelEnumerator::initDomRec(SharedContext& ctx) {
    const auto& p   = ctx.configuration()->solver(0);
    const auto& dom = ctx.heuristic;
    const auto& s   = *ctx.master();
    if (auto assume = dom.assume ? std::span(*dom.assume) : std::span<Literal>(); p.heuId == HeuristicType::domain) {
        for (auto lit : assume) { ctx.mark(lit); }
        DomainTable pref;
        for (const auto& d : dom) {
            if ((d.comp() || d.type() == DomModType::level) && (s.isTrue(d.cond()) || ctx.marked(d.cond()))) {
                pref.add(d.var(), d.type(), d.bias(), d.prio(), lit_true);
            }
        }
        pref.simplify();
        for (const auto& d : pref) {
            if (d.bias() > 0) {
                addProject(ctx, d.var());
            }
        }
        for (auto lit : assume) { ctx.unmark(lit.var()); }
        if ((p.heuristic.domMod & HeuParams::mod_level) != 0u) {
            DomainTable::applyDefault(
                ctx, [&](Literal lit, auto, auto) { addProject(ctx, lit.var()); }, p.heuristic.domPref);
        }
    }
    if (project_.empty()) {
        ctx.warn("domRec ignored: No domain atoms found.");
        opts_.proj -= project_dom_lits;
        return false;
    }
    if (ctx.concurrency() > 1) {
        for (auto i : irange(1u, ctx.concurrency())) {
            const SolverParams pi = ctx.configuration()->solver(i);
            if (pi.heuId != p.heuId || pi.heuristic.domMod != p.heuristic.domMod ||
                (pi.heuristic.domPref && pi.heuristic.domPref != p.heuristic.domPref)) {
                ctx.warn("domRec: Inconsistent domain heuristics, results undefined.");
                break;
            }
        }
    }
    return true;
}

void ModelEnumerator::addProject(SharedContext& ctx, Var_t v) {
    project_.add(v);
    ctx.setFrozen(v, true);
}
bool ModelEnumerator::project(Var_t v) const { return project_.contains(v); }

} // namespace Clasp
