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
#include <clasp/program_builder.h>

#include <clasp/clause.h>
#include <clasp/parser.h>
#include <clasp/shared_context.h>
#include <clasp/solver.h>
#include <clasp/weight_constraint.h>

#include <potassco/error.h>

#include <limits>
#include <unordered_map>
namespace Clasp {

/////////////////////////////////////////////////////////////////////////////////////////
// class ProgramBuilder
/////////////////////////////////////////////////////////////////////////////////////////
ProgramBuilder::ProgramBuilder() : ctx_(nullptr), frozen_(true) {}
ProgramBuilder::~ProgramBuilder() = default;
bool ProgramBuilder::ok() const { return ctx_ && ctx_->ok(); }
bool ProgramBuilder::startProgram(SharedContext& ctx) {
    ctx.report(Event::subsystem_load);
    ctx_    = &ctx;
    frozen_ = ctx.frozen();
    return ctx_->ok() && doStartProgram();
}
bool ProgramBuilder::updateProgram() {
    POTASSCO_CHECK_PRE(ctx_, "startProgram() not called!");
    bool up = frozen();
    bool ok =
        ctx_->ok() && ctx_->unfreeze() && doUpdateProgram() && (ctx_->setSolveMode(SharedContext::solve_multi), true);
    frozen_ = ctx_->frozen();
    if (up && not frozen()) {
        ctx_->report(Event::subsystem_load);
    }
    return ok;
}
bool ProgramBuilder::endProgram() {
    POTASSCO_CHECK_PRE(ctx_, "startProgram() not called!");
    bool ok = ctx_->ok();
    if (ok && not frozen_) {
        ctx_->report(Event::subsystem_prepare);
        ok      = doEndProgram();
        frozen_ = true;
    }
    return ok;
}
void ProgramBuilder::getAssumptions(LitVec& out) const {
    POTASSCO_CHECK_PRE(ctx_ && frozen());
    doGetAssumptions(out);
}
void ProgramBuilder::getWeakBounds(SumVec& out) const {
    POTASSCO_CHECK_PRE(ctx_ && frozen());
    doGetWeakBounds(out);
}
ProgramParser& ProgramBuilder::parser() {
    if (not parser_) {
        parser_.reset(doCreateParser());
    }
    return *parser_;
}
bool ProgramBuilder::parseProgram(std::istream& input) {
    POTASSCO_CHECK_PRE(ctx_ && not frozen());
    ProgramParser& p = parser();
    POTASSCO_CHECK_PRE(p.accept(input), "unrecognized input format");
    return p.parse();
}
void ProgramBuilder::addMinLit(Weight_t prio, WeightLiteral x) { ctx_->addMinimize(x, prio); }
void ProgramBuilder::markOutputVariables() const {
    const OutputTable& out = ctx_->output;
    for (auto v : out.vars_range()) { ctx_->setOutput(v, true); }
    for (const auto& pred : out.pred_range()) { ctx_->setOutput(pred.cond.var(), true); }
}
void ProgramBuilder::doGetWeakBounds(SumVec&) const {}
/////////////////////////////////////////////////////////////////////////////////////////
// class SatBuilder
/////////////////////////////////////////////////////////////////////////////////////////
bool SatBuilder::markAssigned() {
    if (pos_ == ctx()->master()->numAssignedVars()) {
        return true;
    }
    bool ok = ctx()->ok() && ctx()->master()->propagate();
    for (auto lit : ctx()->master()->trailView(pos_)) {
        markLit(~lit);
        ++pos_;
    }
    return ok;
}
void SatBuilder::prepareProblem(uint32_t numVars, Wsum_t cw, uint32_t clauseHint) {
    POTASSCO_CHECK_PRE(ctx(), "startProgram() not called!");
    auto start = ctx()->addVars(numVars, VarType::atom, VarInfo::flag_input | VarInfo::flag_nant);
    ctx()->output.setVarRange(Range32(start, start + numVars));
    ctx()->startAddConstraints(std::min(clauseHint, 10000u));
    varState_.resize(start + numVars);
    vars_       = ctx()->numVars();
    hardWeight_ = cw;
    markAssigned();
}
bool SatBuilder::addObjective(WeightLitView min) {
    for (const auto& lit : min) {
        addMinLit(0, lit);
        markOcc(~lit.lit);
    }
    return ctx()->ok();
}
void SatBuilder::addProject(Var_t v) { ctx()->output.addProject(posLit(v)); }
void SatBuilder::addAssumption(Literal x) {
    assume_.push_back(x);
    markOcc(x);
    ctx()->setFrozen(x.var(), true);
}
bool SatBuilder::addClause(LitVec& clause, Wsum_t cw) {
    if (not ctx()->ok() || satisfied(clause)) {
        return ctx()->ok();
    }
    POTASSCO_CHECK_PRE(cw >= 0 && (cw <= std::numeric_limits<Weight_t>::max() || cw == hardWeight_),
                       "Clause weight out of bounds");
    if (cw == hardWeight_) {
        return ClauseCreator::create(*ctx()->master(), clause, {}, ConstraintType::static_).ok() && markAssigned();
    }
    // Store weight, relaxation var, and (optionally) clause
    softClauses_.push_back(Literal::fromRep(static_cast<uint32_t>(cw)));
    if (clause.size() > 1) {
        softClauses_.push_back(posLit(++vars_));
        softClauses_.insert(softClauses_.end(), clause.begin(), clause.end());
    }
    else if (not clause.empty()) {
        softClauses_.push_back(~clause.back());
    }
    else {
        softClauses_.push_back(lit_true);
    }
    softClauses_.back().flag(); // mark end of clause
    return true;
}
bool SatBuilder::satisfied(LitVec& cc) {
    bool sat = false;
    auto j   = cc.begin();
    for (auto x : cc) {
        auto m = trueValue(x);
        if (auto p = varState_[x.var()] & 3u; p == 0) {
            varState_[x.var()] |= m;
            x.unflag();
            *j++ = x;
        }
        else if (p != m) {
            sat = true;
            break;
        }
    }
    cc.erase(j, cc.end());
    for (auto x : cc) {
        Potassco::store_clear_mask(varState_[x.var()], 3u);
        if (not sat) {
            markOcc(x);
        }
    }
    return sat;
}
bool SatBuilder::addConstraint(WeightLitVec& lits, Weight_t bound) {
    if (not ctx()->ok()) {
        return false;
    }
    auto rep = WeightLitsRep::create(*ctx()->master(), lits, bound);
    if (rep.open()) {
        for (const auto& [lit, _] : rep.literals()) { markOcc(lit); }
    }
    return WeightConstraint::create(*ctx()->master(), lit_true, rep, {}).ok();
}
bool SatBuilder::doStartProgram() {
    vars_ = ctx()->numVars();
    pos_  = 0;
    assume_.clear();
    return markAssigned();
}
ProgramParser* SatBuilder::doCreateParser() { return new SatParser(*this); }
bool           SatBuilder::doEndProgram() {
    bool ok = ctx()->ok();
    if (not softClauses_.empty() && ok) {
        ctx()->setPreserveModels(true);
        uint32_t softVars = vars_ - ctx()->numVars();
        ctx()->addVars(softVars, VarType::atom, VarInfo::flag_nant);
        ctx()->startAddConstraints();
        LitVec cc;
        for (auto it = softClauses_.begin(), end = softClauses_.end(); it != end && ok; ++it) {
            auto    w     = static_cast<Weight_t>(it->rep());
            Literal relax = *++it;
            if (not relax.flagged()) {
                cc.assign(1, relax);
                do { cc.push_back(*++it); } while (not cc.back().flagged());
                cc.back().unflag();
                ok = ClauseCreator::create(*ctx()->master(), cc, {}, ConstraintType::static_).ok();
            }
            addMinLit(0, WeightLiteral{relax.unflag(), w});
        }
        discardVec(softClauses_);
    }
    if (ok) {
        constexpr uint32_t seen = 12;
        const bool         elim = not ctx()->preserveModels();
        for (auto v : irange(1u, size32(varState_))) {
            if (uint32_t m = varState_[v]; not Potassco::test_mask(m, seen)) {
                if (m) {
                    ctx()->setNant(v, false);
                    ctx()->master()->setPref(v, ValueSet::def_value, static_cast<Val_t>(m >> 2));
                }
                else if (elim) {
                    ctx()->eliminate(v);
                }
            }
        }
        markOutputVariables();
    }
    return ok;
}
/////////////////////////////////////////////////////////////////////////////////////////
// class PBBuilder
/////////////////////////////////////////////////////////////////////////////////////////
struct PBBuilder::ProductIndex : std::unordered_map<PKey, Literal, PKey, PKey> {};

PBBuilder::PBBuilder() : products_(std::make_unique<ProductIndex>()) {}
PBBuilder::~PBBuilder() = default;
void PBBuilder::prepareProblem(uint32_t numVars, uint32_t numProd, uint32_t numSoft, uint32_t numCons) {
    POTASSCO_CHECK_PRE(ctx(), "startProgram() not called!");
    auto out = ctx()->addVars(numVars, VarType::atom, VarInfo::flag_nant | VarInfo::flag_input);
    auxVar_  = ctx()->addVars(numProd + numSoft, VarType::atom, VarInfo::flag_nant);
    endVar_  = auxVar_ + numProd + numSoft;
    ctx()->output.setVarRange(Range32(out, out + numVars));
    ctx()->startAddConstraints(numCons);
}
uint32_t PBBuilder::nextAuxVar() {
    POTASSCO_CHECK_PRE(ctx()->validVar(auxVar_), "Variables out of bounds");
    return auxVar_++;
}
bool PBBuilder::addConstraint(WeightLitVec& lits, Weight_t bound, bool eq, Weight_t cw) {
    if (not ctx()->ok()) {
        return false;
    }
    Var_t eqVar = 0;
    if (cw > 0) { // soft constraint
        if (lits.size() != 1) {
            eqVar = nextAuxVar();
            addMinLit(0, WeightLiteral{negLit(eqVar), cw});
        }
        else {
            if (lits[0].weight < 0) {
                bound       += (lits[0].weight = -lits[0].weight);
                lits[0].lit  = ~lits[0].lit;
            }
            if (lits[0].weight < bound) {
                lits[0].lit = lit_false;
            }
            addMinLit(0, WeightLiteral{~lits[0].lit, cw});
            return true;
        }
    }
    return WeightConstraint::create(*ctx()->master(), posLit(eqVar), lits, bound,
                                    not eq ? WeightConstraint::CreateFlag{} : WeightConstraint::create_eq_bound)
        .ok();
}

bool PBBuilder::addObjective(WeightLitView min) {
    for (const auto& lit : min) { addMinLit(0, lit); }
    return ctx()->ok();
}
void PBBuilder::addProject(Var_t v) { ctx()->output.addProject(posLit(v)); }
void PBBuilder::addAssumption(Literal x) {
    assume_.push_back(x);
    ctx()->setFrozen(x.var(), true);
}
bool PBBuilder::setSoftBound(Wsum_t b) {
    if (b > 0) {
        soft_ = b - 1;
    }
    return true;
}

void PBBuilder::doGetWeakBounds(SumVec& out) const {
    if (soft_ != std::numeric_limits<Wsum_t>::max()) {
        if (out.empty()) {
            out.push_back(soft_);
        }
        else if (out[0] > soft_) {
            out[0] = soft_;
        }
    }
}

Literal PBBuilder::addProduct(LitVec& lits) {
    if (not ctx()->ok()) {
        return lit_false;
    }
    prod_.lits.reserve(lits.size() + 1);
    if (productSubsumed(lits, prod_)) {
        return lits[0];
    }
    Literal& eq = (*products_)[prod_];
    if (eq != lit_true) {
        return eq;
    }
    eq = posLit(nextAuxVar());
    addProductConstraints(eq, lits);
    return eq;
}
bool PBBuilder::productSubsumed(LitVec& lits, PKey& prod) {
    for (auto& s = *ctx()->master();;) {
        auto j      = lits.begin();
        auto last   = lit_true;
        auto abst   = 0u;
        auto sorted = true;
        prod.lits.assign(1, lit_true); // room for abst
        for (auto lit : lits) {
            if (s.isFalse(lit) || ~lit == last) { // product is always false
                lits.assign(1, lit_false);
                return true;
            }
            else if (last.var() > lit.var()) { // not sorted - redo with sorted product
                sorted = false;
                break;
            }
            else if (not s.isTrue(lit) && last != lit) {
                prod.lits.push_back(lit);
                abst += hashLit(lit);
                last  = lit;
                *j++  = last;
            }
        }
        if (sorted) {
            prod.lits[0].rep() = abst;
            lits.erase(j, lits.end());
            if (lits.empty()) {
                lits.assign(1, lit_true);
            }
            return lits.size() < 2;
        }
        std::ranges::sort(lits);
    }
}
void PBBuilder::addProductConstraints(Literal eqLit, LitVec& lits) {
    Solver& s = *ctx()->master();
    assert(s.value(eqLit.var()) == value_free);
    bool ok = ctx()->ok();
    for (auto it = lits.begin(), end = lits.end(); it != end && ok; ++it) {
        assert(s.value(it->var()) == value_free);
        ok  = ctx()->addBinary(~eqLit, *it);
        *it = ~*it;
    }
    lits.push_back(eqLit);
    if (ok) {
        ClauseCreator::create(s, lits, ClauseCreator::clause_no_prepare);
    }
}

bool PBBuilder::doStartProgram() {
    auxVar_ = ctx()->numVars() + 1;
    soft_   = std::numeric_limits<Wsum_t>::max();
    assume_.clear();
    return true;
}
bool PBBuilder::doEndProgram() {
    while (auxVar_ != endVar_) {
        if (not ctx()->addUnary(negLit(nextAuxVar()))) {
            return false;
        }
    }
    markOutputVariables();
    return true;
}
ProgramParser* PBBuilder::doCreateParser() { return new SatParser(*this); }
/////////////////////////////////////////////////////////////////////////////////////////
// class BasicProgramAdapter
/////////////////////////////////////////////////////////////////////////////////////////
BasicProgramAdapter::BasicProgramAdapter(ProgramBuilder& prg) : prg_(&prg), sat_(true), inc_(false) {
    sat_ = dynamic_cast<SatBuilder*>(prg_) != nullptr;
    POTASSCO_CHECK_PRE(sat_ || dynamic_cast<PBBuilder*>(prg_), "unsupported program type");
}
void BasicProgramAdapter::initProgram(bool inc) { inc_ = inc; }
void BasicProgramAdapter::beginStep() {
    if (inc_ || prg_->frozen()) {
        prg_->updateProgram();
    }
}

template <typename C>
void BasicProgramAdapter::withPrg(C&& call) const {
    // NOLINTNEXTLINE(*-pro-type-static-cast-downcast)
    sat_ ? call(static_cast<SatBuilder&>(*prg_)) : call(static_cast<PBBuilder&>(*prg_));
}

void BasicProgramAdapter::rule(Potassco::HeadType, Potassco::AtomSpan head, Potassco::LitSpan body) {
    POTASSCO_CHECK_PRE(head.empty(), "unsupported rule type");
    clause_.clear();
    constraint_.clear();
    withPrg([&]<typename P>(P& builder) {
        if constexpr (std::is_same_v<P, SatBuilder>) {
            for (auto lit : body) { clause_.push_back(~toLit(lit)); }
            builder.addClause(clause_);
        }
        else {
            for (auto lit : body) { constraint_.push_back(WeightLiteral{~toLit(lit), 1}); }
            builder.addConstraint(constraint_, 1);
        }
    });
}
void BasicProgramAdapter::rule(Potassco::HeadType, Potassco::AtomSpan head, Potassco::Weight_t bound,
                               Potassco::WeightLitSpan body) {
    POTASSCO_CHECK_PRE(head.empty(), "unsupported rule type");
    constraint_.clear();
    Wsum_t newBound = -bound + 1;
    for (const auto& [lit, weight] : body) {
        constraint_.push_back(WeightLiteral{~toLit(lit), weight});
        newBound += weight;
    }
    POTASSCO_CHECK(std::in_range<Weight_t>(newBound), EOVERFLOW, "weight overflow");
    withPrg([&](auto& builder) { builder.addConstraint(constraint_, static_cast<Weight_t>(newBound)); });
}
void BasicProgramAdapter::minimize(Potassco::Weight_t prio, Potassco::WeightLitSpan lits) {
    POTASSCO_CHECK_PRE(prio == 0, "unsupported rule type");
    constraint_.clear();
    for (const auto& [lit, weight] : lits) { constraint_.push_back(WeightLiteral{toLit(lit), weight}); }
    withPrg([&](auto& builder) { builder.addObjective(constraint_); });
}
} // namespace Clasp
