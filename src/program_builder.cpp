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

#include <limits>

namespace Clasp {

/////////////////////////////////////////////////////////////////////////////////////////
// class ProgramBuilder
/////////////////////////////////////////////////////////////////////////////////////////
ProgramBuilder::ProgramBuilder() : ctx_(nullptr), frozen_(true) {}
ProgramBuilder::~ProgramBuilder() = default;
bool ProgramBuilder::ok() const { return ctx_ && ctx_->ok(); }
bool ProgramBuilder::startProgram(SharedContext& ctx) {
    ctx_    = &ctx;
    frozen_ = ctx.frozen();
    return ctx_->ok() && doStartProgram();
}
bool ProgramBuilder::updateProgram() {
    POTASSCO_CHECK_PRE(ctx_, "startProgram() not called!");
    bool ok = ctx_->ok() && ctx_->unfreeze() && doUpdateProgram();
    if (ok) {
        ctx_->setSolveMode(SharedContext::solve_multi);
    }
    if (ok && frozen()) {
        frozen_ = ctx_->frozen();
    }
    return ok;
}
bool ProgramBuilder::endProgram() {
    POTASSCO_CHECK_PRE(ctx_, "startProgram() not called!");
    bool ok = ctx_->ok();
    if (ok && not frozen_) {
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
auto ProgramBuilder::parser() -> ProgramParser& {
    if (not parser_) {
        parser_ = doCreateParser();
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
auto SatBuilder::numVars() const -> Var_t { return ctx()->numVars(); }
bool SatBuilder::acquireVars(Var_t v) {
    if (not ctx()->validVar(v)) {
        ctx()->addVars(v - ctx()->numVars(), VarType::atom, VarInfo::flag_input | VarInfo::flag_nant);
        varState_.resize(ctx()->numVars() + 1, 0u);
    }
    return true;
}
void SatBuilder::integrateVars(LitView lits) {
    std::ignore = prepared_ || lits.empty() || acquireVars(std::ranges::max_element(lits)->var());
}
void SatBuilder::integrateVars(WeightLitView lits) {
    std::ignore = prepared_ || lits.empty() || acquireVars(std::ranges::max_element(lits)->lit.var());
}
bool SatBuilder::markUnits() {
    if (marked_ >= ctx()->master()->numAssignedVars()) {
        return true;
    }
    bool ok = ctx()->ok() && ctx()->master()->propagate();
    for (auto lit : ctx()->master()->trailView(marked_)) {
        markLit(~lit);
        ++marked_;
    }
    return ok;
}
void SatBuilder::setOutputVars() {
    if (auto mx = ctx()->numVars(); mx) {
        ctx()->output.setVarRange({1u, mx + 1u});
    }
}
void SatBuilder::prepareProblem(uint32_t numVars, uint32_t clauseHint) {
    POTASSCO_CHECK_PRE(ctx() && ctx()->ok() && ctx()->numVars() == 0u, "startProgram() not called!");
    acquireVars(numVars);
    setOutputVars();
    ctx()->startAddConstraints(std::min(clauseHint, 10000u));
    prepared_ = true;
}
bool SatBuilder::addObjective(WeightLitView min) {
    integrateVars(min);
    for (const auto& lit : min) {
        addMinLit(0, lit);
        markOcc(~lit.lit);
    }
    return ctx()->ok();
}
void SatBuilder::forceMaxSat() { addMinLit(0, {.lit = lit_true, .weight = 0}); }
void SatBuilder::addProject(Var_t v) { ctx()->output.addProject(posLit(v)); }
void SatBuilder::addAssumption(Literal x) {
    integrateVars(Potassco::toSpan(x));
    assume_.push_back(x);
    markOcc(x);
    ctx()->setFrozen(x.var(), true);
}
bool SatBuilder::addClause(LitVec& clause, Wsum_t cw) {
    if (not ctx()->ok() || satisfied(clause, cw)) {
        return ctx()->ok();
    }
    if (cw <= hard_weight) {
        return ClauseCreator::create(*ctx()->master(), clause, {}, ConstraintType::static_).ok() && markUnits();
    }
    POTASSCO_CHECK_PRE(std::cmp_less_equal(cw, weight_max), "Clause weight out of bounds");
    if (auto sz = size32(clause); sz > 1) {
        ++soft_;
        softClauses_.push_back(Literal::fromRep(static_cast<uint32_t>(cw))); // clause weight
        softClauses_.push_back(Literal::fromRep(sz));                        // clause size
        appendVec(softClauses_, clause);                                     // literals of clause
    }
    else {
        addMinLit(0, WeightLiteral{not clause.empty() ? ~clause[0] : lit_true, static_cast<Weight_t>(cw)});
    }
    return true;
}
bool SatBuilder::satisfied(LitVec& cc, Wsum_t cw) {
    integrateVars(cc);
    bool sat = cw == 0;
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
    truncateVec(cc, j);
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
    integrateVars(lits);
    auto rep = WeightLitsRep::create(*ctx()->master(), lits, bound);
    if (rep.open()) {
        for (const auto& [lit, _] : rep.literals()) { markOcc(lit); }
    }
    return WeightConstraint::create(*ctx()->master(), lit_true, rep, {}).ok() && markUnits();
}
bool SatBuilder::doStartProgram() {
    POTASSCO_CHECK_PRE(ctx() && ctx()->numVars() == 0u, "SharedContext must be empty");
    prepared_ = false;
    soft_     = 0u;
    marked_   = 0u;
    assume_.clear();
    varState_.clear();
    return ctx()->ok();
}
auto SatBuilder::doCreateParser() -> ParserPtr { return std::make_unique<SatParser>(*this); }
bool SatBuilder::doEndProgram() {
    auto ok = ctx()->ok() && markUnits();
    if (ok && not softClauses_.empty()) {
        auto aux = soft_ ? ctx()->addVars(soft_, VarType::atom, VarInfo::flag_nant) : numVars() + 1;
        ctx()->startAddConstraints(soft_);
        ctx()->setPreserveModels(true);
        soft_ = 0u;
        LitVec cc;
        for (auto it = softClauses_.begin(), end = softClauses_.end(); it != end && ok;) {
            auto w  = static_cast<Weight_t>(it++->rep()); // clause weight
            auto sz = it->rep() + 1u;                     // clause size (+1 for relaxation var)
            POTASSCO_ASSERT(sz > 2u && ctx()->validVar(aux));
            *it = posLit(aux++); // replace with relaxation var
            addMinLit(0, WeightLiteral{*it, w});
            cc.assign(it, it + sz);
            it += sz;
            ok  = ClauseCreator::create(*ctx()->master(), cc, {}, ConstraintType::static_).ok();
        }
        while (ok && ctx()->validVar(aux)) { ok = ctx()->addUnary(negLit(aux++)); }
        discardVec(softClauses_);
    }
    if (ok && not varState_.empty()) {
        constexpr uint32_t seen = 12;
        const bool         elim = not ctx()->preserveModels();
        ctx()->master()->acquireProblemVars();
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
    prepared_ = true;
    return ok;
}
/////////////////////////////////////////////////////////////////////////////////////////
// class PBBuilder
/////////////////////////////////////////////////////////////////////////////////////////
struct PBBuilder::Product {
    [[nodiscard]] static constexpr auto allocSize(LitView lits) -> uint32_t {
        return toU32(sizeof(Product) + size32(lits) * sizeof(Literal));
    }
    [[nodiscard]] auto litView() const -> LitView { return {lits, size}; }
    Literal            eq;
    uint32_t           size{0};
    POTASSCO_WARNING_BEGIN_RELAXED
    Literal lits[0];
    POTASSCO_WARNING_END_RELAXED
};

void PBBuilder::prepareProblem(uint32_t numVars, uint32_t numProd, uint32_t numSoft, uint32_t numCons) {
    POTASSCO_CHECK_PRE(ctx(), "startProgram() not called!");
    auto out = ctx()->addVars(numVars, VarType::atom, VarInfo::flag_nant | VarInfo::flag_input);
    auxVar_  = ctx()->addVars(numProd + numSoft, VarType::atom, VarInfo::flag_nant);
    endVar_  = auxVar_ + numProd + numSoft;
    ctx()->output.setVarRange(Range32(out, out + numVars));
    ctx()->startAddConstraints(numCons);
}
auto PBBuilder::nextAuxVar() -> uint32_t {
    POTASSCO_CHECK_PRE(ctx()->validVar(auxVar_), "Variables out of bounds");
    return auxVar_++;
}
bool PBBuilder::addConstraint(WeightLitVec& lits, Weight_t bound, bool eq, Weight_t cw) {
    if (not ctx()->ok()) {
        return false;
    }
    Var_t eqVar = 0;
    auto& s     = *ctx()->master();
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
    if (not eq) {
        return WeightConstraint::create(s, posLit(eqVar), lits, bound).ok();
    }
    // For soft constraints, we only create the following implications:
    // Aux => l1w1 + …+ lnwn >= B
    // ~Aux <= l1w1 + …+ lnwn >= B+1
    auto aux        = cw > 0 ? posLit(eqVar) : lit_true;
    auto lowerFlags = cw > 0 ? WeightConstraint::create_only_btb : WeightConstraint::CreateFlag{};
    auto upperFlags = cw > 0 ? WeightConstraint::create_only_bfb : WeightConstraint::CreateFlag{};
    auto rep        = WeightLitsRep::create(s, lits, bound + 1);
    if (not WeightConstraint::create(s, ~aux, rep, upperFlags).ok()) {
        return false;
    }
    // restore bound and redo coefficient reduction
    rep.bound -= 1;
    if (rep.bound > 0) {
        for (unsigned i = 0; i != rep.size && rep.lits[i].weight > rep.bound; ++i) {
            rep.reach -= rep.lits[i].weight;
            rep.reach += (rep.lits[i].weight = rep.bound);
        }
    }
    else {
        rep.size  = 0;
        rep.reach = 0;
    }
    return WeightConstraint::create(s, aux, rep, lowerFlags).ok();
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
auto PBBuilder::productSubsumed(LitVec& lits) const -> uint32_t {
    for (auto& s = *ctx()->master();;) {
        auto j      = lits.begin();
        auto last   = lit_true;
        auto abst   = 0u;
        auto sorted = true;
        for (auto lit : lits) {
            if (s.isFalse(lit) || ~lit == last) { // product is always false
                lits.assign(1, lit_false);
                return 0u;
            }
            if (last.var() > lit.var()) { // not sorted - redo with sorted product
                sorted = false;
                break;
            }
            if (not s.isTrue(lit) && last != lit) {
                abst += hashLit(lit);
                last  = lit;
                *j++  = last;
            }
        }
        if (sorted) {
            truncateVec(lits, j);
            if (lits.empty()) {
                lits.assign(1, lit_true);
            }
            return abst;
        }
        std::ranges::sort(lits);
    }
}
auto PBBuilder::product(Potassco::Id_t id) const -> const Product* {
    POTASSCO_ASSERT(id < products_.size());
    return reinterpret_cast<const Product*>(products_.data() + id);
}

auto PBBuilder::addProduct(LitVec& lits) -> Literal {
    if (not ctx()->ok()) {
        return lit_false;
    }
    auto abst = productSubsumed(lits);
    POTASSCO_ASSERT(not lits.empty());
    if (lits.size() == 1) {
        return lits[0];
    }
    if (auto r =
            productIndex_.find_if(abst, [&](uint32_t id) { return std::ranges::equal(lits, product(id)->litView()); });
        r.valid()) {
        return product(*r)->eq;
    }
    else {
        auto& ctx   = *this->ctx();
        auto& s     = *ctx.master();
        auto  eqLit = posLit(nextAuxVar());
        auto  idx   = size32(products_);
        auto* p     = new (products_.appendForOverwrite(Product::allocSize(lits)).data()) Product;
        p->size     = size32(lits);
        p->eq       = eqLit;
        auto* pOut  = p->lits;
        productIndex_.add(r, abst, idx);
        assert(s.value(eqLit.var()) == value_free);
        for (auto& lit : lits) {
            assert(s.value(lit.var()) == value_free);
            ctx.addBinary(~eqLit, lit);
            *pOut++ = lit;
            lit     = ~lit;
        }
        assert(ctx.ok());
        lits.push_back(eqLit);
        ClauseCreator::create(s, lits, ClauseCreator::clause_no_prepare);
        return eqLit;
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
auto PBBuilder::doCreateParser() -> ParserPtr { return std::make_unique<SatParser>(*this); }
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
void BasicProgramAdapter::outputAtom(Potassco::Atom_t atom, std::string_view name) {
    POTASSCO_CHECK_PRE(prg_->ctx()->validVar(atom), "invalid variable");
    prg_->ctx()->output.add(name, posLit(atom), atom);
}

} // namespace Clasp
