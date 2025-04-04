//
// Copyright (c) 2013-present Benjamin Kaufmann
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
#include <clasp/logic_program.h>

#include <clasp/asp_preprocessor.h>
#include <clasp/clause.h>
#include <clasp/dependency_graph.h>
#include <clasp/enumerator.h>
#include <clasp/minimize_constraint.h>
#include <clasp/parser.h>
#include <clasp/shared_context.h>
#include <clasp/solver.h>
#include <clasp/util/misc_types.h>

#include <potassco/theory_data.h>

#include <cctype>
#include <unordered_map>
#include <unordered_set>

namespace Clasp::Asp {
/////////////////////////////////////////////////////////////////////////////////////////
// Statistics
/////////////////////////////////////////////////////////////////////////////////////////
#define RK(x) RuleStats::x
const char* RuleStats::toStr(unsigned k) {
    POTASSCO_ASSERT(k <= numKeys(), "Invalid key");
    switch (k) {
        case normal   : return "Normal";
        case choice   : return "Choice";
        case minimize : return "Minimize";
        case acyc     : return "Acyc";
        case heuristic: return "Heuristic";
        default       : return "None";
    }
}
uint32_t    RuleStats::sum() const { return std::accumulate(key, key + numKeys(), 0u); }
const char* BodyStats::toStr(unsigned t) {
    POTASSCO_ASSERT(t < numKeys(), "Invalid body type!");
    switch (t) {
        default                            : return "Normal";
        case to_underlying(BodyType::count): return "Count";
        case to_underlying(BodyType::sum)  : return "Sum";
    }
}
uint32_t BodyStats::sum() const { return std::accumulate(key, key + numKeys(), 0u); }

namespace {
template <unsigned I>
double sumBodies(const LpStats* self) {
    return self->bodies[I].sum();
}
template <unsigned I>
double sumRules(const LpStats* self) {
    return self->rules[I].sum();
}
double sumEqs(const LpStats* self) { return self->eqs(); }
} // namespace
#define LP_STATS(APPLY)                                                                                                \
    APPLY("atoms", VALUE(atoms))                                                                                       \
    APPLY("atoms_aux", VALUE(auxAtoms))                                                                                \
    APPLY("disjunctions", VALUE(disjunctions[0]))                                                                      \
    APPLY("disjunctions_non_hcf", VALUE(disjunctions[1]))                                                              \
    APPLY("bodies", FUNC(sumBodies<0>))                                                                                \
    APPLY("bodies_tr", FUNC(sumBodies<1>))                                                                             \
    APPLY("sum_bodies", VALUE(bodies[0][to_underlying(BodyType::sum)]))                                                \
    APPLY("sum_bodies_tr", VALUE(bodies[1][to_underlying(BodyType::sum)]))                                             \
    APPLY("count_bodies", VALUE(bodies[0][to_underlying(BodyType::count)]))                                            \
    APPLY("count_bodies_tr", VALUE(bodies[1][to_underlying(BodyType::count)]))                                         \
    APPLY("sccs", VALUE(sccs))                                                                                         \
    APPLY("sccs_non_hcf", VALUE(nonHcfs))                                                                              \
    APPLY("gammas", VALUE(gammas))                                                                                     \
    APPLY("ufs_nodes", VALUE(ufsNodes))                                                                                \
    APPLY("rules", FUNC(sumRules<0>))                                                                                  \
    APPLY("rules_normal", VALUE(rules[0][RK(normal)]))                                                                 \
    APPLY("rules_choice", VALUE(rules[0][RK(choice)]))                                                                 \
    APPLY("rules_minimize", VALUE(rules[0][RK(minimize)]))                                                             \
    APPLY("rules_acyc", VALUE(rules[0][RK(acyc)]))                                                                     \
    APPLY("rules_heuristic", VALUE(rules[0][RK(heuristic)]))                                                           \
    APPLY("rules_tr", FUNC(sumRules<1>))                                                                               \
    APPLY("rules_tr_normal", VALUE(rules[1][RK(normal)]))                                                              \
    APPLY("rules_tr_choice", VALUE(rules[1][RK(choice)]))                                                              \
    APPLY("rules_tr_minimize", VALUE(rules[1][RK(minimize)]))                                                          \
    APPLY("rules_tr_acyc", VALUE(rules[1][RK(acyc)]))                                                                  \
    APPLY("rules_tr_heuristic", VALUE(rules[1][RK(heuristic)]))                                                        \
    APPLY("eqs", FUNC(sumEqs))                                                                                         \
    APPLY("eqs_atom", VALUE(eqs_[+VarType::atom - 1]))                                                                 \
    APPLY("eqs_body", VALUE(eqs_[+VarType::body - 1]))                                                                 \
    APPLY("eqs_other", VALUE(eqs_[+VarType::hybrid - 1]))

void LpStats::accu(const LpStats& o) {
    atoms    += o.atoms;
    auxAtoms += o.auxAtoms;
    ufsNodes += o.ufsNodes;
    if (sccs == PrgNode::no_scc || o.sccs == PrgNode::no_scc) {
        sccs    = o.sccs;
        nonHcfs = o.nonHcfs;
        gammas  = o.gammas;
    }
    else {
        sccs    += o.sccs;
        nonHcfs += o.nonHcfs;
        gammas  += o.gammas;
    }
    for (auto i : irange(disjunctions)) {
        disjunctions[i] += o.disjunctions[i];
        for (auto k : irange(BodyStats::numKeys())) { bodies[i][k] += o.bodies[i][k]; }
        for (auto k : irange(RuleStats::numKeys())) { rules[i][k] += o.rules[i][k]; }
    }
    std::ranges::transform(eqs_, o.eqs_, eqs_, std::plus{});
}

static constexpr const char* lp_stats_s[] = {
#define KEY(x, y) x,
    LP_STATS(KEY)
#undef KEY
        "lp"};
uint32_t    LpStats::size() { return (sizeof(lp_stats_s) / sizeof(const char*)) - 1; }
const char* LpStats::key(uint32_t i) {
    POTASSCO_CHECK(i < size(), ERANGE);
    return lp_stats_s[i];
}
StatisticObject LpStats::at(const char* k) const {
#define MAP_IF(x, A)                                                                                                   \
    if (std::strcmp(k, x) == 0)                                                                                        \
        return A;
#define VALUE(X) StatisticObject::value(&(X))
#define FUNC(F)  StatisticObject::value<LpStats, F>(this)
    LP_STATS(MAP_IF)
#undef VALUE
#undef FUNC
#undef MAP_IF
    POTASSCO_CHECK(false, ERANGE);
}
#undef LP_STATS
/////////////////////////////////////////////////////////////////////////////////////////
// class LogicProgram
/////////////////////////////////////////////////////////////////////////////////////////
constexpr uint32_t false_id = PrgNode::no_node;
constexpr uint32_t body_id  = PrgNode::no_node + 1;
constexpr bool     isAtom(Id_t uid) { return Potassco::atom(Potassco::lit(uid)) < body_id; }
constexpr bool     isBody(Id_t uid) { return Potassco::atom(Potassco::lit(uid)) >= body_id; }
constexpr Id_t     nodeId(Id_t uid) { return Potassco::atom(Potassco::lit(uid)) - (isAtom(uid) ? 0 : body_id); }
constexpr bool     signId(Id_t uid) { return Potassco::lit(uid) < 0; }

using AtomVal = std::pair<Atom_t, Potassco::TruthValue>;
constexpr uint32_t encodeExternal(Atom_t a, Potassco::TruthValue value) {
    return (a << 2) | static_cast<uint32_t>(value);
}
constexpr AtomVal decodeExternal(uint32_t x) { return {x >> 2, static_cast<Potassco::TruthValue>(x & 3u)}; }

// Adds nogoods representing this node to the solver.
template <typename NodeType>
static bool toConstraint(NodeType* node, const LogicProgram& prg, ClauseCreator& c) {
    if (node->value() != value_free && not prg.ctx()->addUnary(node->trueLit())) {
        return false;
    }
    return not node->relevant() || node->addConstraints(prg, c);
}

using IdSet    = std::unordered_set<Id_t>;
using IndexMap = std::unordered_multimap<uint32_t, uint32_t>;
struct LogicProgram::Aux {
    AtomList  scc;          // atoms that are strongly connected
    DomRules  dom;          // list of domain heuristic directives
    AcycRules acyc;         // list of user-defined edges for acyclicity check
    VarVec    project;      // atoms in projection directives
    VarVec    external;     // atoms in external directives
    IdSet     skippedHeads; // heads of rules that have been removed during parsing
};

struct LogicProgram::IndexData {
    IndexMap body;   // hash -> body id
    IndexMap disj;   // hash -> disjunction id
    IndexMap domEq;  // maps eq atoms modified by dom heuristic to aux vars
    VarVec   outSet; // atoms with non-trivial out state (shown and/or projected)
    PrgAtom* eqTrue{nullptr};
    bool     distTrue{false};
    bool     outState{false};
};

LogicProgram::LogicProgram()
    : index_(std::make_unique<IndexData>())
    , input_(1, UINT32_MAX)
    , statsId_(0)
    , auxData_(std::make_unique<Aux>())
    , incData_(nullptr) {}
LogicProgram::~LogicProgram() { reset(); }
void LogicProgram::reset() {
    dispose();
    deleteAtoms(0);
    discardVec(assume_);
    discardVec(atomState_);
    discardVec(atoms_);
    discardVec(frozen_);
    discardVec(propQ_);
    nonHcfs_ = NonHcfSet();
    incData_.reset();
    input_   = AtomRange(1, UINT32_MAX);
    stats    = {};
    statsId_ = 0;
    *index_  = IndexData();
}
void LogicProgram::dispose() {
    auto disposeVec = [](auto& vec, auto destroyOp) {
        std::ranges::for_each(vec, destroyOp);
        discardVec(vec);
    };
    disposeVec(bodies_, DestroyObject());
    disposeVec(disjunctions_, DestroyObject());
    disposeVec(extended_, DeleteObject());
    disposeVec(minimize_, DeleteObject());
    PodVector<ShowPair>::destruct(show_);
    discardVec(initialSupp_);
    *auxData_ = Aux();
    index_->body.clear();
    index_->disj.clear();
    theory_.reset();
    rule_.clear();
}
void LogicProgram::deleteAtoms(uint32_t start) {
    for (PrgAtom* atom : atoms(start)) {
        if (atom != index_->eqTrue) {
            delete atom;
        }
    }
    if (start == 0 && index_ && index_->eqTrue) {
        delete std::exchange(index_->eqTrue, nullptr);
    }
}
bool LogicProgram::doStartProgram() {
    if (not atoms_.empty()) {
        reset();
    }
    // atom 0 is always true
    atoms_.push_back(new PrgAtom(0, false));
    auto* trueAt = getTrueAtom();
    trueAt->assignValue(value_true);
    trueAt->setInUpper(true);
    trueAt->setLiteral(lit_true);
    atomState_.set(0, AtomState::fact_flag);
    return true;
}
void LogicProgram::setOptions(const AspOptions& opts) {
    opts_ = opts;
    if (opts.suppMod) {
        opts_.noSCC = 1;
    }
    if (opts.suppMod && ctx() && ctx()->sccGraph.get()) {
        ctx()->warn("'supp-models' ignored for non-tight programs.");
        opts_.suppMod = 0;
        opts_.noSCC   = 0;
    }
}
void LogicProgram::enableDistinctTrue() { index_->distTrue = true; }
void LogicProgram::enableOutputState() { index_->outState = true; }
auto LogicProgram::doCreateParser() -> ProgramParser* { return new AspParser(*this); }
bool LogicProgram::doUpdateProgram() {
    if (not incData_) {
        incData_ = std::make_unique<Incremental>();
    }
    if (not frozen()) {
        return true;
    }
    // delete bodies/disjunctions...
    dispose();
    setFrozen(false);
    assume_.clear();
    theory_.update();
    incData_->unfreeze.clear();
    incData_->first = false;
    input_.hi       = std::min(input_.hi, endAtom());
    // reset prop queue and add supported atoms from previous steps
    // {'ai' | 'ai' in P}.
    PrgBody* support = input_.hi > 1 ? getTrueBody() : nullptr;
    propQ_.clear();
    for (auto end = startAuxAtom(); Atom_t i : irange(1u, end)) {
        if (getRootId(i) >= end) {
            // atom is equivalent to some aux atom - make i the new root
            uint32_t r = getRootId(i);
            std::swap(atoms_[i], atoms_[r]);
            atoms_[r]->setEq(i);
        }
        // remove dangling references
        PrgAtom* a = atoms_[i];
        a->clearSupports();
        a->clearDeps(PrgAtom::dep_all);
        a->setIgnoreScc(false);
        if (a->relevant() || a->frozen()) {
            auto v = a->value();
            a->setValue(value_free);
            a->resetId(i, not a->frozen());
            if (ctx()->master()->value(a->var()) != value_free && not a->frozen()) {
                v = ctx()->master()->isTrue(a->literal()) ? value_true : value_false;
            }
            if (v != value_free) {
                assignValue(a, v, PrgEdge::noEdge());
            }
            if (not a->frozen() && a->value() != value_false) {
                a->setIgnoreScc(true);
                support->addHead(a, PrgEdge::gamma_choice);
            }
        }
        else if (a->removed() || (not a->eq() && a->value() == value_false)) {
            a->resetId(i, true);
            a->setValue(value_false);
            atomState_.set(i, AtomState::false_flag);
        }
    }
    // delete any introduced aux atoms
    // this is safe because aux atoms are never part of the input program
    // it is necessary in order to free their ids, i.e. the id of an aux atom
    // from step I might be needed for a program atom in step I+1
    deleteAtoms(startAuxAtom());
    shrinkVecTo(atoms_, startAuxAtom());
    auto nAtoms = size32(atoms_);
    atomState_.resize(nAtoms);
    input_   = AtomRange(nAtoms, UINT32_MAX);
    stats    = {};
    statsId_ = 0;
    return true;
}
bool LogicProgram::doEndProgram() {
    if (not frozen() && ctx()->ok()) {
        prepareProgram(not opts_.noSCC);
        addConstraints();
        addDomRules();
        addAcycConstraint();
    }
    return ctx()->ok();
}

void LogicProgram::addMinimize() {
    POTASSCO_ASSERT(frozen());
    for (const auto* min : minimize_) {
        auto prio = min->bound();
        auto lits = min->sumLits();
        for (const auto& [lit, weight] : lits) { addMinLit(prio, WeightLiteral{getLiteral(Asp::id(lit)), weight}); }
        // Make sure minimize constraint is not empty
        if (lits.empty()) {
            addMinLit(prio, WeightLiteral{lit_false, 1});
        }
    }
}
static void outRule(Potassco::AbstractProgram& out, const Rule& r) {
    if (r.normal()) {
        out.rule(r.ht, r.head, r.cond);
    }
    else {
        out.rule(r.ht, r.head, r.agg.bound, r.agg.lits);
    }
}

void LogicProgram::accept(Potassco::AbstractProgram& out, bool addPreamble) {
    if (not started()) {
        return;
    }
    if (addPreamble) {
        if (not incData_ || incData_->first) {
            out.initProgram(incData_ != nullptr);
        }
        out.beginStep();
    }
    POTASSCO_SCOPE_EXIT({
        if (addPreamble) {
            out.endStep();
        }
    });
    if (not ok()) {
        out.rule(HeadType::disjunctive, {}, {});
        return;
    }
    // visit external directives
    for (auto e : auxData_->external) {
        auto [atom, value] = decodeExternal(e);
        out.external(atom, value);
    }
    // visit eq- and assigned atoms
    for (auto i : irange(startAtom(), size32(atoms_))) {
        if (auto* atom = atoms_[i]; atom->eq()) {
            auto head = Potassco::toSpan(i);
            if (auto body = Potassco::lit(getRootId(i)); isFact(Potassco::atom(body))) {
                out.rule(HeadType::disjunctive, head, {});
            }
            else if (inProgram(Potassco::atom(body))) {
                out.rule(HeadType::disjunctive, head, Potassco::toSpan(body));
            }
        }
        else if (not atomState_.isFact(i) && atom->value() != value_free) {
            auto body = Potassco::neg(i);
            if (atoms_[i]->value() != value_false) {
                out.rule(HeadType::disjunctive, {}, Potassco::toSpan(body));
            }
            else if (inProgram(i)) {
                body = Potassco::neg(body);
                out.rule(HeadType::disjunctive, {}, Potassco::toSpan(body));
            }
        }
    }
    // visit program rules
    const bool simp = frozen();
    using Potassco::Lit_t;
    VarVec choice;
    for (auto* b : bodies_) {
        rule_.clear();
        choice.clear();
        if (b->relevant() && (b->inRule() || b->value() == value_false) && b->toData(*this, rule_)) {
            if (b->value() == value_false) {
                outRule(out, rule_.rule());
                continue;
            }
            uint32_t numDis = 0;
            Atom_t   head;
            Lit_t    auxB;
            Rule     r = rule_.rule();
            for (auto h : b->heads()) {
                if (h.isGamma() || (simp && not getHead(h)->hasVar())) {
                    continue;
                }
                if (h.isAtom() && h.node() && inProgram(h.node())) {
                    if (h.isNormal()) {
                        head   = h.node();
                        r.head = Potassco::toSpan(head);
                        outRule(out, r);
                    }
                    else if (h.isChoice()) {
                        choice.push_back(h.node());
                    }
                    if (simp && getRootAtom(h.node())->var() == b->var() && not r.normal()) {
                        // replace complex body with head atom
                        auxB = Potassco::lit(h.node());
                        if (getRootAtom(h.node())->literal() != b->literal()) {
                            auxB *= -1;
                        }
                        r.bt   = BodyType::normal;
                        r.cond = Potassco::toSpan(auxB);
                    }
                }
                else if (h.isDisj()) {
                    ++numDis;
                }
            }
            if (not choice.empty()) {
                r.head = choice;
                r.ht   = HeadType::choice;
                outRule(out, r);
            }
            if (numDis) {
                for (auto h : b->heads()) {
                    if (h.isDisj()) {
                        PrgDisj* d = getDisj(h.node());
                        r.head     = d->atoms();
                        r.ht       = HeadType::disjunctive;
                        outRule(out, r);
                        if (--numDis == 0) {
                            break;
                        }
                    }
                }
            }
        }
    }
    LpWLitVec wlits;
    auto      pred = [&](Potassco::WeightLit x) {
        return x.weight != 0 && (x.weight < 0 || x.lit < 0 || inProgram(getRootId(Potassco::atom(x))));
    };
    for (const auto* min : minimize_) {
        WeightLitSpan ws = min->sumLits();
        if (auto it = std::ranges::find_if_not(ws, pred); it != ws.end()) {
            // simplify literals
            wlits.assign(ws.begin(), it);
            for (++it; it != ws.end(); ++it) {
                if (pred(*it)) {
                    wlits.push_back(*it);
                }
            }
            ws = wlits;
        }
        out.minimize(min->bound(), ws);
    }
    Potassco::LitVec lits;
    // visit output directives
    for (const auto& [id, name] : show_) {
        if (extractCondition(id, lits)) {
            out.output(name.c_str(), lits);
        }
    }
    // visit projection directives
    if (not auxData_->project.empty()) {
        out.project(auxData_->project.back() ? Potassco::AtomSpan(auxData_->project) : Potassco::AtomSpan{});
    }
    // visit assumptions
    if (not assume_.empty()) {
        out.assume(assume_);
    }
    // visit heuristics
    for (const auto& dom : auxData_->dom) {
        if (extractCondition(dom.cond, lits)) {
            out.heuristic(dom.atom, static_cast<DomModType>(dom.type), dom.bias, dom.prio, lits);
        }
    }
    // visit acyc edges
    for (const auto& a : auxData_->acyc) {
        if (extractCondition(a.cond, lits)) {
            out.acycEdge(static_cast<int>(a.node[0]), static_cast<int>(a.node[1]), lits);
        }
    }

    if (theory_.numAtoms()) {
        struct This final : TheoryData::Visitor {
            This(const LogicProgram& p, Potassco::AbstractProgram& o, Potassco::LitVec& c)
                : self(&p)
                , out(&o)
                , cond(&c) {}
            void visit(const TheoryData& data, Id_t termId, const Potassco::TheoryTerm& t) override {
                if (not addTermSeen(termId)) {
                    return;
                }
                data.accept(t, *this, TheoryData::visit_current);
                Potassco::print(*out, termId, t);
            }
            void visit(const TheoryData& data, Id_t elemId, const Potassco::TheoryElement& e) override {
                if (not addElemSeen(elemId)) {
                    return;
                }
                data.accept(e, *this, TheoryData::visit_current);
                cond->clear();
                if (e.condition()) {
                    self->extractCondition(e.condition(), *cond);
                }
                out->theoryElement(elemId, e.terms(), *cond);
            }
            void visit(const TheoryData& data, const Potassco::TheoryAtom& a) override {
                data.accept(a, *this, TheoryData::visit_current);
                Potassco::print(*out, a);
                const Atom_t id = a.atom();
                if (self->validAtom(id) && self->atomState_.isSet(id, AtomState::false_flag) &&
                    not self->inProgram(id)) {
                    Lit_t x = Potassco::lit(id);
                    out->rule(HeadType::disjunctive, {}, Potassco::toSpan(x));
                }
            }
            bool addTermSeen(Id_t id) { return seen.add(id * 2); }
            bool addElemSeen(Id_t id) { return seen.add((id * 2) + 1); }

            const LogicProgram*        self;
            Potassco::AbstractProgram* out;
            Potassco::LitVec*          cond;
            Potassco::DynamicBitset    seen;
        } self(*this, out, lits);
        theory_.accept(self, TheoryData::visit_current);
    }
}
/////////////////////////////////////////////////////////////////////////////////////////
// Program mutating functions
/////////////////////////////////////////////////////////////////////////////////////////
#define CHECK_NOT_FROZEN() POTASSCO_CHECK_PRE(not frozen(), "Can't update frozen program!")
static const char* getAtomName(const LogicProgram& prg, Atom_t a) {
    const char* ret = prg.findName(a);
    return ret && *ret ? ret : "_";
}
#define CHECK_MODULAR(x, atomId)                                                                                       \
    POTASSCO_CHECK_PRE(x, "redefinition of atom <'%s',%u>", getAtomName(*this, (atomId)), (atomId))

Atom_t LogicProgram::newAtom() {
    CHECK_NOT_FROZEN();
    auto id = size32(atoms_);
    atoms_.push_back(new PrgAtom(id));
    return id;
}
Id_t LogicProgram::newCondition(Potassco::LitSpan cond) {
    CHECK_NOT_FROZEN();
    SRule meta;
    if (simplifyNormal(HeadType::disjunctive, {}, cond, rule_, meta)) {
        Rule r = rule_.rule();
        if (r.cond.empty()) {
            return 0;
        }
        if (r.cond.size() == 1) {
            return Asp::id(r.cond[0]);
        }
        PrgBody* b = getBodyFor(r, meta);
        b->markFrozen();
        return static_cast<Id_t>(Clasp::Asp::body_id | b->id());
    }
    return static_cast<Id_t>(Clasp::Asp::false_id);
}
LogicProgram& LogicProgram::addOutput(const Potassco::ConstString& str, Potassco::LitSpan cond) {
    CHECK_NOT_FROZEN();
    if (cond.size() == 1) {
        POTASSCO_CHECK_PRE(Potassco::atom(cond[0]) < body_id, "Atom out of bounds");
        return addOutput(str, Asp::id(cond[0]));
    }
    if (not ctx()->output.filter(str)) {
        show_.push_back(ShowPair(newCondition(cond), str));
    }
    return *this;
}
LogicProgram& LogicProgram::addOutput(const Potassco::ConstString& str, Id_t id) {
    CHECK_NOT_FROZEN();
    if (not ctx()->output.filter(str) && id != false_id) {
        if (Potassco::atom(id) < body_id) {
            resize(Potassco::atom(id));
        }
        show_.push_back(ShowPair(id, str));
    }
    return *this;
}
LogicProgram& LogicProgram::addOutput(std::string_view str, Potassco::LitSpan cond) {
    return addOutput(Potassco::ConstString(str, Potassco::ConstString::create_shared), cond);
}
LogicProgram& LogicProgram::addOutput(std::string_view str, Id_t id) {
    return addOutput(Potassco::ConstString(str, Potassco::ConstString::create_shared), id);
}

LogicProgram& LogicProgram::addProject(Potassco::AtomSpan atoms) {
    CHECK_NOT_FROZEN();
    VarVec& pro = auxData_->project;
    if (not atoms.empty()) {
        if (not pro.empty() && pro.back() == 0) {
            pro.pop_back();
        }
        pro.insert(pro.end(), atoms.begin(), atoms.end());
    }
    else if (pro.empty()) {
        pro.push_back(0);
    }
    return *this;
}
LogicProgram& LogicProgram::removeProject() {
    bool cleanup = not auxData_->project.empty() || ctx()->output.hasProject();
    auxData_->project.clear();
    ctx()->output.clearProject();
    if (cleanup) {
        for (auto& x : index_->outSet) { Potassco::store_clear_mask(x, out_projected); }
    }
    return *this;
}

Potassco::TheoryData& LogicProgram::theoryData() { return theory_; }

void LogicProgram::pushFrozen(PrgAtom* atom, Val_t v) {
    if (not atom->frozen()) {
        frozen_.push_back(atom->id());
    }
    atom->markFrozen(v);
}

LogicProgram& LogicProgram::addExternal(Atom_t atomId, Potassco::TruthValue value) {
    CHECK_NOT_FROZEN();
    if (PrgAtom* a = resize(atomId); a->numSupports() == 0 && (isNewAtom(a->id()) || a->frozen())) {
        if (value == Potassco::TruthValue::release) {
            // add dummy edge - will be removed once we update the set of frozen atoms
            a->addSupport(PrgEdge::noEdge());
            value = Potassco::TruthValue::free;
        }
        pushFrozen(a, static_cast<Val_t>(value));
        auxData_->external.push_back(encodeExternal(a->id(), value));
    }
    return *this;
}

LogicProgram& LogicProgram::freeze(Atom_t atomId, Val_t value) {
    POTASSCO_ASSERT(value < value_weak_true);
    return addExternal(atomId, static_cast<Potassco::TruthValue>(value));
}

LogicProgram& LogicProgram::unfreeze(Atom_t atomId) { return addExternal(atomId, Potassco::TruthValue::release); }
void          LogicProgram::setMaxInputAtom(uint32_t n) {
    CHECK_NOT_FROZEN();
    resize(n++);
    POTASSCO_CHECK_PRE(n >= startAtom(), "invalid input range");
    input_.hi = n;
}
Atom_t LogicProgram::startAuxAtom() const { return validAtom(input_.hi) ? input_.hi : size32(atoms_); }
bool   LogicProgram::supportsSmodels(const char** errorOut) const {
    const char*  ignore;
    const char*& eOut = errorOut ? *errorOut : ignore;
    if (incData_ || not theory_.empty()) {
        eOut = incData_ ? "incremental" : "theory";
        return false;
    }
    if (not auxData_->dom.empty()) {
        eOut = "heuristic";
        return false;
    }
    if (not auxData_->acyc.empty()) {
        eOut = "edge";
        return false;
    }
    if (not assume_.empty()) {
        eOut = "assumption";
        return false;
    }
    if (not auxData_->project.empty()) {
        eOut = "projection";
        return false;
    }
    if (not std::ranges::all_of(show_, [](const ShowPair& s) {
            auto lit = Potassco::lit(s.first);
            return lit > 0 && static_cast<uint32_t>(lit) < body_id;
        })) {
        eOut = "general output";
        return false;
    }
    return true;
}

bool LogicProgram::isExternal(Atom_t aId) const {
    if (not aId || not validAtom(aId)) {
        return false;
    }
    PrgAtom* a = getRootAtom(aId);
    return a->frozen() && (a->numSupports() == 0 || frozen());
}
bool LogicProgram::isFact(Atom_t a) const {
    return validAtom(a) && (atomState_.isFact(a) || atomState_.isFact(getRootId(a)));
}
bool LogicProgram::isNew(Atom_t a) const { return isNewAtom(a) && validAtom(a); }
bool LogicProgram::isOld(Atom_t a) const { return a && a < startAtom(); }
bool LogicProgram::isDefined(Atom_t aId) const {
    if (not validAtom(aId) || getAtom(aId)->removed()) {
        return false;
    }
    PrgAtom* a = getAtom(aId);
    return isFact(aId) || (a->relevant() && a->numSupports() && not isExternal(aId));
}
bool LogicProgram::inProgram(Atom_t id) const {
    if (PrgAtom* a = validAtom(id) ? getAtom(id) : nullptr; a) {
        return a->relevant() && (a->numSupports() || a->frozen() || isOld(id));
    }
    return false;
}
LogicProgram& LogicProgram::addAssumption(Potassco::LitSpan lits) {
    assume_.insert(assume_.end(), lits.begin(), lits.end());
    return *this;
}

LogicProgram& LogicProgram::addAcycEdge(uint32_t n1, uint32_t n2, Id_t condId) {
    CHECK_NOT_FROZEN();
    if (condId != false_id) {
        AcycArc arc = {condId, {n1, n2}};
        auxData_->acyc.push_back(arc);
    }
    upStat(RK(acyc), 1);
    return *this;
}

LogicProgram& LogicProgram::addDomHeuristic(Atom_t atom, DomModType t, int bias, unsigned prio) {
    return addDomHeuristic(atom, t, bias, prio, {});
}
LogicProgram& LogicProgram::addDomHeuristic(Atom_t atom, DomModType type, int bias, unsigned prio, Id_t cond) {
    static_assert(sizeof(DomRule) == sizeof(uint32_t[3]), "Invalid DomRule size");
    CHECK_NOT_FROZEN();
    if (cond != false_id) {
        auxData_->dom.push_back(DomRule());
        DomRule& x = auxData_->dom.back();
        x.atom     = atom;
        x.type     = +type;
        x.cond     = cond;
        x.bias     = Clasp::saturate_cast<int16_t>(bias);
        x.prio     = Clasp::saturate_cast<uint16_t>(prio);
    }
    upStat(RK(heuristic), 1);
    return *this;
}
LogicProgram& LogicProgram::addRule(const Rule& rule) {
    CHECK_NOT_FROZEN();
    if (SRule meta; simplifyRule(rule, rule_, meta)) {
        Rule sRule = rule_.rule();
        upStat(sRule.ht);
        if (handleNatively(sRule)) { // and can be handled natively
            addRule(sRule, meta);
        }
        else {
            upStat(sRule.bt);
            if (sRule.head.size() <= 1 && transformNoAux(sRule)) {
                // rule transformation does not require aux atoms - do it now
                int oId  = statsId_;
                statsId_ = 1;
                RuleTransform tm(*this);
                upStat(sRule.bt, -1);
                upStat(rule.ht, -1);
                tm.transform(sRule, RuleTransform::strategy_no_aux);
                statsId_ = oId;
            }
            else {
                // make sure we have all head atoms
                for (auto head : sRule.head) { resize(head); }
                extended_.push_back(new RuleBuilder(rule_));
            }
        }
    }
    if (statsId_ == 0) {
        // Assume all (new) heads are initially in "upper" closure.
        for (auto h : rule.head) {
            if (isOld(h)) {
                continue;
            }
            if (validAtom(h)) {
                getAtom(h)->setInUpper(true);
            }
            else {
                auxData_->skippedHeads.insert(h);
            }
        }
    }
    rule_.clear();
    return *this;
}

LogicProgram& LogicProgram::addRule(Potassco::RuleBuilder& rb) {
    LogicProgramAdapter prg(*this);
    rb.end(&prg);
    return *this;
}
LogicProgram& LogicProgram::addMinimize(Weight_t prio, WeightLitSpan lits) {
    CHECK_NOT_FROZEN();
    auto it = std::ranges::lower_bound(minimize_, prio, std::less{}, [](const auto* rb) { return rb->bound(); });
    if (it == minimize_.end() || (*it)->bound() != prio) {
        upStat(RuleStats::minimize);
        it = minimize_.insert(it, new RuleBuilder());
        (*it)->startMinimize(prio);
    }
    for (const auto& lit : lits) {
        (*it)->addGoal(lit);
        // Touch all atoms in minimize -> these are input atoms even if they won't occur in a head.
        resize(Potassco::atom(lit));
    }
    return *this;
}
LogicProgram& LogicProgram::removeMinimize() {
    std::ranges::for_each(minimize_, DeleteObject());
    discardVec(minimize_);
    ctx()->removeMinimize();
    return *this;
}
#undef CHECK_NOT_FROZEN
/////////////////////////////////////////////////////////////////////////////////////////
// Query functions
/////////////////////////////////////////////////////////////////////////////////////////
bool LogicProgram::isFact(const PrgAtom* a) const {
    uint32_t eqId = getRootId(a->id());
    if (atomState_.isFact(eqId)) {
        return true;
    }
    if (a->value() == value_true) {
        for (auto b : a->supports()) {
            if (b.isBody() && b.isNormal() && getBody(b.node())->bound() == 0) {
                return true;
            }
        }
    }
    return false;
}
Literal LogicProgram::getLiteral(Id_t id, MapLit m) const {
    Literal out = lit_false;
    if (Id_t nId = nodeId(id); isAtom(id) && validAtom(nId)) {
        out = getRootAtom(nId)->literal();
        if (m == MapLit::refined) {
            if (auto dom = index_->domEq.find(nId); dom != index_->domEq.end()) {
                out = posLit(dom->second);
            }
            else if (isSentinel(out) && incData_ && not incData_->steps.empty()) {
                auto v = isNewAtom(id)
                             ? incData_->steps.back().second
                             : std::ranges::lower_bound(incData_->steps, Incremental::StepTrue(nId, 0))->second;
                out    = Literal(v, out.sign());
            }
        }
    }
    else if (isBody(id)) {
        POTASSCO_CHECK_PRE(validBody(nId), "Invalid condition");
        out = getBody(getEqBody(nId))->literal();
    }
    return out ^ signId(id);
}

LogicProgram::OutputState LogicProgram::getOutputState(Atom_t atom, MapLit mode) const {
    uint32_t res = out_none;
    while (validAtom(atom)) {
        Var_t key = atom << 2u;
        auto  it  = std::ranges::lower_bound(index_->outSet, key);
        if (it != index_->outSet.end() && (*it & ~3u) == key) {
            res |= static_cast<OutputState>(*it & 3u);
        }
        Atom_t next = mode == MapLit::raw ? atom : getRootId(atom);
        if (next == atom) {
            break;
        }
        atom = next;
        mode = MapLit::raw;
    }
    return static_cast<OutputState>(res);
}

void LogicProgram::doGetAssumptions(LitVec& out) const {
    for (auto v : frozen_) {
        if (Literal lit = getRootAtom(v)->assumption(); lit != lit_true) {
            out.push_back(lit);
        }
    }
    for (auto v : assume_) { out.push_back(getLiteral(Asp::id(v))); }
}
bool LogicProgram::translateCore(LitView solverCore, Potassco::LitVec& prgLits) const {
    uint32_t marked = 0;
    prgLits.clear();
    for (auto lit : solverCore) {
        if (not ctx()->validVar(lit.var())) {
            break;
        }
        ctx()->mark(lit);
        ++marked;
    }
    if (marked == solverCore.size()) {
        for (auto it = frozen_.begin(), end = frozen_.end(); it != end && marked; ++it) {
            PrgAtom* atom = getRootAtom(*it);
            Literal  lit  = atom->assumption();
            if (lit == lit_true || not ctx()->marked(lit)) {
                continue;
            }
            prgLits.push_back(atom->literal() == lit ? Potassco::lit(*it) : Potassco::neg(*it));
            ctx()->unmark(lit);
            --marked;
        }
        for (auto it = assume_.begin(), end = assume_.end(); it != end && marked; ++it) {
            Literal lit = getLiteral(Asp::id(*it));
            if (not ctx()->marked(lit)) {
                continue;
            }
            prgLits.push_back(*it);
            ctx()->unmark(lit);
            --marked;
        }
    }
    for (auto lit : solverCore) {
        if (ctx()->validVar(lit.var())) {
            ctx()->unmark(lit.var());
        }
    }
    return prgLits.size() == solverCore.size();
}
/////////////////////////////////////////////////////////////////////////////////////////
// Program definition - private
/////////////////////////////////////////////////////////////////////////////////////////
void LogicProgram::addRule(const Rule& r, const SRule& meta) {
    if (r.head.size() <= 1 && r.ht == HeadType::disjunctive) {
        if (r.head.empty()) {
            addIntegrity(r, meta);
            return;
        }
        if (r.normal() && r.cond.empty()) {
            addFact(r.head[0]);
            return;
        }
    }
    // only a non-false body can define atoms
    if (PrgBody* b = getBodyFor(r, meta); b->value() != value_false) {
        bool const     disjunctive = r.head.size() > 1 && r.ht == HeadType::disjunctive;
        const EdgeType t           = r.ht == HeadType::disjunctive ? PrgEdge::normal : PrgEdge::choice;
        uint32_t       headHash    = 0;
        bool           ignoreScc   = opts_.noSCC || b->size() == 0;
        for (auto h : r.head) {
            PrgAtom* a = resize(h);
            CHECK_MODULAR(isNewAtom(h) || a->frozen() || a->value() == value_false, h);
            if (not disjunctive) {
                // Note: b->heads may now contain duplicates. They are removed in PrgBody::simplifyHeads.
                b->addHead(a, t);
                if (ignoreScc) {
                    a->setIgnoreScc(ignoreScc);
                }
            }
            else {
                headHash += hashLit(posLit(h));
                atomState_.addToHead(h);
            }
        }
        if (disjunctive) {
            PrgDisj* d = getDisjFor(r.head, headHash);
            b->addHead(d, t);
        }
    }
}
void LogicProgram::addFact(Atom_t atomId) {
    PrgAtom* a = resize(atomId);
    CHECK_MODULAR(isNewAtom(atomId) || a->frozen() || a->value() == value_false, atomId);
    if (atomId != a->id() || atomState_.isFact(atomId)) {
        return;
    }
    a->setIgnoreScc(true);
    atomState_.set(atomId, AtomState::fact_flag);
    if (a->frozen() || not a->deps().empty()) {
        PrgBody* tb = getTrueBody();
        tb->addHead(a, PrgEdge::normal);
        assignValue(a, value_true, PrgEdge::newEdge(*tb, PrgEdge::normal));
        return;
    }
    // Simplify and remove atom from program
    if (not a->assignValue(value_true)) {
        setConflict();
    }
    EdgeVec supps;
    a->clearSupports(supps);
    for (auto s : supps) {
        if (s.isBody()) {
            getBody(s.node())->markHeadsDirty();
        }
        else if (s.isDisj()) { // Disjunction is true
            getDisj(s.node())->detach(*this);
        }
    }
    if (index_->eqTrue == nullptr) {
        a->setInUpper(false);
        a->clearLiteral(true);
        a->setEq(0);
        index_->eqTrue = std::exchange(a, nullptr);
    }
    atoms_[atomId] = index_->eqTrue;
    delete a;
}
void LogicProgram::addIntegrity(const Rule& r, const SRule& meta) {
    if (r.sum() || r.cond.size() != 1 || meta.bid != var_max) {
        PrgBody* body = getBodyFor(r, meta);
        if (not body->assignValue(value_false) || not body->propagateValue(*this, true)) {
            setConflict();
        }
    }
    else {
        PrgAtom* a = resize(Potassco::atom(r.cond[0]));
        auto     v = r.cond[0] > 0 ? value_false : value_weak_true;
        assignValue(a, v, PrgEdge::noEdge());
    }
}
bool LogicProgram::assignValue(PrgAtom* a, Val_t v, PrgEdge reason) {
    if (a->eq()) {
        a = getRootAtom(a->id());
    }
    auto old = a->value();
    if (old == value_weak_true && v != value_weak_true) {
        old = value_free;
    }
    if (not a->assignValue(v)) {
        setConflict();
        return false;
    }
    if (old == value_free) {
        propQ_.push_back(a->id());
    }
    if (v == value_false) {
        atomState_.set(a->id(), AtomState::false_flag);
    }
    else if (v == value_true && reason.isBody() && reason.isNormal() && getBody(reason.node())->bound() == 0) {
        atomState_.set(a->id(), AtomState::fact_flag);
    }
    return true;
}
bool LogicProgram::assignValue(PrgHead* h, Val_t v, PrgEdge reason) {
    return not h->isAtom() || assignValue(node_cast<PrgAtom>(h), v, reason);
}

bool LogicProgram::handleNatively(const Rule& r) const {
    auto mode = opts_.erMode;
    if (mode == mode_native || (r.normal() && r.ht == HeadType::disjunctive)) {
        return true;
    }
    switch (mode) {
        case mode_transform        : return false;
        case mode_transform_choice : return r.ht != HeadType::choice;
        case mode_transform_card   : return r.bt != BodyType::count;
        case mode_transform_weight : return r.normal();
        case mode_transform_dynamic: return r.normal() || transformNoAux(r) == false;
        default:
            POTASSCO_ASSERT(mode == mode_transform_integ || mode == mode_transform_scc || mode == mode_transform_nhcf,
                            "unhandled extended rule mode");
            return true;
    }
}

bool LogicProgram::transformNoAux(const Rule& r) {
    return r.ht == HeadType::disjunctive && r.sum() &&
           (r.agg.bound == 1 ||
            (r.agg.lits.size() <= 6 && choose(size32(r.agg.lits), static_cast<unsigned>(r.agg.bound)) <= 15));
}

void LogicProgram::transformExtended() {
    uint32_t      a = numAtoms();
    RuleTransform tm(*this);
    for (const auto* rb : extended_) {
        Rule r = rb->rule();
        upStat(r.ht, -1);
        upStat(r.bt, -1);
        if (r.normal() || (r.ht == HeadType::disjunctive && r.head.size() < 2)) {
            tm.transform(r);
        }
        else {
            using Potassco::Lit_t;
            Atom_t aux   = newAtom();
            Lit_t  auxB  = Potassco::lit(aux);
            Rule   rAux1 = r; // aux :- body
            rAux1.ht     = HeadType::disjunctive;
            rAux1.head   = Potassco::toSpan(aux);
            Rule rAux2   = Rule::normal(r.ht, r.head, Potassco::toSpan(auxB)); // head :- auxB
            if (handleNatively(rAux1)) {
                addRule(rAux1);
            }
            else {
                auto st = transformNoAux(rAux1) ? RuleTransform::strategy_no_aux : RuleTransform::strategy_default;
                tm.transform(rAux1, st);
            }
            if (handleNatively(rAux2)) {
                addRule(rAux2);
            }
            else {
                tm.transform(rAux2);
            }
        }
        delete rb;
    }
    extended_.clear();
    incTrAux(numAtoms() - a);
}

void LogicProgram::transformIntegrity(uint32_t nAtoms, uint32_t maxAux) {
    if (stats.bodies[1][to_underlying(BodyType::count)] == 0) {
        return;
    }
    // find all constraint rules that are integrity constraints
    BodyList integrity;
    for (auto* b : bodies_) {
        if (b->relevant() && b->type() == BodyType::count && b->value() == value_false) {
            integrity.push_back(b);
        }
    }
    if (not integrity.empty() && (integrity.size() == 1 || (ratio(nAtoms, size32(bodies_)) > 0.5 &&
                                                            ratio(integrity.size(), size32(bodies_)) < 0.01))) {
        auto          aux = size32(atoms_);
        RuleTransform tr(*this);
        RuleBuilder   temp;
        // transform integrity constraints
        for (auto* b : integrity) {
            auto est = static_cast<uint32_t>(b->bound() * (b->sumW() - b->bound()));
            if (est > maxAux) {
                // reached limit on aux atoms - stop transformation
                break;
            }
            if (b->toData(*this, temp) && temp.bodyType() != BodyType::normal) {
                maxAux -= est;
                // transform rule
                setFrozen(false);
                upStat(HeadType::disjunctive, -1);
                upStat(BodyType::count, -1);
                tr.transform(Rule::sum(HeadType::disjunctive, {}, temp.sum()));
                setFrozen(true);
                // propagate integrity condition to new rules
                propagate(true);
                b->markRemoved();
            }
            temp.clear();
        }
        // create vars for new atoms/bodies
        for (auto* a : atoms(aux)) {
            for (auto s : a->supports()) {
                PrgBody* nb = bodies_[s.node()];
                POTASSCO_ASSERT(nb->value() != value_false);
                nb->assignVar(*this);
            }
            a->assignVar(*this, a->support());
        }
        incTrAux(size32(atoms_) - aux);
    }
}

void LogicProgram::prepareExternals() {
    if (auxData_->external.empty()) {
        return;
    }
    VarVec& external = auxData_->external;
    auto    j        = external.begin();
    for (auto ext : external) {
        Atom_t         id   = getRootId(decodeExternal(ext).first);
        const PrgAtom* atom = getAtom(id);
        if (not atomState_.inHead(id) && not atom->support()) {
            auto value = atom->numSupports() == 0 ? static_cast<Potassco::TruthValue>(atom->freezeValue())
                                                  : Potassco::TruthValue::release;
            atomState_.addToHead(id);
            *j++ = encodeExternal(id, value);
        }
    }
    external.erase(j, external.end());
    atomState_.clearRule(external, [](unsigned ext) { return decodeExternal(ext).first; });
}
void LogicProgram::updateFrozenAtoms() {
    if (frozen_.empty()) {
        return;
    }
    PrgBody* support = nullptr;
    auto     j       = frozen_.begin();
    for (auto f : frozen_) {
        Id_t     id = getRootId(f);
        PrgAtom* a  = getAtom(id);
        POTASSCO_ASSERT(a->frozen());
        a->resetId(id, false);
        if (a->numSupports() == 0) {
            POTASSCO_ASSERT(a->relevant());
            POTASSCO_CHECK_PRE(id < startAuxAtom(), "frozen atom shall be an input atom");
            if (not support) {
                support = getTrueBody();
            }
            a->setIgnoreScc(true);
            support->addHead(a, PrgEdge::gamma_choice);
            *j++ = id; // still frozen
        }
        else {
            a->clearFrozen();
            if (not a->support()) {
                // remove dummy edge added in unfreeze()
                a->removeSupport(PrgEdge::noEdge());
            }
            if (isOld(id) && incData_) {
                // add to unfreeze so that we can later perform completion
                incData_->unfreeze.push_back(id);
            }
        }
    }
    frozen_.erase(j, frozen_.end());
}

void LogicProgram::prepareProgram(bool checkSccs) {
    POTASSCO_ASSERT(not frozen());
    prepareExternals();
    // Given that freezeTheory() might introduce otherwise
    // unused atoms, it must be called before we fix the
    // number of input atoms. It must also be called before resetting
    // the initial "upper" closure so that we can correctly classify
    // theory atoms.
    freezeTheory();
    // Prepare for preprocessing by resetting our "upper" closure.
    for (auto* atom : newAtoms()) { atom->setInUpper(false); }
    uint32_t nAtoms  = (input_.hi = std::min(input_.hi, endAtom()));
    stats.auxAtoms  += endAtom() - nAtoms;
    for (auto i : irange(RuleStats::numKeys())) { stats.rules[1][i] += stats.rules[0][i]; }
    for (auto i : irange(BodyStats::numKeys())) { stats.bodies[1][i] += stats.bodies[0][i]; }
    statsId_ = 1;
    transformExtended();
    updateFrozenAtoms();
    PrgAtom* suppAtom = nullptr;
    if (opts_.suppMod) {
        VarVec h;
        suppAtom = getAtom(newAtom());
        h.assign(1, suppAtom->id());
        addRule(HeadType::choice, h, {});
        auto body = Potassco::lit(suppAtom->id());
        h.clear();
        for (Atom_t v : irange(startAtom(), suppAtom->id())) {
            if (atoms_[v]->numSupports()) {
                h.push_back(v);
            }
        }
        addRule(HeadType::choice, h, Potassco::toSpan(body));
    }
    setFrozen(true);
    Preprocessor p;
    if (hasConflict() || not propagate(true) ||
        not p.preprocess(*this, opts_.iters != 0 ? Preprocessor::full_eq : Preprocessor::no_eq, opts_.iters,
                         opts_.dfOrder != 0)) {
        setConflict();
        return;
    }
    if (suppAtom && (not assignValue(suppAtom, value_false, PrgEdge::noEdge()) || not propagate(true))) {
        setConflict();
        return;
    }
    if (opts_.erMode == mode_transform_integ || opts_.erMode == mode_transform_dynamic) {
        nAtoms -= startAtom();
        transformIntegrity(nAtoms, std::min(15000u, nAtoms * 2));
    }
    addMinimize();
    uint32_t sccs = 0;
    if (checkSccs) {
        uint32_t   startScc = incData_ ? incData_->startScc : 0;
        SccChecker c(*this, auxData_->scc, startScc);
        sccs       = c.sccs();
        stats.sccs = (sccs - startScc);
        if (incData_) {
            incData_->startScc = c.sccs();
        }
        if (not disjunctions_.empty() || (opts_.erMode == mode_transform_scc && sccs)) {
            // reset node ids changed by scc checking
            for (auto i : irange(bodies_)) {
                if (auto* b = getBody(i); b->relevant()) {
                    b->resetId(i, true);
                }
            }
            for (auto i : irange(atoms_)) {
                if (auto* a = getAtom(i); a->relevant()) {
                    a->resetId(i, true);
                }
            }
        }
    }
    else {
        stats.sccs = PrgNode::no_scc;
    }
    finalizeDisjunctions(p, sccs);
    prepareComponents();
    prepareOutputTable();
    freezeAssumptions();
    if (incData_ && index_->distTrue) {
        for (auto end = startAuxAtom(); auto a : irange(startAtom(), end)) {
            if (isSentinel(getRootAtom(a)->literal())) {
                Incremental::StepTrue t(end - 1, 0);
                if (not incData_->steps.empty()) {
                    t.second = ctx()->addVar(VarType::atom, 0);
                }
                incData_->steps.push_back(t);
                break;
            }
        }
    }
    theory_.filter([this](const Potassco::TheoryAtom& a) {
        Atom_t id = a.atom();
        if (getLiteral(id) != lit_false && getRootAtom(id)->value() != value_false) {
            ctx()->setFrozen(getLiteral(id).var(), true);
            return false;
        }
        PrgAtom* at = getRootAtom(id);
        return not at->frozen();
    });
    stats.atoms = size32(atoms_) - startAtom();
    index_->body.clear();
    index_->disj.clear();
}
void LogicProgram::freezeTheory() {
    const IdSet& skippedHeads = auxData_->skippedHeads;
    for (const auto* a : theory_.currAtoms()) {
        if (isFact(a->atom()) || isOld(a->atom())) {
            continue;
        }
        PrgAtom* atom    = resize(a->atom());
        bool     inUpper = atom->inUpper() || skippedHeads.contains(a->atom());
        if (not atom->frozen() && atom->numSupports() == 0 && atom->relevant() && not inUpper) {
            pushFrozen(atom, value_free);
        }
    }
}

POTASSCO_WARNING_PUSH()
POTASSCO_WARNING_IGNORE_GNU("-Wnon-virtual-dtor") // Base class dtor is protected and therefore non-virtual is safe.
struct LogicProgram::DlpTr final : RuleTransform::ProgramAdapter {
    DlpTr(LogicProgram* x, EdgeType et) : self(x), type(et), scc(PrgNode::no_scc) {}
    Atom_t newAtom() override {
        Atom_t   x = self->newAtom();
        PrgAtom* a = self->getAtom(x);
        a->setScc(scc);
        a->setSeen(true);
        atoms.push_back(x);
        if (scc != PrgNode::no_scc) {
            self->auxData_->scc.push_back(a);
        }
        return x;
    }
    void addRule(const Rule& r) override {
        SRule meta;
        if (not self->simplifyRule(r, rule, meta)) {
            return;
        }
        bool     gamma = type == PrgEdge::gamma;
        Rule     rs    = rule.rule();
        PrgAtom* a     = self->getAtom(rs.head[0]);
        PrgBody* body  = self->assignBodyFor(rs, meta, type, gamma);
        if (body->value() != value_false && not body->hasHead(a, PrgEdge::normal)) {
            body->addHead(a, type);
            self->stats.gammas += static_cast<uint32_t>(gamma);
        }
    }
    void assignAuxAtoms() {
        self->incTrAux(size32(atoms));
        while (not atoms.empty()) {
            PrgAtom* ax = self->getAtom(atoms.back());
            atoms.pop_back();
            if (auto s = ax->support(); s) {
                ax->setInUpper(true);
                ax->assignVar(*self, s);
            }
            else {
                POTASSCO_ASSERT(ax->numSupports() == 0);
                self->assignValue(ax, value_false, s);
            }
        }
    }
    LogicProgram* self;
    EdgeType      type;
    uint32_t      scc;
    VarVec        atoms;
    RuleBuilder   rule;
};
POTASSCO_WARNING_POP()

// replace disjunctions with gamma (shifted) and delta (component-shifted) rules
void LogicProgram::finalizeDisjunctions(Preprocessor& p, uint32_t numSccs) {
    if (disjunctions_.empty()) {
        return;
    }
    VarVec   head;
    BodyList supports;
    index_->disj.clear();
    SccMap sccMap;
    sccMap.resize(numSccs, 0);
    enum SccFlag : uint32_t { seen_scc = 1u, is_scc_non_hcf = 128u };
    // replace disjunctions with shifted rules and non-hcf-disjunctions
    DisjList disj;
    disj.swap(disjunctions_);
    setFrozen(false);
    uint32_t shifted     = 0;
    stats.nonHcfs        = size32(nonHcfs_);
    Literal          bot = lit_false;
    Potassco::LitVec rb;
    VarVec           rh;
    DlpTr            tr(this, PrgEdge::gamma);

    // detach disjunctions
    for (uint32_t id : irange(disj)) {
        PrgDisj* d = disj[id];
        d->resetId(id, true);    // id changed during scc checking
        d->detach(*this, false); // remove from atoms and bodies but keep state
    }

    // replace disjunctions with shifted rules or new component-shifted disjunction
    for (auto* d : disj) {
        Literal dx = d->inUpper() ? d->literal() : bot;
        head.clear();
        supports.clear();
        for (auto aId : d->atoms()) {
            PrgAtom* at = getAtom(aId);
            if (dx == bot) {
                continue;
            }
            if (at->eq()) {
                at = getAtom(aId = getRootId(aId));
            }
            if (isFact(at)) {
                dx = bot;
                continue;
            }
            if (at->inUpper()) {
                head.push_back(aId);
                if (at->scc() != PrgNode::no_scc) {
                    sccMap[at->scc()] = seen_scc;
                }
            }
        }
        EdgeVec temp;
        d->clearSupports(temp);
        for (auto edge : temp) {
            PrgBody* b = getBody(edge.node());
            if (b->relevant() && b->value() != value_false) {
                supports.push_back(b);
            }
        }
        d->destroy();
        // create shortcut for supports to avoid duplications during shifting
        Literal supportLit = dx != bot ? getEqAtomLit(dx, supports, p, sccMap) : dx;
        // create shifted rules and split disjunctions into non-hcf components
        RuleTransform shifter(tr);
        for (auto h : head) {
            uint32_t scc = getAtom(h)->scc();
            if (scc == PrgNode::no_scc || (sccMap[scc] & seen_scc) != 0) {
                if (scc != PrgNode::no_scc) {
                    sccMap[scc] &= ~seen_scc;
                }
                else {
                    scc = UINT32_MAX;
                }
                rh.assign(1, h);
                rb.clear();
                if (supportLit.var() != 0) {
                    rb.push_back(toInt(supportLit));
                }
                else if (supportLit.sign()) {
                    continue;
                }
                for (auto o : head) {
                    if (o != h) {
                        if (getAtom(o)->scc() == scc) {
                            rh.push_back(o);
                        }
                        else {
                            rb.push_back(Potassco::neg(o));
                        }
                    }
                }
                SRule meta;
                if (not simplifyRule(Rule::normal(HeadType::disjunctive, rh, rb), rule_, meta)) {
                    continue;
                }
                Rule     sr   = rule_.rule();
                PrgBody* body = assignBodyFor(sr, meta, PrgEdge::normal, true);
                if (body->value() != value_false && sr.head.size() == 1) {
                    ++shifted;
                    body->addHead(getAtom(sr.head[0]), PrgEdge::normal);
                }
                else if (body->value() != value_false && sr.head.size() > 1) {
                    PrgDisj* x = getDisjFor(sr.head, 0);
                    body->addHead(x, PrgEdge::normal);
                    x->assignVar(*this, x->support());
                    x->setInUpper(true);
                    x->setSeen(true);
                    if ((sccMap[scc] & is_scc_non_hcf) == 0) {
                        sccMap[scc] |= is_scc_non_hcf;
                        nonHcfs_.add(scc);
                    }
                    if (not options().noGamma) {
                        if (sr.cond.size() >= 4) {
                            // make body eq to a new aux atom
                            tr.scc        = body->scc(*this) == scc ? scc : PrgNode::no_scc;
                            Atom_t eqAtom = tr.newAtom();
                            body->addHead(getAtom(eqAtom), PrgEdge::normal);
                            rb.assign(1, Potassco::lit(eqAtom));
                            sr.cond = rb;
                            tr.assignAuxAtoms();
                            tr.scc = PrgNode::no_scc;
                        }
                        shifter.transform(sr, RuleTransform::strategy_no_aux);
                    }
                    else {
                        // only add support edge
                        for (auto a : x->atoms()) { body->addHead(getAtom(a), PrgEdge::gamma_choice); }
                    }
                }
            }
        }
    }
    POTASSCO_ASSERT(tr.atoms.empty());
    if (not disjunctions_.empty() && nonHcfs_.config == nullptr) {
        nonHcfs_.config = ctx()->configuration()->config("tester");
    }
    upStat(RK(normal), static_cast<int>(shifted));
    stats.nonHcfs = size32(nonHcfs_) - stats.nonHcfs;
    rh.clear();
    setFrozen(true);
}
// optionally transform extended rules in sccs
void LogicProgram::prepareComponents() {
    int trRec = opts_.erMode == mode_transform_scc;
    // HACK: force transformation of extended rules in non-hcf components
    // REMOVE this once minimality check supports aggregates
    if (not disjunctions_.empty() && trRec != 1) {
        trRec = 2;
    }
    if (trRec != 0) {
        DlpTr         tr(this, PrgEdge::normal);
        RuleTransform trans(tr);
        RuleBuilder   temp;
        setFrozen(false);
        EdgeVec heads;
        // find recursive aggregates
        for (auto bId : irange(numBodies())) { // NOTE: set of bodies might change
            PrgBody* body = getBody(bId);
            if (body->type() == BodyType::normal || not body->hasVar() || body->value() == value_false) {
                continue;
            } // not aggregate or not relevant
            tr.scc = body->scc(*this);
            if (tr.scc == PrgNode::no_scc || (trRec == 2 && not nonHcfs_.find(tr.scc))) {
                continue;
            } // not recursive
            // transform all rules a :- B, where scc(a) == scc(B):
            heads.clear();
            for (auto h : body->heads()) {
                POTASSCO_ASSERT(h.isAtom());
                if (getAtom(h.node())->scc() == tr.scc) {
                    heads.push_back(h);
                }
            }
            if (heads.empty()) {
                continue;
            }
            temp.clear();
            if (not body->toData(*this, temp) || temp.bodyType() == BodyType::normal) {
                body->simplify(*this, true, nullptr);
                continue;
            }
            HeadType ht = not isChoice(heads[0].type()) ? HeadType::disjunctive : HeadType::choice;
            Atom_t   h  = heads[0].node();
            if (heads.size() > 1) { // more than one head, make body eq to some new aux atom
                ht = HeadType::disjunctive;
                h  = tr.newAtom();
            }
            trans.transform(Rule::sum(ht, Potassco::toSpan(h), temp.sum()));
            temp.clearBody().addGoal(Potassco::lit(h));
            for (auto head : heads) {
                body->removeHead(getAtom(head.node()), head.type());
                if (h != head.node()) {
                    ht      = not isChoice(head.type()) ? HeadType::disjunctive : HeadType::choice;
                    h       = head.node();
                    tr.type = ht == HeadType::disjunctive ? PrgEdge::normal : PrgEdge::choice;
                    tr.addRule(Rule::normal(ht, Potassco::toSpan(h), temp.body()));
                }
            }
        }
        tr.assignAuxAtoms();
        setFrozen(true);
    }
}

void LogicProgram::mergeOutput(VarVec::iterator& hint, Atom_t atom, OutputState state) {
    if (not index_->outState) {
        return; // not enabled
    }
    Var_t key = atom << 2u;
    if (hint == index_->outSet.end() || key < (*hint & ~3u)) {
        hint = index_->outSet.begin();
    }
    hint = std::lower_bound(hint, index_->outSet.end(), key);
    if (hint == index_->outSet.end() || (*hint & ~3u) != key) {
        hint = index_->outSet.insert(hint, key | state);
    }
    else {
        *hint |= state;
    }
}
void LogicProgram::addOutputState(Atom_t atom, OutputState state) {
    auto outPos = index_->outSet.end();
    mergeOutput(outPos, atom, state);
}

void LogicProgram::prepareOutputTable() {
    OutputTable& out    = ctx()->output;
    auto         outPos = index_->outSet.end();
    // add new output predicates in program order to output table
    std::ranges::stable_sort(show_.begin(), show_.end(), std::less{}, [](const ShowPair& p) { return p.first; });
    for (const auto& [id, name] : show_) {
        Literal lit    = getLiteral(id);
        bool    isAtom = id < startAuxAtom();
        if (not isSentinel(lit)) {
            out.add(name, lit, id);
        }
        else if (lit == lit_true) {
            out.add(name);
        }
        if (isAtom) {
            ctx()->setOutput(lit.var(), true);
            mergeOutput(outPos, id, out_shown);
        }
    }
    std::ranges::sort(auxData_->project);
    for (auto p : auxData_->project) {
        out.addProject(getLiteral(p));
        mergeOutput(outPos, p, out_projected);
    }
}

// Make assumptions/externals exempt from sat-preprocessing
void LogicProgram::freezeAssumptions() {
    for (auto a : frozen_) { ctx()->setFrozen(getRootAtom(a)->var(), true); }
    for (auto l : assume_) { ctx()->setFrozen(getLiteral(Asp::id(l)).var(), true); }
}

// add (completion) nogoods
bool LogicProgram::addConstraints() {
    ClauseCreator gc(ctx()->master());
    if (options().iters == 0) {
        gc.addDefaultFlags(ClauseCreator::clause_force_simplify);
    }
    ctx()->startAddConstraints();
    // handle initial conflict, if any
    if (not ctx()->ok() || not ctx()->addUnary(getTrueAtom()->trueLit())) {
        return false;
    }
    if (incData_ && not incData_->steps.empty() && not ctx()->addUnary(posLit(incData_->steps.back().second))) {
        return false;
    }
    if (options().noGamma && not disjunctions_.empty()) {
        // add "rule" nogoods for disjunctions
        for (const auto* disjunction : disjunctions_) {
            gc.start().add(~disjunction->literal());
            for (auto a : disjunction->atoms()) { gc.add(getAtom(a)->literal()); }
            if (not gc.end()) {
                return false;
            }
        }
    }
    // add bodies from this step
    for (auto* body : bodies_) {
        if (not toConstraint(body, *this, gc)) {
            return false;
        }
    }
    // add atoms thawed in this step
    for (auto u : unfreeze()) {
        if (not toConstraint(getAtom(u), *this, gc)) {
            return false;
        }
    }
    // add atoms from this step
    const bool     freezeAll = incData_ != nullptr;
    const uint32_t hiAtom    = startAuxAtom();
    for (uint32_t id = startAtom(); auto* a : atoms(id)) {
        if (not toConstraint(a, *this, gc)) {
            return false;
        }
        if (id < hiAtom && a->hasVar()) {
            if (freezeAll) {
                ctx()->setFrozen(a->var(), true);
            }
            ctx()->setInput(a->var(), true);
        }
        ++id;
    }
    if (not auxData_->scc.empty()) {
        if (not ctx()->sccGraph) {
            ctx()->sccGraph = std::make_unique<PrgDepGraph>(static_cast<PrgDepGraph::NonHcfMapType>(opts_.oldMap == 0));
        }
        uint32_t oldNodes = ctx()->sccGraph->nodes();
        ctx()->sccGraph->addSccs(*this, auxData_->scc, nonHcfs_);
        stats.ufsNodes = ctx()->sccGraph->nodes() - oldNodes;
    }
    return true;
}
void LogicProgram::addDomRules() {
    if (auxData_->dom.empty()) {
        return;
    }
    VarVec        domVec;
    EqVec         eqVec;
    DomRules&     doms = auxData_->dom;
    Solver const& s    = *ctx()->master();
    // mark any previous domain atoms so that we can decide
    // whether existing variables can be used for the atoms in doms
    if (incData_) {
        domVec.swap(incData_->doms);
        for (auto v : domVec) {
            if (s.value(v) == value_free) {
                ctx()->mark(posLit(v));
            }
        }
    }
    DomRule r{};
    auto    j = doms.begin();
    for (auto& dr : doms) {
        Literal cond = getLiteral(dr.cond);
        Literal slit = getLiteral(dr.atom);
        auto    svar = slit.var();
        if (s.isFalse(cond) || s.value(svar) != value_free) {
            continue;
        }
        if (s.isTrue(cond)) {
            dr.cond = 0;
            cond    = lit_true;
        }
        // check if atom is the root for its var
        if (not atomState_.isSet(dr.atom, AtomState::dom_flag)) {
            if (not ctx()->marked(posLit(svar))) {
                // var(it->atom) is not yet used - make it->atom its root
                ctx()->mark(posLit(svar));
                atomState_.set(dr.atom, AtomState::dom_flag);
                domVec.push_back(svar);
            }
            else if (auto eq = index_->domEq.find(dr.atom); eq != index_->domEq.end()) {
                // var(it->atom) is used but we already created a new var for it->atom
                slit = posLit(svar = eq->second);
            }
            else {
                // var(it->atom) is used - introduce new aux var and make it eq to lit(atom)
                Eq n = {ctx()->addVar(VarType::atom, VarInfo::flag_nant), slit};
                eqVec.push_back(n);
                svar = n.var;
                slit = posLit(svar);
                index_->domEq.emplace(static_cast<uint32_t>(dr.atom), svar);
            }
        }
        *j++ = (r = dr);
        if (slit.sign()) {
            if (auto mod = static_cast<DomModType>(r.type); mod == DomModType::sign) {
                r.bias = static_cast<int16_t>(r.bias != 0 ? -r.bias : 0);
            }
            else if (mod == DomModType::true_) {
                r.type = +DomModType::false_;
            }
            else if (mod == DomModType::false_) {
                r.type = +DomModType::true_;
            }
        }
        ctx()->heuristic.add(svar, static_cast<DomModType>(r.type), r.bias, r.prio, cond);
    }
    if (j != doms.end()) {
        upStat(RK(heuristic), -static_cast<int>(doms.end() - j));
        doms.erase(j, doms.end());
    }
    // cleanup var flags
    for (auto v : domVec) { ctx()->unmark(v); }
    if (incData_) {
        incData_->doms.swap(domVec);
    }
    if (not eqVec.empty()) {
        ctx()->startAddConstraints();
        for (const auto& [var, lit] : eqVec) {
            // var == lit
            ctx()->addBinary(~lit, posLit(var));
            ctx()->addBinary(lit, negLit(var));
        }
    }
}

void LogicProgram::addAcycConstraint() {
    AcycRules& acyc = auxData_->acyc;
    if (acyc.empty()) {
        return;
    }
    SharedContext& ctx = *this->ctx();
    const Solver&  s   = *ctx.master();
    if (ctx.extGraph) {
        ctx.extGraph->update();
    }
    else {
        ctx.extGraph = std::make_unique<ExtDepGraph>();
    }
    auto* graph = ctx.extGraph.get();
    for (auto x : acyc) {
        if (auto lit = getLiteral(x.cond); not s.isFalse(lit)) {
            graph->addEdge(lit, x.node[0], x.node[1]);
        }
        else {
            upStat(RK(acyc), -1);
        }
    }
    if (graph->finalize(ctx) == 0) {
        ctx.extGraph = nullptr;
    }
}
#undef CHECK_MODULAR
/////////////////////////////////////////////////////////////////////////////////////////
// misc/helper functions
/////////////////////////////////////////////////////////////////////////////////////////
PrgAtom* LogicProgram::resize(Atom_t atomId) {
    POTASSCO_CHECK(atomId < body_id, EOVERFLOW, "Atom out of bounds");
    while (size32(atoms_) <= atomId) { newAtom(); }
    return getRootAtom(atomId);
}
void LogicProgram::setConflict() {
    POTASSCO_ASSERT(started());
    getTrueAtom()->setLiteral(lit_false);
}
bool LogicProgram::propagate(bool backprop) {
    POTASSCO_ASSERT(frozen());
    bool oldB      = opts_.backprop != 0;
    opts_.backprop = backprop;
    for (auto qFront = static_cast<std::size_t>(0); qFront < propQ_.size();) {
        PrgAtom* a = getAtom(propQ_[qFront++]);
        if (not a->relevant()) {
            continue;
        }
        if (not a->propagateValue(*this, backprop)) {
            setConflict();
            return false;
        }
        if (a->hasVar() && a->id() < startAtom() && not ctx()->addUnary(a->trueLit())) {
            setConflict();
            return false;
        }
    }
    opts_.backprop = oldB;
    propQ_.clear();
    return true;
}
Val_t LogicProgram::litVal(const PrgAtom* a, bool pos) {
    if (a->value() != value_free || not a->relevant()) {
        if (bool vSign = a->value() == value_false || not a->relevant(); vSign == pos) {
            return value_false;
        }
        return a->value() != value_weak_true ? value_true : value_free;
    }
    return value_free;
}

// Simplifies the given normal rule H :- l1, ..., ln
//  - removes true and duplicate literals from body: {T,a,b,a} -> {a, b}.
//  - checks for contradictions and false literals in body: {'a', not 'a'} -> F
//  - checks for satisfied head and removes false atoms from head
// POST: if true out contains the simplified normal rule.
bool LogicProgram::simplifyNormal(HeadType ht, Potassco::AtomSpan head, Potassco::LitSpan body, RuleBuilder& out,
                                  SRule& meta) {
    out.clear();
    out.startBody();
    meta    = SRule();
    bool ok = true;
    for (auto lit : body) {
        auto* a = resize(Potassco::atom(lit));
        auto  p = Literal(a->id(), lit < 0); // replace any eq atoms
        auto  v = litVal(a, not p.sign());
        if (v == value_false || atomState_.inBody(~p)) {
            ok = false;
            break;
        }
        if (v != value_true && not atomState_.inBody(p)) {
            atomState_.addToBody(p);
            out.addGoal(toInt(p));
            meta.pos  += not p.sign();
            meta.hash += hashLit(p);
        }
    }
    meta.bid = ok ? findBody(meta.hash, size32(out.body())) : var_max;
    ok       = ok && pushHead(ht, head, 0, out);
    atomState_.clearRule(out.body());
    return ok;
}

// Simplifies the given sum rule: H :- lb { l1 = w1 ... ln = wn }.
//  - removes assigned literals and updates lb accordingly
//  - removes literals li with weight wi = 0
//  - reduces weights wi > bound() to bound
//  - merges duplicate literals in sum, i.e. lb {a=w1, b=w2, a=w3} -> lb {a=w1+w3, b=w2}
//  - checks for contradiction, i.e. sum contains both p and not p and both are needed
//  - replaces sum with count if all weights are equal
//  - replaces sum with normal body if all literals must be true for the sum to be satisfied
// POST: if true out contains the simplified rule.
bool LogicProgram::simplifySum(HeadType ht, Potassco::AtomSpan head, const Potassco::Sum& body, RuleBuilder& out,
                               SRule& meta) {
    meta           = SRule();
    Weight_t bound = body.bound, maxW = 1, minW = weight_max, sumW = 0, dirty = 0;
    out.clear();
    out.startSum(bound);
    for (const auto& [lit, weight] : body.lits) {
        if (bound <= 0) {
            break;
        }
        if (weight <= 0) {
            POTASSCO_CHECK(weight == 0, EDOM, "Non-negative weight expected!");
            continue; // skip irrelevant lits
        }
        auto* a = resize(Potassco::atom(lit));
        auto  p = Literal(a->id(), lit < 0); // replace any eq atoms
        if (auto v = litVal(a, not p.sign()); v == value_true) {
            bound -= weight;
        }
        else if (v != value_false) {
            POTASSCO_CHECK((weight_max - sumW) >= weight, EOVERFLOW, "Integer overflow!");
            sumW   += weight;
            auto w  = weight;
            if (not atomState_.inBody(p)) {
                atomState_.addToBody(p);
                out.addGoal(toInt(p), weight);
                meta.pos  += not p.sign();
                meta.hash += hashLit(p);
            }
            else { // Merge duplicate lits
                auto* pos = out.findSumLit(toInt(p));
                POTASSCO_ASSERT(pos);
                w = (pos->weight += weight);
                ++dirty; // minW might have changed
            }
            if (w > maxW) {
                maxW = w;
            }
            if (w < minW) {
                minW = w;
            }
            dirty += static_cast<Weight_t>(atomState_.inBody(~p));
        }
    }
    Weight_t sumR = sumW;
    if (bound > 0 && (dirty || maxW > bound)) {
        sumR = 0, minW = weight_max;
        for (auto& [lit, weight] : out.sumLits()) {
            if (weight > bound) {
                sumW   -= (weight - bound);
                weight  = (maxW = bound);
            }
            if (weight < minW) {
                minW = weight;
            }
            if (not atomState_.inBody(~toLit(lit))) {
                sumR += weight;
            }
            else if (lit > 0) { // body contains lit and ~lit: we can achieve at most max(weight(lit), weight(~lit))
                auto cpw  = out.findSumLit(Potassco::neg(lit))->weight;
                sumR     += std::max(weight, std::min(cpw, bound));
            }
        }
    }
    out.setBound(bound);
    if (bound <= 0 || sumR < bound) {
        atomState_.clearRule(out.sumLits());
        return bound <= 0 && simplifyNormal(ht, head, {}, out, meta);
    }
    if ((sumW - minW) < bound) {
        out.weaken(BodyType::normal);
        meta.bid = findBody(meta.hash, size32(out.body()));
        bool ok  = pushHead(ht, head, 0, out);
        atomState_.clearRule(out.body());
        return ok;
    }
    if (minW == maxW) {
        out.weaken(BodyType::count, maxW != 1);
        bound = out.bound();
    }
    meta.bid = findBody(meta.hash, out.bodyType(), out.bound(), out.sumLits());
    bool ok  = pushHead(ht, head, sumW - out.bound(), out);
    atomState_.clearRule(out.sumLits());
    return ok;
}

// Pushes the given rule head to the body given in out.
// Pre: Body literals are marked and lits is != 0 if body is a sum.
bool LogicProgram::pushHead(HeadType ht, Potassco::AtomSpan head, Weight_t slack, RuleBuilder& out) {
    constexpr uint8_t ignoreMask = AtomState::false_flag | AtomState::head_flag;
    bool              sat = false, sum = out.bodyType() == BodyType::sum;
    out.start(ht);
    for (auto h : head) {
        if (not atomState_.isSet(h, AtomState::simp_mask)) {
            out.addHead(h);
            atomState_.addToHead(h);
        }
        else if (not atomState_.isSet(h, ignoreMask)) { // h occurs in B+ and/or B- or is true
            auto wp = static_cast<Weight_t>(atomState_.inBody(posLit(h))),
                 wn = static_cast<Weight_t>(atomState_.inBody(negLit(h)));
            if (wp && sum) {
                wp = out.findSumLit(Potassco::lit(h))->weight;
            }
            if (wn && sum) {
                wn = out.findSumLit(Potassco::neg(h))->weight;
            }
            if (atomState_.isFact(h) || wp > slack) {
                sat = true;
            }
            else if (wn <= slack) {
                out.addHead(h);
                atomState_.addToHead(h);
            }
        }
    }
    atomState_.clearRule(out.head());
    return not sat || (ht == HeadType::choice && not out.head().empty());
}

bool LogicProgram::simplifyRule(const Rule& r, Potassco::RuleBuilder& out, SRule& meta) {
    return r.normal() ? simplifyNormal(r.ht, r.head, r.cond, out, meta) : simplifySum(r.ht, r.head, r.agg, out, meta);
}
// create new atom aux representing supports, i.e.
// aux == S1 v ... v Sn
Literal LogicProgram::getEqAtomLit(Literal lit, const BodyList& supports, Preprocessor& p, const SccMap& sccMap) {
    if (supports.empty() || lit == lit_false) {
        return lit_false;
    }
    if (supports.size() == 1 && supports[0]->size() < 2 && supports.back()->literal() == lit) {
        return supports[0]->size() == 0 ? lit_true : supports[0]->goal(0);
    }
    if (p.getRootAtom(lit) != var_max && opts_.noSCC) {
        // Use existing root atom only if scc checking is disabled.
        // Otherwise, we would have to recheck SCCs from that atom again because
        // adding a new edge could create a new or change an existing SCC.
        return posLit(p.getRootAtom(lit));
    }
    incTrAux(1);
    Atom_t   auxV = newAtom();
    PrgAtom* aux  = getAtom(auxV);
    aux->setLiteral(lit);
    aux->setSeen(true);
    if (p.getRootAtom(lit) == var_max) {
        p.setRootAtom(aux->literal(), auxV);
    }
    uint32_t scc = PrgNode::no_scc;
    for (auto* b : supports) {
        if (b->relevant() && b->value() != value_false) {
            for (uint32_t g = 0; scc == PrgNode::no_scc && g != b->size() && not b->goal(g).sign(); ++g) {
                uint32_t aScc = getAtom(b->goal(g).var())->scc();
                if (aScc != PrgNode::no_scc && (sccMap[aScc] & 1u)) {
                    scc = aScc;
                }
            }
            b->addHead(aux, PrgEdge::normal);
            if (b->value() != value_free && not assignValue(aux, b->value(), PrgEdge::newEdge(*b, PrgEdge::normal))) {
                break;
            }
            aux->setInUpper(true);
        }
    }
    if (not aux->inUpper()) {
        aux->setValue(value_false);
        return lit_false;
    }
    if (scc != PrgNode::no_scc) {
        aux->setScc(scc);
        auxData_->scc.push_back(aux);
    }
    return posLit(auxV);
}

PrgBody* LogicProgram::getBodyFor(const Rule& r, const SRule& meta, bool addDeps) {
    if (meta.bid < size32(bodies_)) {
        return getBody(meta.bid);
    }
    // no corresponding body exists, create a new object
    PrgBody* b = PrgBody::create(*this, numBodies(), r, meta.pos, addDeps);
    index_->body.emplace(meta.hash, b->id());
    bodies_.push_back(b);
    if (b->isSupported()) {
        initialSupp_.push_back(b->id());
    }
    upStat(r.bt);
    return b;
}
PrgBody* LogicProgram::getTrueBody() {
    if (uint32_t id = findBody(0, 0); validBody(id)) {
        return getBody(id);
    }
    return getBodyFor(Rule::normal(HeadType::choice, {}, {}), SRule());
}
PrgBody* LogicProgram::assignBodyFor(const Rule& r, const SRule& meta, EdgeType depEdge, bool simpStrong) {
    PrgBody* b = getBodyFor(r, meta, depEdge != PrgEdge::gamma);
    if (not b->hasVar() && not b->seen()) {
        uint32_t eqId;
        b->markDirty();
        b->simplify(*this, simpStrong, &eqId);
        if (eqId != b->id()) {
            POTASSCO_ASSERT(b->id() == size32(bodies_) - 1);
            removeBody(b, meta.hash);
            bodies_.pop_back();
            if (depEdge != PrgEdge::gamma) {
                for (auto g : b->goals()) { getAtom(g.var())->removeDep(b->id(), not g.sign()); }
            }
            b->destroy();
            b = bodies_[eqId];
        }
    }
    b->setSeen(true);
    b->assignVar(*this);
    return b;
}

bool LogicProgram::equalLits(const PrgBody& b, WeightLitSpan lits) {
    auto last = lits.begin(), e = lits.end();
    for (auto i : irange(b.size())) {
        Potassco::WeightLit wl = {toInt(b.goal(i)), b.weight(i)};
        if (auto x = wl <=> *last; x == std::strong_ordering::equal) {
            continue;
        }
        else if (x == std::strong_ordering::less) {
            last = std::lower_bound(lits.begin(), e = last, wl);
        }
        else {
            last = std::lower_bound(last + 1, e = lits.end(), wl);
        }
        if (last == e || *last != wl) {
            return false;
        }
    }
    return true;
}

// Pre: all literals in body are marked.
uint32_t LogicProgram::findBody(uint32_t hash, BodyType type, uint32_t size, Weight_t bound,
                                Potassco::WeightLit* sum) const {
    POTASSCO_ASSERT(type != BodyType::normal || bound == static_cast<Weight_t>(size));
    bool sorted = false;
    for (auto [it, end] = index_->body.equal_range(hash); it != end; ++it) {
        const PrgBody& b = *getBody(it->second);
        if (not checkBody(b, type, size, bound) || not atomState_.inBody(b.goals())) {
            continue;
        }
        if (not b.hasWeights()) {
            return b.id();
        }
        if (sum) {
            if (not sorted) {
                std::sort(sum, sum + size);
                sorted = true;
            }
            if (equalLits(b, {sum, size})) {
                return b.id();
            }
        }
    }
    return var_max;
}

uint32_t LogicProgram::findEqBody(const PrgBody* b, uint32_t hash) {
    uint32_t eqId = var_max, n = 0, r = 0;
    for (auto [it, end] = index_->body.equal_range(hash); it != end && eqId == var_max; ++it) {
        const PrgBody& rhs = *getBody(it->second);
        if (not checkBody(rhs, b->type(), b->size(), b->bound())) {
            continue;
        }
        if (b->size() == 0) {
            eqId = rhs.id();
        }
        else if (b->size() == 1) {
            eqId = b->goal(0) == rhs.goal(0) && b->weight(0) == rhs.weight(0) ? rhs.id() : var_max;
        }
        else {
            if (++n == 1) {
                atomState_.addToBody(b->goals());
            }
            if (not atomState_.inBody(rhs.goals())) {
                continue;
            }
            if (not b->hasWeights()) {
                eqId = rhs.id();
            }
            else {
                if (n == 1 || r == 0) {
                    rule_.clear();
                    if (not b->toData(*this, rule_) || rule_.bodyType() != BodyType::sum) {
                        rule_.clear();
                        continue;
                    }
                    r = 1;
                    std::ranges::sort(rule_.sumLits());
                }
                if (equalLits(rhs, rule_.sumLits())) {
                    eqId = rhs.id();
                }
            }
        }
    }
    if (n) {
        rule_.clear();
        atomState_.clearBody(b->goals());
    }
    return eqId;
}

PrgDisj* LogicProgram::getDisjFor(Potassco::AtomSpan head, uint32_t headHash) {
    PrgDisj* d = nullptr;
    if (headHash) {
        for (auto [it, end] = index_->disj.equal_range(headHash); it != end; ++it) {
            PrgDisj& o = *disjunctions_[it->second];
            if (o.relevant() && o.size() == head.size() && atomState_.allMarked(o.atoms(), AtomState::head_flag)) {
                POTASSCO_ASSERT(o.id() == it->second);
                d = &o;
                break;
            }
        }
        atomState_.clearRule(head);
    }
    if (not d) {
        // no corresponding disjunction exists, create a new object
        // and link it to all atoms
        ++stats.disjunctions[statsId_];
        d = PrgDisj::create(size32(disjunctions_), head);
        disjunctions_.push_back(d);
        PrgEdge edge = PrgEdge::newEdge(*d, PrgEdge::choice);
        for (auto h : head) { getAtom(h)->addSupport(edge); }
        if (headHash) {
            index_->disj.emplace(headHash, d->id());
        }
    }
    return d;
}

// body has changed - update index
uint32_t LogicProgram::update(PrgBody* body, uint32_t oldHash, uint32_t newHash) {
    uint32_t id = removeBody(body, oldHash);
    if (body->relevant()) {
        uint32_t eqId = findEqBody(body, newHash);
        if (eqId == var_max) {
            // No equivalent body found.
            // Add new entry to index
            index_->body.emplace(newHash, id);
        }
        return eqId;
    }
    return var_max;
}

// body b has changed - remove old entry from body node index
uint32_t LogicProgram::removeBody(const PrgBody* b, uint32_t oldHash) {
    uint32_t id = b->id();
    for (auto [it, end] = index_->body.equal_range(oldHash); it != end; ++it) {
        if (bodies_[it->second] == b) {
            id = it->second;
            index_->body.erase(it);
            break;
        }
    }
    return id;
}

PrgAtom* LogicProgram::mergeEqAtoms(PrgAtom* a, Id_t rootId) {
    PrgAtom* root = getAtom(rootId = getRootId(rootId));
    auto     mv   = getMergeValue(a, root);
    POTASSCO_ASSERT(not a->eq() && not root->eq() && not a->frozen());
    if (a->ignoreScc()) {
        root->setIgnoreScc(true);
    }
    if (mv != a->value() && not assignValue(a, mv, PrgEdge::noEdge())) {
        return nullptr;
    }
    if (mv != root->value() && not assignValue(root, mv, PrgEdge::noEdge())) {
        return nullptr;
    }
    a->setEq(rootId);
    incEqs(VarType::atom);
    return root;
}

// returns whether posSize(root) <= posSize(body)
bool LogicProgram::positiveLoopSafe(const PrgBody* body, const PrgBody* root) {
    uint32_t i = 0, end = std::min(body->size(), root->size());
    while (i != end && body->goal(i).sign() == root->goal(i).sign()) { ++i; }
    return i == root->size() || root->goal(i).sign();
}

PrgBody* LogicProgram::mergeEqBodies(PrgBody* b, Id_t rootId, bool hashEq, bool atomsAssigned) {
    PrgBody* root = getBody(rootId = getEqNode(bodies_, rootId));
    bool     bp   = options().backprop != 0;
    if (b == root) {
        return root;
    }
    POTASSCO_ASSERT(not b->eq() && not root->eq() && (hashEq || b->literal() == root->literal()));
    if (not b->simplifyHeads(*this, atomsAssigned) ||
        (b->value() != root->value() &&
         (not mergeValue(b, root) || not root->propagateValue(*this, bp) || not b->propagateValue(*this, bp)))) {
        setConflict();
        return nullptr;
    }
    if (hashEq || positiveLoopSafe(b, root)) {
        b->setLiteral(root->literal());
        if (not root->mergeHeads(*this, *b, atomsAssigned, not hashEq)) {
            setConflict();
            return nullptr;
        }
        incEqs(VarType::body);
        b->setEq(rootId);
        return root;
    }
    return b;
}

const char* LogicProgram::findName(Atom_t x) const {
    for (const auto& pred : ctx()->output.pred_range()) {
        if (pred.user == x) {
            return pred.name.c_str();
        }
    }
    auto it = std::ranges::find_if(show_, [x](const auto& sp) { return sp.first == x; });
    return it != show_.end() ? it->second.c_str() : "";
}
VarVec& LogicProgram::getSupportedBodies(bool sorted) {
    if (sorted) {
        std::ranges::stable_sort(initialSupp_, [&](Id_t lhs, Id_t rhs) {
            const auto* bLhs = bodies_[lhs];
            const auto* bRhs = bodies_[rhs];
            return bLhs->size() < bRhs->size() || (bLhs->size() == bRhs->size() && bLhs->type() < bRhs->type());
        });
    }
    return initialSupp_;
}

Atom_t LogicProgram::falseAtom() {
    for (auto i : irange(1u, size32(atoms_))) {
        if (atoms_[i]->value() == value_false || atomState_.isSet(i, AtomState::false_flag)) {
            return i;
        }
    }
    bool s = frozen();
    setFrozen(false);
    auto aFalse = newAtom();
    assignValue(getAtom(aFalse), value_false, PrgEdge::noEdge());
    setFrozen(s);
    return aFalse;
}

bool LogicProgram::extractCondition(Id_t cId, Potassco::LitVec& cond) const {
    cond.clear();
    if (cId == false_id || (frozen() && getLiteral(cId) == lit_false)) {
        return false;
    }
    if (not cId || isAtom(cId)) {
        cond.assign(cId != 0, Potassco::lit(cId));
        return true;
    }
    Id_t bId = nodeId(cId);
    POTASSCO_ASSERT(validBody(bId), "Invalid literal");
    const PrgBody* body = getBody(getEqBody(bId));
    cond.reserve(body->size());
    for (auto g : body->goals()) { cond.push_back(toInt(g)); }
    return true;
}
Val_t isConsequence(const LogicProgram& prg, Potassco::Lit_t atomLit, const Model& model) {
    auto outState = prg.getOutputState(Potassco::atom(atomLit));
    auto expState =
        prg.ctx()->output.projectMode() == ProjectMode::project ? LogicProgram::out_projected : LogicProgram::out_shown;
    if (not Potassco::test(outState, expState)) {
        return value_false;
    }
    return model.isCons(solverLiteral(prg, atomLit));
}
#undef RT
/////////////////////////////////////////////////////////////////////////////////////////
// class LogicProgramAdapter
/////////////////////////////////////////////////////////////////////////////////////////
LogicProgramAdapter::LogicProgramAdapter(LogicProgram& prg, const Options& opts)
    : lp_(&prg)
    , opts_(opts)
    , inc_(false) {}
LogicProgramAdapter::LogicProgramAdapter(LogicProgram& prg) : LogicProgramAdapter(prg, {}) {}
void LogicProgramAdapter::initProgram(bool inc) { inc_ = inc; }
void LogicProgramAdapter::beginStep() {
    if (inc_ || lp_->frozen()) {
        lp_->updateProgram();
    }
}
void LogicProgramAdapter::endStep() {
    if (inc_ && opts_.removeMinimize && lp_->ctx()->hasMinimize()) {
        lp_->ctx()->removeMinimize();
    }
}
void LogicProgramAdapter::rule(HeadType ht, Potassco::AtomSpan head, Potassco::LitSpan body) {
    lp_->addRule(ht, head, body);
}
void LogicProgramAdapter::rule(HeadType ht, Potassco::AtomSpan head, Potassco::Weight_t bound, WeightLitSpan body) {
    lp_->addRule(ht, head, bound, body);
}
void LogicProgramAdapter::minimize(Potassco::Weight_t prio, WeightLitSpan lits) { lp_->addMinimize(prio, lits); }
void LogicProgramAdapter::project(Potassco::AtomSpan atoms) { lp_->addProject(atoms); }
void LogicProgramAdapter::output(std::string_view str, Potassco::LitSpan cond) { lp_->addOutput(str, cond); }
void LogicProgramAdapter::outputAtom(Atom_t atom, const Potassco::ConstString& n) { lp_->addOutput(n, atom); }
void LogicProgramAdapter::external(Atom_t a, Potassco::TruthValue v) { lp_->addExternal(a, v); }
void LogicProgramAdapter::assume(Potassco::LitSpan lits) { lp_->addAssumption(lits); }
void LogicProgramAdapter::heuristic(Atom_t a, Potassco::DomModifier t, int bias, unsigned prio,
                                    Potassco::LitSpan cond) {
    lp_->addDomHeuristic(a, t, bias, prio, cond);
}
void LogicProgramAdapter::acycEdge(int s, int t, Potassco::LitSpan cond) {
    lp_->addAcycEdge(static_cast<uint32_t>(s), static_cast<uint32_t>(t), cond);
}
void LogicProgramAdapter::theoryTerm(Id_t termId, int number) { lp_->theoryData().addTerm(termId, number); }
void LogicProgramAdapter::theoryTerm(Id_t termId, std::string_view name) { lp_->theoryData().addTerm(termId, name); }
void LogicProgramAdapter::theoryTerm(Id_t termId, int cId, Potassco::IdSpan args) {
    if (cId >= 0) {
        lp_->theoryData().addTerm(termId, static_cast<Id_t>(cId), args);
    }
    else {
        lp_->theoryData().addTerm(termId, static_cast<Potassco::TupleType>(cId), args);
    }
}
void LogicProgramAdapter::theoryElement(Id_t elementId, Potassco::IdSpan terms, Potassco::LitSpan cond) {
    lp_->theoryData().addElement(elementId, terms, lp_->newCondition(cond));
}
void LogicProgramAdapter::theoryAtom(Id_t atomOrZero, Id_t termId, Potassco::IdSpan elements) {
    lp_->theoryData().addAtom(atomOrZero, termId, elements);
}
void LogicProgramAdapter::theoryAtom(Id_t atomOrZero, Id_t termId, Potassco::IdSpan elements, Id_t op, Id_t rhs) {
    lp_->theoryData().addAtom(atomOrZero, termId, elements, op, rhs);
}
} // namespace Clasp::Asp
