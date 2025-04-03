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
#include <clasp/logic_program_types.h>

#include <clasp/clause.h>
#include <clasp/logic_program.h>
#include <clasp/solver.h>
#include <clasp/util/misc_types.h>
#include <clasp/weight_constraint.h>

#include <potassco/error.h>

namespace Clasp::Asp {
static_assert(std::is_same_v<Potassco::Weight_t, Weight_t>, "unexpected weight type");
static_assert(std::is_same_v<Potassco::Atom_t, Var_t>, "unexpected atom type");
static_assert(std::is_same_v<Potassco::Id_t, uint32_t>, "unexpected id type");
static_assert(std::is_same_v<Potassco::Lit_t, int32_t>, "unexpected literal type");
static_assert(std::is_same_v<Potassco::Weight_t, int32_t>, "unexpected weight type");
template <typename T>
constexpr auto writable(SpanView<T> in) {
    return std::span<T>(const_cast<T*>(in.data()), in.size());
}
/////////////////////////////////////////////////////////////////////////////////////////
// class RuleTransform
//
// class for transforming extended rules to normal rules
/////////////////////////////////////////////////////////////////////////////////////////
struct RuleTransform::Impl {
    Impl() = default;
    struct TodoItem {
        TodoItem(uint32_t i, Weight_t w, Atom_t v) : idx(i), bound(w), head(v) {}
        uint32_t idx;
        Weight_t bound;
        Atom_t   head;
    };
    using TodoQueue = PodQueue<TodoItem>;
    using LitVec    = Potassco::LitVec;
    using WLitVec   = Potassco::WLitVec;
    [[nodiscard]] Atom_t newAtom() const { return prg ? prg->newAtom() : adapt->newAtom(); }
    // NOLINTBEGIN(modernize-use-nodiscard)
    uint32_t addRule(const Rule& r) const {
        if (prg) {
            prg->addRule(r);
        }
        else {
            adapt->addRule(r);
        }
        return 1;
    }
    uint32_t addRule(HeadType ht, Potassco::AtomSpan head, Potassco::LitSpan b) const {
        return addRule(Rule::normal(ht, head, b));
    }
    uint32_t addRule(Atom_t h, Potassco::LitSpan b) const {
        return addRule(HeadType::disjunctive, {&h, static_cast<std::size_t>(h != 0)}, b);
    }
    // NOLINTEND(modernize-use-nodiscard)
    uint32_t transform(Atom_t head, Weight_t bound, Potassco::WeightLitSpan lits, Strategy s);
    uint32_t transformSelect(Atom_t head);
    uint32_t transformSplit(Atom_t head);
    uint32_t transformChoice(Potassco::AtomSpan);
    uint32_t transformDisjunction(Potassco::AtomSpan);
    uint32_t addRule(Atom_t head, bool add, uint32_t idx, Weight_t bound);
    Atom_t   getAuxVar(uint32_t idx, Weight_t bound) {
        assert(bound > 0 && idx < agg_.size());
        auto k = static_cast<uint32_t>(bound - 1);
        if (aux_[k] == 0) {
            todo_.push(TodoItem(idx, bound, aux_[k] = newAtom()));
        }
        return aux_[k];
    }
    ProgramAdapter* adapt{nullptr};
    LogicProgram*   prg{nullptr};
    LitVec          lits;

private:
    WLitVec   agg_;
    SumVec    sumR_;
    VarVec    aux_;
    TodoQueue todo_;
    Weight_t  bound_{0};
};

RuleTransform::RuleTransform(ProgramAdapter& prg) : impl_(std::make_unique<Impl>()) { impl_->adapt = &prg; }
RuleTransform::RuleTransform(LogicProgram& prg) : impl_(std::make_unique<Impl>()) { impl_->prg = &prg; }
RuleTransform::~RuleTransform() = default;

uint32_t RuleTransform::transform(const Rule& r, Strategy s) {
    if (r.sum()) {
        Atom_t h   = not r.head.empty() ? r.head[0] : 0;
        bool   aux = r.ht == HeadType::choice || size(r.head) > 1;
        if (aux) {
            h                  = impl_->newAtom();
            Potassco::Lit_t bl = Potassco::lit(h);
            (void) impl_->addRule(r.ht, r.head, Potassco::toSpan(bl));
        }
        return static_cast<uint32_t>(aux) + impl_->transform(h, r.agg.bound, r.agg.lits, s);
    }
    if (size(r.head) > static_cast<uint32_t>(r.ht == HeadType::disjunctive)) {
        impl_->lits.clear();
        uint32_t nAux = (size(r.cond) > 1) && (size(r.head) > 1) && s != strategy_no_aux;
        if (nAux) {
            // make body eq to a new aux atom
            Atom_t auxB = impl_->newAtom();
            (void) impl_->addRule(auxB, r.cond);
            impl_->lits.push_back(Potassco::lit(auxB));
        }
        else {
            impl_->lits.assign(begin(r.cond), end(r.cond));
        }
        return nAux + (r.ht == HeadType::choice ? impl_->transformChoice(r.head) : impl_->transformDisjunction(r.head));
    }
    return impl_->addRule(r);
}

// A choice rule {h1,...hn} :- BODY is replaced with:
// h1   :- BODY, not aux1.
// aux1 :- not h1.
// ...
// hn   :- BODY, not auxN.
// auxN :- not hn.
uint32_t RuleTransform::Impl::transformChoice(Potassco::AtomSpan atoms) {
    uint32_t nRule = 0;
    auto     bLit  = static_cast<Potassco::Lit_t>(0);
    auto     bAux  = Potassco::toSpan(bLit);
    for (auto atom : atoms) {
        auto hAux = newAtom();
        bAux[0]   = Potassco::neg(atom);
        lits.push_back(Potassco::neg(hAux));
        nRule += addRule(atom, lits);
        nRule += addRule(hAux, bAux);
        lits.pop_back();
    }
    return nRule;
}

// A disjunctive rule h1|...|hn :- BODY is replaced with:
// hi   :- BODY, {not hj | 1 <= j != i <= n}.
uint32_t RuleTransform::Impl::transformDisjunction(Potassco::AtomSpan atoms) {
    uint32_t bIdx = size32(lits);
    for (auto at : atoms.subspan(1)) { lits.push_back(Potassco::neg(at)); }
    uint32_t nRule = 0;
    for (auto it = atoms.begin(), end = atoms.end();;) {
        nRule += addRule(*it, lits);
        if (++it == end) {
            break;
        }
        lits[bIdx++] = Potassco::neg(*(it - 1));
    }
    return nRule;
}

uint32_t RuleTransform::Impl::transform(Atom_t head, Weight_t bound, Potassco::WeightLitSpan wlits, Strategy s) {
    bound_ = bound;
    agg_.assign(begin(wlits), end(wlits));
    constexpr auto cmpW = [](const auto& lhs, const auto& rhs) {
        return Potassco::weight(lhs) > Potassco::weight(rhs);
    };
    if (not std::ranges::is_sorted(agg_, cmpW)) {
        std::ranges::stable_sort(agg_, cmpW);
    }
    Wsum_t sum = 0;
    sumR_.resize(agg_.size());
    for (auto i = agg_.size(); i--;) {
        agg_[i].weight = std::min(agg_[i].weight, bound_);
        sumR_[i]       = (sum += agg_[i].weight);
        POTASSCO_CHECK_PRE(agg_[i].weight >= 0 && sum <= weight_max, "invalid weight rule");
    }
    if (bound_ > sum) {
        return 0;
    }
    if (bound_ <= 0) {
        return addRule(head, {});
    }
    if ((sum - agg_.back().weight) < bound_) { // normal rule
        lits.clear();
        for (const auto& p : agg_) { lits.push_back(lit(p)); }
        return addRule(head, lits);
    }
    return s == strategy_no_aux || (sum < 6 && s == strategy_default) ? transformSelect(head) : transformSplit(head);
}

// Exponential transformation of cardinality and weight constraint.
// Creates minimal subsets, no aux atoms.
// E.g. a rule h = 2 {a,b,c,d} is translated into the following six rules:
// h :- a, b.
// h :- a, c.
// h :- a, d.
// h :- b, c.
// h :- b, d.
// h :- c, d.
uint32_t RuleTransform::Impl::transformSelect(Atom_t h) {
    lits.clear();
    uint32_t nRule = 0;
    Wsum_t   cw    = 0;
    assert(sumR_[0] >= bound_ && cw < bound_);
    aux_.clear();
    for (uint32_t it = 0, end = size32(agg_);;) {
        while (cw < bound_) {
            cw += Potassco::weight(agg_[it]);
            lits.push_back(Potassco::lit(agg_[it]));
            aux_.push_back(it++);
        }
        nRule += addRule(h, lits);
        do {
            if (aux_.empty()) {
                return nRule;
            }
            it = aux_.back();
            aux_.pop_back();
            lits.pop_back();
            cw -= Potassco::weight(agg_[it]);
        } while (++it == end || (cw + sumR_[it]) < bound_);
    }
}
// Quadratic transformation of cardinality and weight constraint.
// Introduces aux atoms.
// E.g. a rule h = 2 {a,b,c,d} is translated into the following eight rules:
// h       :- a, aux_1_1.
// h       :- aux_1_2.
// aux_1_1 :- b.
// aux_1_1 :- aux_2_1.
// aux_1_2 :- b, aux_2_1.
// aux_1_2 :- c, d.
// aux_2_1 :- c.
// aux_2_1 :- d.
uint32_t RuleTransform::Impl::transformSplit(Atom_t h) {
    const Weight_t bound = bound_;
    uint32_t       nRule = 0;
    uint32_t       level = 0;
    aux_.resize(static_cast<uint32_t>(bound), 0);
    todo_.clear();
    todo_.push(TodoItem(0, bound, h));
    while (not todo_.empty()) {
        TodoItem i = todo_.pop_ret();
        if (i.idx > level) {
            // We are about to start a new level of the tree - reset aux_
            level = i.idx;
            aux_.assign(static_cast<uint32_t>(bound), 0);
        }
        // For a todo item i with head h and lit x = agg_[i.idx] create at most two rules:
        // r1: h :- x, aux(i.idx+1, i.bound-weight(x))
        // r2: h :- aux(i.idx+1, i.bound).
        // The first rule r1 represents the case where x is true, while
        // the second rule encodes the case where the literal is false.
        nRule += addRule(i.head, true, i.idx, i.bound - agg_[i.idx].weight);
        nRule += addRule(i.head, false, i.idx, i.bound);
    }
    return nRule;
}

// Creates a rule head :- agg_[idx], aux(idx+1, bound) or head :- aux(idx+1, bound) or depending on add.
uint32_t RuleTransform::Impl::addRule(Atom_t head, bool add, uint32_t bIdx, Weight_t bound) {
    const Weight_t minW = agg_.back().weight;
    const Wsum_t   maxW = sumR_[bIdx + 1];
    if (bound <= 0) {
        assert(add);
        lits.assign(1, agg_[bIdx].lit);
        return addRule(head, lits);
    }
    if ((maxW - minW) < bound) {
        // remaining literals are all needed to satisfy bound
        bIdx += static_cast<uint32_t>(not add);
        if (maxW >= bound) {
            lits.clear();
            for (; bIdx != agg_.size(); ++bIdx) { lits.push_back(agg_[bIdx].lit); }
            return addRule(head, lits);
        }
        return 0;
    }
    lits.clear();
    if (add) {
        lits.push_back(agg_[bIdx].lit);
    }
    lits.push_back(Potassco::lit(getAuxVar(bIdx + 1, bound)));
    return addRule(head, lits);
}
/////////////////////////////////////////////////////////////////////////////////////////
// class SccChecker
//
// SCC/cycle checking
/////////////////////////////////////////////////////////////////////////////////////////
SccChecker::SccChecker(LogicProgram& prg, AtomList& sccAtoms, uint32_t startScc)
    : prg_(&prg)
    , sccAtoms_(&sccAtoms)
    , count_(0)
    , sccs_(startScc) {
    for (auto* atom : prg.atoms()) { visitDfs(atom, PrgNode::atom); }
    for (auto* body : prg.bodies()) { visitDfs(body, PrgNode::body); }
}

void SccChecker::visitDfs(PrgNode* node, NodeType t) {
    if (not prg_ || not doVisit(node)) {
        return;
    }
    callStack_.clear();
    nodeStack_.clear();
    count_ = 0;
    addCall(node, t, 0);
    while (not callStack_.empty()) {
        Call c = callStack_.back();
        callStack_.pop_back();
        if (not recurse(c)) {
            node = unpackNode(c.node);
            if (c.min < node->id()) {
                node->resetId(c.min, true);
            }
            else if (c.node == nodeStack_.back()) {
                // node is trivially-connected; all such nodes are in the same Pseudo-SCC
                if (isNode(nodeStack_.back(), PrgNode::atom)) {
                    node_cast<PrgAtom>(node)->setScc(PrgNode::no_scc);
                }
                node->resetId(PrgNode::no_node, true);
                nodeStack_.pop_back();
            }
            else { // non-trivial SCC
                PrgNode* succVertex;
                do {
                    succVertex = unpackNode(nodeStack_.back());
                    if (isNode(nodeStack_.back(), PrgNode::atom)) {
                        node_cast<PrgAtom>(succVertex)->setScc(sccs_);
                        sccAtoms_->push_back(node_cast<PrgAtom>(succVertex));
                    }
                    nodeStack_.pop_back();
                    succVertex->resetId(PrgNode::no_node, true);
                } while (succVertex != node);
                ++sccs_;
            }
        }
    }
}

bool SccChecker::recurse(Call& c) {
    PrgNode* n = unpackNode(c.node);
    if (not n->seen()) {
        nodeStack_.push_back(c.node);
        c.min = count_++;
        n->resetId(c.min, true);
    }
    if (isNode(c.node, PrgNode::body)) {
        auto*    b = node_cast<PrgBody>(n);
        NodeType t;
        auto     off = c.next;
        for (auto e : b->heads().subspan(off)) {
            PrgHead* h;
            if (e.isAtom()) {
                h = prg_->getAtom(e.node());
                t = PrgNode::atom;
            }
            else {
                h = prg_->getDisj(e.node());
                t = PrgNode::disj;
            }
            if (doVisit(h, false) && onNode(h, t, c, off)) {
                return true;
            }
            ++off;
        }
    }
    else if (isNode(c.node, PrgNode::atom)) {
        auto* a   = node_cast<PrgAtom>(n);
        auto  off = c.next;
        for (auto dep : a->deps().subspan(off)) {
            if (dep.sign()) {
                continue;
            }
            PrgBody* bn = prg_->getBody(dep.var());
            if (doVisit(bn, false) && onNode(bn, PrgNode::body, c, off)) {
                return true;
            }
            ++off;
        }
    }
    else if (isNode(c.node, PrgNode::disj)) {
        auto* d   = node_cast<PrgDisj>(n);
        auto  off = c.next;
        for (auto e : d->atoms().subspan(off)) {
            PrgAtom* a = prg_->getAtom(e);
            if (doVisit(a, false) && onNode(a, PrgNode::atom, c, off)) {
                return true;
            }
            ++off;
        }
    }
    return false;
}

bool SccChecker::onNode(PrgNode* n, NodeType t, Call& c, uint32_t data) {
    if (not n->seen()) {
        Call rec = {c.node, c.min, data};
        callStack_.push_back(rec);
        addCall(n, t, 0);
        return true;
    }
    if (n->id() < c.min) {
        c.min = n->id();
    }
    return false;
}
/////////////////////////////////////////////////////////////////////////////////////////
// class PrgHead
/////////////////////////////////////////////////////////////////////////////////////////
PrgHead::PrgHead(uint32_t id, NodeType t, uint32_t data, bool checkScc)
    : PrgNode(id, checkScc)
    , data_(data)
    , upper_(0)
    , dirty_(0)
    , freeze_(0)
    , isAtom_(t == PrgNode::atom) {
    struct X {
        uint64_t x;
        EdgeVec  y;
        uint32_t z;
    };
    static_assert(sizeof(PrgHead) == sizeof(X), "Unsupported Alignment");
}
// Adds the node with given id as a support to this head
// and marks the head as dirty so that any duplicates/false/eq
// supports are removed once simplify() is called.
void PrgHead::addSupport(PrgEdge r, Simplify s) {
    supports_.push_back(r);
    if (s == force_simplify) {
        dirty_ = (supports_.size() > 1);
    }
}
// Removes the given node from the set of supports of this head.
void PrgHead::removeSupport(PrgEdge r) {
    if (relevant()) {
        erase(supports_, r);
    }
    dirty_ = 1;
}

void PrgHead::clearSupports() {
    supports_.clear();
    upper_ = 0;
    dirty_ = 0;
}
// Simplifies the set of predecessors supporting this head.
// Removes false/eq supports and returns the number of
// different supporting literals in numDiffSupps.
bool PrgHead::simplifySupports(LogicProgram& prg, bool strong, uint32_t* numDiffSupps) {
    uint32_t numLits = numSupports();
    if (dirty_ == 1) {
        uint32_t choices = 0;
        dirty_           = 0;
        numLits          = 0;
        auto& ctx        = *prg.ctx();
        auto  j          = supports_.begin();
        for (auto s : supports_) {
            if (PrgNode* x = prg.getSupp(s);
                x->relevant() && x->value() != value_false && (not strong || x->hasVar())) {
                if (not x->seen()) {
                    *j++ = s;
                    x->setSeen(true);
                }
                else if (not choices) {
                    continue;
                }
                else {
                    if (auto n = std::find_if(supports_.begin(), j, [&s](PrgEdge e) { return e.node() == s.node(); });
                        s < *n) {
                        *n = s;
                    }
                    else {
                        continue;
                    }
                }
                choices += (s.isBody() && s.isChoice());
                if (strong && not ctx.marked(x->literal())) {
                    ++numLits;
                    ctx.mark(x->literal());
                }
            }
        }
        supports_.erase(j, supports_.end());
        choices = 0;
        for (auto s : supports_) {
            PrgNode* x = prg.getSupp(s);
            x->setSeen(false);
            if (strong && ctx.marked(x->literal())) {
                ctx.unmark(x->var());
            }
            if (s.isChoice()) {
                ++choices;
            }
        }
        numLits += choices;
    }
    if (numDiffSupps) {
        *numDiffSupps = numLits;
    }
    return not supports_.empty() || prg.assignValue(this, value_false, PrgEdge::noEdge());
}

// Assigns a variable to this head.
// No support: no var and value false
// More than one support or type not normal or no eq: new var
// Exactly one support that is normal: use that
void PrgHead::assignVar(LogicProgram& prg, PrgEdge support, bool allowEq) {
    if (hasVar() || not relevant()) {
        return;
    }
    uint32_t numS = numSupports();
    if (numS == 0 && not support) {
        prg.assignValue(this, value_false, support);
    }
    else {
        assert(support);
        PrgNode* sup    = prg.getSupp(support);
        bool     newVar = numS > 1 || (not allowEq && prg.ctx()->varInfo(sup->var()).atom());
        if (support.isNormal() && sup->hasVar() && (not newVar || sup->value() == value_true)) {
            // head is equivalent to sup
            setLiteral(sup->literal());
            prg.ctx()->setVarEq(var(), true);
            prg.incEqs(VarType::hybrid);
        }
        else {
            setLiteral(posLit(prg.ctx()->addVar(VarType::atom, 0)));
        }
    }
}

// Backpropagates the value of this head to its supports.
bool PrgHead::backpropagate(LogicProgram& prg, Val_t val, bool bpFull) {
    bool ok = true;
    if (val == value_false) {
        // a false head can't have supports
        EdgeVec temp;
        temp.swap(supports_);
        markDirty();
        for (auto e : temp) {
            if (e.isBody()) {
                ok = prg.getBody(e.node())->propagateAssigned(prg, this, e.type());
            }
            else {
                assert(e.isDisj() && isAtom());
                ok = prg.getDisj(e.node())->propagateAssigned(prg, this, e.type());
            }
            if (not ok) {
                break;
            }
        }
    }
    else if (val != value_free && numSupports() == 1 && bpFull) {
        // head must be true and only has one support, thus the only support must
        // be true, too.
        PrgBody* b = nullptr;
        if (supports_[0].isBody()) {
            b = prg.getBody(supports_[0].node());
        }
        else if (supports_[0].isDisj()) {
            if (PrgDisj* d = prg.getDisj(supports_[0].node()); d->numSupports() == 1) {
                b = prg.getBody(d->support().node());
            }
        }
        ok = not b || b->value() == val || (b->assignValue(val) && b->propagateValue(prg, bpFull));
    }
    return ok;
}

/////////////////////////////////////////////////////////////////////////////////////////
// class PrgAtom
/////////////////////////////////////////////////////////////////////////////////////////
PrgAtom::PrgAtom(uint32_t id, bool checkScc) : PrgHead(id, PrgNode::atom, PrgNode::no_scc, checkScc) {
    static_assert(sizeof(PrgAtom) == sizeof(PrgHead) + sizeof(LitVec), "Unsupported Alignment");
}

void PrgAtom::setEqGoal(Literal x) {
    if (eq()) {
        POTASSCO_CHECK(not x.sign() || x.var() < no_scc, EOVERFLOW, "Id out of range");
        data_ = x.sign() ? x.var() : no_scc;
    }
}
Literal PrgAtom::eqGoal(bool sign) const {
    if (not eq() || sign || data_ == no_scc) {
        return {id(), sign};
    }
    return negLit(data_);
}

// Adds a dependency between this atom and the body with
// the given id. If pos is true, atom appears positively
// in body, otherwise negatively.
void PrgAtom::addDep(Var_t bodyId, bool pos) { deps_.push_back(Literal(bodyId, not pos)); }

// Removes a dependency between this atom and the body with
// the given id. If pos is true, atom appears positively
// in body, otherwise negatively.
void PrgAtom::removeDep(Var_t bodyId, bool pos) {
    if (auto it = std::ranges::find(deps_, Literal(bodyId, not pos)); it != deps_.end()) {
        deps_.erase(it);
    }
}

// Removes the subset of dependencies given by d
void PrgAtom::clearDeps(Dependency d) {
    if (d == dep_all) {
        deps_.clear();
    }
    else {
        erase_if(deps_, [sign = (d == dep_neg)](Literal x) { return x.sign() == sign; });
    }
}

bool PrgAtom::hasDep(Dependency d) const {
    return std::ranges::any_of(deps_,
                               [d](Literal lit) { return d == dep_all || static_cast<Dependency>(lit.sign()) == d; });
}

bool PrgAtom::inDisj() const {
    return std::ranges::any_of(supports_, [](PrgEdge e) { return e.isDisj(); });
}

// Propagates the value of this atom to its dependent bodies
// and, if backpropagation is enabled, to its supporting bodies/disjunctions.
// PRE: value() != value_free
bool PrgAtom::propagateValue(LogicProgram& prg, bool backprop) {
    auto val = value();
    assert(val != value_free);
    // propagate value forward
    Literal dep = posLit(id());
    for (auto d : deps_) {
        if (not prg.getBody(d.var())->propagateAssigned(prg, dep ^ d.sign(), val)) {
            return false;
        }
    }
    if (inDisj() && prg.isFact(this)) {
        // - atom is true, thus all disjunctive rules containing it are superfluous
        EdgeVec temp;
        temp.swap(supports_);
        auto j = temp.begin();
        auto t = PrgEdge::choice;
        for (auto e : temp) {
            if (not e.isDisj()) {
                *j++ = e;
            }
            else if (not prg.getDisj(e.node())->propagateAssigned(prg, this, t)) {
                return false;
            }
        }
        temp.erase(j, temp.end());
        supports_.swap(temp);
    }
    return backpropagate(prg, val, backprop);
}

// Adds the atom-oriented nogoods for this atom in form of clauses.
// Adds the support clause [~a S1...Sn] (where each Si is a supporting node of a)
// representing the tableau-rules BTA and FFA.
// Furthermore, adds the clause [a ~Bj] representing tableau-rules FTA and BFA
// if Bj supports a via a "normal" edge.
bool PrgAtom::addConstraints(const LogicProgram& prg, ClauseCreator& gc) {
    auto& ctx  = *prg.ctx();
    auto  j    = supports_.begin();
    auto  nant = false;
    gc.start().add(~literal());
    for (auto support : supports_) {
        PrgNode* n    = prg.getSupp(support);
        Literal  bLit = n->literal();
        // consider only bodies which are part of the simplified program, i.e.
        // are associated with a variable in the solver.
        if (n->relevant() && n->hasVar()) {
            *j++ = support;
            nant = nant || support.isChoice();
            if (not support.isDisj()) {
                gc.add(bLit);
            }
            if (support.isNormal() && not ctx.addBinary(literal(), ~bLit)) { // FTA/BFA
                return false;
            }
        }
    }
    supports_.erase(j, supports_.end());
    if (nant || hasDep(PrgAtom::dep_neg)) {
        ctx.setNant(var(), true);
    }
    return gc.end(ClauseCreator::clause_force_simplify).ok();
}
/////////////////////////////////////////////////////////////////////////////////////////
// class PrgBody
/////////////////////////////////////////////////////////////////////////////////////////
[[nodiscard]] static Literal solverLiteral(const LogicProgram& prg, Literal goal) {
    return prg.getAtom(goal.var())->literal() ^ goal.sign();
}
PrgBody::PrgBody(uint32_t id, BodyType t, uint32_t sz)
    : PrgNode(id, true)
    , size_(sz)
    , head_(0)
    , type_(to_underlying(t))
    , sBody_(0)
    , sHead_(0)
    , freeze_(0)
    , unsupp_(0)
    , headData_() {
    POTASSCO_CHECK_PRE(sz <= max_size, "body too large");
}
PrgBody::PrgBody(uint32_t id, const LogicProgram& prg, Potassco::LitSpan lits, uint32_t pos, bool addDeps)
    : PrgBody(id, BodyType::normal, size32(lits)) {
    auto c  = new (data_) Norm();
    unsupp_ = static_cast<Weight_t>(pos);
    // store B+ followed by B-
    Literal* p[2] = {c->lits, c->lits + pos};
    for (auto lit : lits) {
        POTASSCO_CHECK_PRE(lit != 0, "body not simplified");
        Literal*& n = p[lit < 0];
        *n          = toLit(lit);
        if (addDeps) {
            prg.getAtom(n->var())->addDep(id, not n->sign());
        }
        ++n;
    }
}

PrgBody::PrgBody(uint32_t id, const LogicProgram& prg, const Potassco::Sum& sum, bool hasWeights, uint32_t pos,
                 bool addDeps)
    : PrgBody(id, hasWeights ? BodyType::sum : BodyType::count, size32(sum.lits)) {
    Agg* a = new (data_) Agg();
    if (not hasWeights) {
        a->bound = sum.bound;
        unsupp_  = sum.bound - static_cast<Weight_t>(size_ - pos);
    }
    else {
        a->sum  = SumData::create(size_, sum.bound, 0);
        unsupp_ = sum.bound;
    }
    // store B+ followed by B- followed by optional weights
    Literal*  base    = a->lits;
    Literal*  p[2]    = {base, base + pos};
    Weight_t* weights = hasWeights ? a->sum->weights : nullptr;
    for (const auto& wl : sum.lits) {
        POTASSCO_CHECK_PRE(wl.lit != 0 && wl.weight > 0, "body not simplified");
        Literal*& n = p[wl.lit < 0];
        *n          = toLit(Potassco::lit(wl));
        if (weights) {
            weights[n - base]  = wl.weight;
            a->sum->sumW      += wl.weight;
            if (n->sign()) {
                unsupp_ -= wl.weight;
            }
        }
        if (addDeps) {
            prg.getAtom(n->var())->addDep(id, not n->sign());
        }
        ++n;
    }
}
PrgBody* PrgBody::create(const LogicProgram& prg, uint32_t id, const Rule& r, uint32_t pos, bool addDeps) {
    static_assert(sizeof(PrgBody) == 24 && sizeof(Agg) == sizeof(void*), "unexpected alignment");
    PrgBody* ret;
    if (r.normal()) {
        size_t bytes = sizeof(PrgBody) + (r.cond.size() * sizeof(Literal));
        ret          = new (::operator new(bytes)) PrgBody(id, prg, r.cond, pos, addDeps);
    }
    else {
        const Potassco::Sum& sum   = r.agg;
        size_t               bytes = sizeof(PrgBody) + (r.agg.lits.size() * sizeof(Literal)) + sizeof(Agg);
        ret = new (::operator new(bytes)) PrgBody(id, prg, sum, r.bt == BodyType::sum, pos, addDeps);
        POTASSCO_CHECK_PRE(ret->bound() > 0 && ret->sumW() > ret->bound(), "body not simplified");
    }
    if (ret->bound() == 0) {
        ret->assignValue(value_true);
        ret->markDirty();
    }
    return ret;
}

PrgBody::~PrgBody() {
    clearHeads();
    if (hasWeights()) {
        sumData()->destroy();
    }
}

void PrgBody::destroy() {
    this->~PrgBody();
    ::operator delete(this);
}

PrgBody::SumData* PrgBody::SumData::create(uint32_t size, Weight_t b, Weight_t s) {
    uint32_t bytes = sizeof(SumData) + (size * sizeof(Weight_t));
    auto*    ret   = new (::operator new(bytes)) SumData();
    ret->bound     = b;
    ret->sumW      = s;
    return ret;
}
void PrgBody::SumData::destroy() { ::operator delete(this); }

uint32_t PrgBody::findLit(const LogicProgram& prg, Literal p) const {
    auto r = goals();
    if (auto it = std::ranges::find(r, p, [&](Literal goal) { return solverLiteral(prg, goal); }); it != r.end()) {
        return static_cast<uint32_t>(std::distance(r.begin(), it));
    }
    return var_max;
}

// Sets the unsupported counter back to
// bound() - negWeight()
bool PrgBody::resetSupported() {
    unsupp_ = bound();
    for (uint32_t x = size(); x && goal(--x).sign();) { unsupp_ -= weight(x); }
    return isSupported();
}

// Removes all heads from this body *without* notifying them
void PrgBody::clearHeads() {
    if (not isSmallHead()) {
        delete largeHead();
    }
    head_ = 0;
}

// Makes h a head-successor of this body and adds this
// body as a support for h.
void PrgBody::addHead(PrgHead* h, EdgeType t) {
    assert(relevant() && h->relevant());
    PrgEdge fwdEdge  = PrgEdge::newEdge(*h, t);
    PrgEdge bwdEdge  = PrgEdge::newEdge(*this, t);
    auto    numHeads = size32(heads());
    auto    numSupps = h->numSupports();
    bool    dup      = false;
    if (numHeads && numSupps && std::min(numHeads, numSupps) < 10) {
        if (numSupps < numHeads) {
            dup = contains(h->supports(), bwdEdge);
        }
        else {
            dup = contains(heads(), fwdEdge);
        }
    }
    if (dup) {
        return;
    }
    addHead(fwdEdge);
    h->addSupport(bwdEdge);
    // mark head-set as dirty
    if (head_ > 1) {
        sHead_ = 1;
    }
}

void PrgBody::addHead(PrgEdge h) {
    if (head_ < 2u) {
        smallHead()[head_++] = h;
    }
    else if (not isSmallHead()) {
        largeHead()->push_back(h);
    }
    else {
        auto  hs      = heads();
        auto* t       = new EdgeVec(hs.begin(), hs.end());
        headData_.ext = t;
        head_         = 3u;
        t->push_back(h);
    }
}

void PrgBody::removeHead(PrgHead* h, EdgeType t) {
    PrgEdge x = PrgEdge::newEdge(*h, t);
    if (eraseHead(x)) {
        h->removeSupport(PrgEdge::newEdge(*this, t)); // also remove back edge
    }
}

bool PrgBody::hasHead(const PrgHead* h, EdgeType t) const {
    if (not hasHeads()) {
        return false;
    }
    auto x  = PrgEdge::newEdge(*h, t);
    auto hs = heads();
    auto it = sHead_ != 0 || isSmallHead() ? std::ranges::find(hs, x) : std::ranges::lower_bound(hs, x);
    return it != hs.end() && *it == x;
}

bool PrgBody::eraseHead(PrgEdge h) {
    auto hs = heads();
    if (auto it = std::ranges::find(hs, h); it != hs.end()) {
        auto pos = std::distance(hs.begin(), it);
        if (not isSmallHead()) {
            largeHead()->erase(largeHead()->begin() + pos);
        }
        else {
            smallHead()[pos] = smallHead()[1];
            --head_;
        }
        return true;
    }
    return false;
}

bool PrgBody::toData(const LogicProgram& prg, Potassco::RuleBuilder& out) const {
    BodyType bt  = type();
    Weight_t sum = 0, bound = this->bound();
    bt == BodyType::normal ? out.startBody() : out.startSum(bound);
    for (auto i : irange(size())) {
        Potassco::WeightLit wl = {toInt(goal(i)), weight(i)};
        if (not prg.frozen() || prg.inProgram(Potassco::atom(wl))) {
            out.addGoal(wl);
            sum += wl.weight;
        }
        else if (wl.lit < 0) {
            bound -= weight(i);
        }
        else if (bt == BodyType::normal) {
            return false;
        }
    }
    if (bt != BodyType::normal) {
        out.setBound(bound);
        if (bound <= 0 || bound >= sum) {
            if (bound > sum) {
                return false;
            }
            if (bound <= 0) {
                out.clearBody();
            }
            else {
                out.weaken(BodyType::normal);
            }
        }
    }
    return true;
}

// Simplifies the body by removing assigned atoms & replacing eq atoms.
// Checks whether simplified body must be false (CONTRA) or is
// structurally equivalent to some other body.
// prg    The program containing this body
// strong If true, treats atoms that have no variable associated as false.
// eqId   The id of a body in prg that is equivalent to this body
bool PrgBody::simplifyBody(LogicProgram& prg, bool strong, uint32_t* eqId) {
    if (eqId) {
        *eqId = id();
    }
    if (sBody_ == 0) {
        return true;
    }
    // update body - compute old hash value
    SharedContext& ctx     = *prg.ctx();
    uint32_t       oldHash = 0;
    Weight_t       bound   = this->bound();
    Weight_t*      jw      = hasWeights() ? sumData()->weights : nullptr;
    Literal*       lits    = this->lits();
    Literal*       j       = lits;
    AtomState&     todo    = prg.atomState();
    Var_t          a;
    int            todos = 0;
    for (Literal *it = j, *end = j + size(); it != end; ++it) {
        a          = it->var();
        bool isEq  = a != prg.getRootId(a);
        oldHash   += hashLit(*it);
        if (isEq) {
            prg.getAtom(a)->removeDep(id(), not it->sign()); // remove old edge
            *it = prg.getAtom(a)->eqGoal(it->sign());        // replace with eq goal
            a   = it->var();                                 // and check it
        }
        Literal aLit = solverLiteral(prg, *it);
        auto    v    = prg.getAtom(a)->value();
        bool    mark = strong || prg.getAtom(a)->hasVar();
        if (strong && not prg.getAtom(a)->hasVar()) {
            v = value_false;
        }
        if (v == value_weak_true && it->sign()) {
            v = value_true;
        }
        if (v == value_true || v == value_false) { // truth value is known - remove subgoal
            if (v == trueValue(*it)) {
                // subgoal is true: decrease necessary lower bound
                bound -= weight(static_cast<uint32_t>(it - lits));
            }
            prg.getAtom(a)->removeDep(id(), not it->sign());
        }
        else if (not mark || not ctx.marked(aLit)) {
            if (mark) {
                ctx.mark(aLit);
            }
            if (isEq) { // remember to add edge for new goal later
                todo.addToBody(*it);
                ++todos;
            }
            *j++ = *it; // copy literal and optionally weight
            if (jw) {
                *jw++ = weight(static_cast<uint32_t>(it - lits));
            }
        }
        else {                                // body contains aLit more than once
            if (type() != BodyType::normal) { // merge subgoal
                Weight_t w = 1;
                if (not jw) {
                    SumData* sum = SumData::create(size(), this->bound(), this->sumW());
                    std::fill_n(sum->weights, size(), w);
                    aggData().sum = sum;
                    type_         = to_underlying(BodyType::sum);
                    jw            = sum->weights + (it - lits);
                }
                else {
                    w = weight(static_cast<uint32_t>(it - lits));
                }
                uint32_t pos             = findLit(prg, aLit);
                sumData()->weights[pos] += w;
            }
            else { // ignore if normal
                --bound;
                if (not isEq) { // remove edge
                    if (todo.inBody(*it)) {
                        todo.clearBody(*it);
                        --todos;
                    }
                    else {
                        prg.getAtom(it->var())->removeDep(id(), not it->sign());
                    }
                }
            }
        }
    }
    // unmark atoms, compute new hash value,
    // and restore pos | neg partition in case
    // we changed some positive goals to negative ones
    size_ = static_cast<uint32_t>(j - lits);
    if (jw) {
        jw = sumData()->weights;
    }
    uint32_t newHash = 0;
    Weight_t sumW = 0, reachW = 0;
    for (uint32_t p = 0, n = size_, i, h; p < n;) {
        if (not lits[p].sign()) {
            h = hashLit(lits[i = p++]);
        }
        else if (lits[n - 1].sign()) {
            h = hashLit(lits[i = --n]);
        }
        else /* restore pos|neg order */ {
            std::swap(lits[p], lits[n - 1]);
            if (jw) {
                std::swap(jw[p], jw[n - 1]);
            }
            continue;
        }
        a = lits[i].var();
        if (todos && todo.inBody(lits[i])) {
            prg.getAtom(a)->addDep(id(), not lits[i].sign());
            todo.clearBody(lits[i]);
            --todos;
        }
        auto v  = prg.getAtom(a)->var();
        auto w  = not jw ? 1 : jw[i];
        sumW   += w;
        reachW += w;
        if (ctx.marked(posLit(v)) && ctx.marked(negLit(v))) {
            // body contains aLit and ~aLit
            if (not hasWeights()) {
                reachW -= 1;
            }
            else {
                Literal  other = solverLiteral(prg, ~lits[i]);
                uint32_t pos   = findLit(prg, other);
                assert(pos != var_max && pos != i && jw);
                reachW -= std::min(w, jw[pos]);
            }
        }
        ctx.unmark(v);
        newHash += h;
    }
    bool ok = normalize(prg, bound, sumW, reachW, newHash);
    if (ok) {
        auto xId = id();
        if (oldHash != newHash) {
            xId = prg.update(this, oldHash, newHash);
        }
        if (eqId) {
            *eqId = xId != var_max ? xId : id();
        }
    }
    if (strong) {
        sBody_ = 0;
    }
    return ok && (value() == value_free || propagateValue(prg));
}

bool PrgBody::normalize(const LogicProgram& prg, Weight_t bound, Weight_t sumW, Weight_t reachW, uint32_t& hashOut) {
    BodyType nt = (sumW == bound || size() == 1) ? BodyType::normal : type();
    bool     ok = true;
    if (sumW >= bound && type() != BodyType::normal) {
        if (hasWeights()) {
            sumData()->bound = bound;
            sumData()->sumW  = sumW;
        }
        else {
            aggData().bound = bound;
        }
    }
    if (bound <= 0) {
        for (auto myId = id(); auto g : goals()) { prg.getAtom(g.var())->removeDep(myId, not g.sign()); }
        size_   = 0;
        hashOut = 0, unsupp_ = 0;
        nt = BodyType::normal;
        ok = assignValue(value_true);
    }
    else if (reachW < bound) {
        ok     = assignValue(value_false);
        sHead_ = 1;
        markRemoved();
    }
    if (nt != type()) {
        assert(nt == BodyType::normal);
        Literal* from = aggData().lits;
        if (hasWeights()) {
            sumData()->destroy();
        }
        Literal* to = (new (data_) Norm())->lits;
        std::copy_n(from, size(), to);
        type_ = to_underlying(nt);
    }
    return ok;
}

// Marks the set of heads in rs and removes
// any duplicate heads.
void PrgBody::prepareSimplifyHeads(const LogicProgram& prg, AtomState& rs) {
    auto hs   = writable(heads());
    auto drop = 0u;
    for (auto j = hs.begin(), end = hs.end(); j != end;) {
        if (not rs.inHead(*j)) {
            rs.addToHead(*j);
            ++j;
        }
        else {
            prg.getHead(*j)->markDirty();
            *j = *--end;
            ++drop;
        }
    }
    if (drop) {
        if (auto nHeads = size32(hs) - drop; isSmallHead()) {
            head_ = nHeads;
        }
        else {
            shrinkVecTo(*largeHead(), nHeads);
        }
    }
}

// Simplifies the heads of this body wrt target.
// Removes superfluous/eq/unsupported heads and checks for self-blocking
// situations.
// PRE: prepareSimplifyHeads was called
bool PrgBody::simplifyHeadsImpl(const LogicProgram& prg, PrgBody& target, AtomState& rs, bool strong) {
    uint32_t newSize = 0;
    bool     merge   = this != &target;
    bool     block   = value() == value_false || (merge && target.value() == value_false);
    auto     hs      = writable(heads());
    auto*    j       = hs.data();
    for (auto h : hs) {
        PrgHead* cur = prg.getHead(h);
        block        = block || target.blockedHead(h, rs);
        if (not cur->relevant() || (strong && not cur->hasVar()) || block || target.superfluousHead(prg, cur, h, rs) ||
            cur->value() == value_false) {
            // remove superfluous and unsupported heads
            cur->removeSupport(PrgEdge::newEdge(*this, h.type()));
            rs.clearHead(h);
            block = block || (cur->value() == value_false && h.type() == PrgEdge::normal);
        }
        else {
            *j++ = h;
            ++newSize;
            if (merge) {
                target.addHead(cur, h.type());
            }
        }
    }
    if (isSmallHead()) {
        head_ = newSize;
    }
    else {
        shrinkVecTo(*largeHead(), newSize);
    }
    return not block;
}

bool PrgBody::simplifyHeads(LogicProgram& prg, bool strong) {
    if (sHead_ == 0) {
        return true;
    }
    return PrgBody::mergeHeads(prg, *this, strong);
}

bool PrgBody::mergeHeads(LogicProgram& prg, PrgBody& heads, bool strong, bool simplify) {
    AtomState& rs = prg.atomState();
    bool       ok = true;
    assert((this == &heads || heads.sHead_ == 0) && "Heads to merge not simplified!");
    if (simplify || &heads == this) {
        // mark the body literals so that we can easily detect superfluous atoms
        // and selfblocking situations.
        for (auto g : goals()) { rs.addToBody(g); }
        // remove duplicate/superfluous heads & check for blocked atoms
        prepareSimplifyHeads(prg, rs);
        if (this == &heads) {
            ok = simplifyHeadsImpl(prg, *this, rs, strong);
        }
        else {
            heads.prepareSimplifyHeads(prg, rs);
            if (not simplifyHeadsImpl(prg, *this, rs, strong) && not assignValue(value_false)) {
                clearRule(rs);
                return false;
            }
            ok = heads.simplifyHeadsImpl(prg, *this, rs, strong);
            if (not ok && (not heads.assignValue(value_false) || not heads.propagateValue(prg, false))) {
                clearRule(rs);
                return false;
            }
        }
        // clear temporary flags & reestablish ordering
        std::ranges::sort(writable(this->heads()));
        clearRule(rs);
        sHead_ = 0;
    }
    else if (relevant()) {
        for (auto e : heads.heads()) {
            if (PrgHead* h = prg.getHead(e); h->relevant()) {
                addHead(h, e.type());
            }
        }
    }
    return ok || (assignValue(value_false) && propagateValue(prg));
}

// Checks whether the head is superfluous w.r.t this body, i.e.
//  - is needed to satisfy the body
//  - it appears in the body and is a choice
//  - it is a disjunction and one of the atoms is needed to satisfy the body
bool PrgBody::superfluousHead(const LogicProgram& prg, const PrgHead* head, PrgEdge it, const AtomState& rs) const {
    if (it.isAtom()) {
        // the head is an atom
        uint32_t atomId = it.node();
        if (rs.inBody(posLit(atomId))) {
            Weight_t w = 1;
            if (hasWeights()) {
                const Literal* lits = aggData().lits;
                const Literal* x    = std::find(lits, lits + size(), posLit(atomId));
                assert(x != lits + size());
                w = sumData()->weights[x - lits];
            }
            if (it.isChoice() || (sumW() - w) < bound()) {
                return true;
            }
        }
        return it.isChoice() && (rs.inBody(negLit(atomId)) || rs.inHead(atomId));
    }
    else {
        assert(it.isDisj());
        // check each contained atom
        const auto* dis = node_cast<PrgDisj>(head);
        for (auto a : dis->atoms()) {
            if (rs.inBody(posLit(a)) || rs.inHead(a)) {
                return true;
            }
            if (prg.isFact(prg.getAtom(a))) {
                return true;
            }
        }
        // check for subsumption
        if (prg.options().iters == LogicProgram::AspOptions::max_eq_iters) {
            for (auto e : heads()) {
                if (e.isDisj() && prg.getDisj(e.node())->size() < dis->size()) {
                    const PrgDisj* other = prg.getDisj(e.node());
                    for (auto a : other->atoms()) {
                        if (not contains(dis->atoms(), a)) {
                            other = nullptr;
                            break;
                        }
                    }
                    if (other && other->size() > 0) {
                        return true;
                    }
                }
            }
        }
    }
    return false;
}

// Checks whether the rule it.node() :- *this is selfblocking, i.e.
// from TB follows conflict
bool PrgBody::blockedHead(PrgEdge it, const AtomState& rs) const {
    if (it.isAtom() && it.isNormal() && rs.inBody(negLit(it.node()))) {
        Weight_t w = 1;
        if (hasWeights()) {
            const Literal* lits = aggData().lits;
            const Literal* x    = std::find(lits, lits + size(), negLit(it.node()));
            assert(x != lits + size());
            w = sumData()->weights[x - lits];
        }
        return (sumW() - w) < bound();
    }
    return false;
}

void PrgBody::assignVar(LogicProgram& prg) {
    if (hasVar() || not relevant()) {
        return;
    }
    if (uint32_t size = this->size(); size == 0 || value() == value_true) {
        setLiteral(lit_true);
    }
    else if (size == 1 && prg.getAtom(goal(0).var())->hasVar()) {
        Literal x = solverLiteral(prg, goal(0));
        setLiteral(x);
        prg.ctx()->setVarEq(var(), true);
        prg.incEqs(VarType::hybrid);
    }
    else if (value() != value_false) {
        setLiteral(posLit(prg.ctx()->addVar(VarType::body, 0)));
    }
    else {
        setLiteral(lit_false);
    }
}

bool PrgBody::propagateSupported(Var_t v) {
    Weight_t w = 1;
    if (hasWeights()) {
        auto gs  = goals();
        auto pos = std::distance(gs.begin(), std::ranges::find(gs, posLit(v)));
        w        = weight(static_cast<uint32_t>(pos));
    }
    return (unsupp_ -= w) <= 0;
}

bool PrgBody::propagateAssigned(LogicProgram& prg, Literal p, Val_t v) {
    if (not relevant()) {
        return true;
    }
    assert(contains(goals(), p));
    markDirty();
    auto     x = v == value_weak_true ? value_true : v;
    Weight_t w = 1; // TODO: find weight of p for weight rule
    if (x == falseValue(p) && (sumW() - w) < bound() && value() != value_false) {
        return assignValue(value_false) && propagateValue(prg);
    }
    else if (x == trueValue(p) && (bound() - w) <= 0 && value() != value_weak_true) {
        return assignValue(value_weak_true) && propagateValue(prg);
    }
    return true;
}

bool PrgBody::propagateAssigned(LogicProgram& prg, const PrgHead* h, EdgeType t) {
    if (not relevant()) {
        return true;
    }
    markHeadsDirty();
    if (h->value() == value_false && hasHead(h, t) && t == PrgEdge::normal) {
        return value() == value_false || (assignValue(value_false) && propagateValue(prg));
    }
    return true;
}

bool PrgBody::propagateValue(LogicProgram& prg, bool backprop) {
    auto val = value();
    assert(value() != value_free);
    // propagate value forward
    for (auto h : heads()) {
        PrgHead* head = prg.getHead(h);
        PrgEdge  supp = PrgEdge::newEdge(*this, h.type());
        if (val == value_false) {
            head->removeSupport(supp);
        }
        else if (not h.isChoice() && head->value() != val && not prg.assignValue(head, val, supp)) {
            return false;
        }
    }
    if (val == value_false) {
        clearHeads();
    }
    // propagate value backward
    if (backprop && relevant()) {
        const uint32_t wInc  = hasWeights();
        Weight_t       maxW  = wInc == 0 ? 1 : *std::max_element(sumData()->weights, sumData()->weights + size());
        Weight_t*      wPos  = wInc == 0 ? &maxW : sumData()->weights;
        Weight_t       bound = value() == value_false ? this->bound() : (sumW() - this->bound()) + 1;
        if (maxW >= bound) {
            for (auto g : goals()) {
                if ((bound - *wPos) <= 0) {
                    auto goalVal = val;
                    if (g.sign()) {
                        goalVal = val == value_false ? value_weak_true : value_false;
                    }
                    if (not prg.assignValue(prg.getAtom(g.var()), goalVal, PrgEdge::noEdge())) {
                        return false;
                    }
                }
                wPos += wInc;
            }
        }
    }
    return true;
}
bool PrgBody::propagateValue(LogicProgram& prg) { return propagateValue(prg, prg.options().backprop != 0); }

// Adds nogoods for the tableau-rules FFB and BTB as well as FTB, BFB.
// For normal bodies, clauses are used, i.e:
//   FFB and BTB:
//     - a binary clause [~b s] for every positive subgoal 's' of 'b'
//     - a binary clause [~b ~n] for every negative subgoal 'n' of 'b'
//   FTB and BFB:
//     - a clause [b ~s1...~sn n1...nn] where 'si' is a positive and 'ni' a negative subgoal
// For count/sum bodies, a weight constraint is created.
bool PrgBody::addConstraints(const LogicProgram& prg, ClauseCreator& gc) {
    if (type() == BodyType::normal) {
        bool    taut = false;
        Literal negB = ~literal();
        gc.start().add(literal());
        for (auto g : goals()) {
            Literal li = solverLiteral(prg, g);
            if (li == literal()) {
                taut = true;
                continue;
            }
            if (not prg.ctx()->addBinary(negB, li)) { // [~B li]
                return false;
            }
            if (li.var() != negB.var()) { // [B v ~l1 v ... v ~ln]
                gc.add(~li);
            }
        }
        return taut || gc.end();
    }
    WeightLitVec lits;
    for (uint32_t idx = 0; auto g : goals()) {
        Literal li = solverLiteral(prg, g);
        lits.push_back(WeightLiteral{li, weight(idx)});
        ++idx;
    }
    return WeightConstraint::create(*prg.ctx()->master(), literal(), lits, bound()).ok();
}

// Returns the SCC of body B, i.e.
// - scc if exist atom a in B.heads(), x in B+, s.th. a.scc == x.scc
// - noScc otherwise
uint32_t PrgBody::scc(const LogicProgram& prg) const {
    auto sccMask = static_cast<uint64_t>(0);
    auto end     = size();
    auto large   = false;
    for (auto i : irange(end)) {
        if (goal(i).sign()) {
            end = i;
            break;
        }
        if (auto scc = prg.getAtom(goal(i).var())->scc(); scc != no_scc) {
            sccMask |= static_cast<uint64_t>(1) << (scc & 63);
            large   |= scc > 63;
        }
    }
    if (sccMask != 0) {
        for (auto h : heads()) {
            const auto head     = h.node();
            auto       atomSpan = Potassco::toSpan(head);
            if (not h.isAtom()) {
                PrgDisj* d = prg.getDisj(head);
                atomSpan   = d->atoms();
            }
            for (auto a : atomSpan) {
                if (auto scc = prg.getAtom(a)->scc();
                    scc != no_scc && (sccMask & (static_cast<uint64_t>(1) << (scc & 63))) != 0) {
                    if (not large) {
                        return scc;
                    }
                    for (auto j : irange(end)) {
                        if (scc == prg.getAtom(goal(j).var())->scc()) {
                            return scc;
                        }
                    }
                }
            }
        }
    }
    return no_scc;
}

/////////////////////////////////////////////////////////////////////////////////////////
// class PrgDisj
//
// Head of a disjunctive rule
/////////////////////////////////////////////////////////////////////////////////////////
PrgDisj* PrgDisj::create(uint32_t id, Potassco::AtomSpan head) {
    void* m = ::operator new(sizeof(PrgDisj) + (head.size() * sizeof(Atom_t)));
    return new (m) PrgDisj(id, head);
}

PrgDisj::PrgDisj(uint32_t id, Potassco::AtomSpan head) : PrgHead(id, disj, size32(head)) {
    std::ranges::copy(head, atoms_);
    std::sort(atoms_, atoms_ + size());
}
PrgDisj::~PrgDisj() = default;
void PrgDisj::destroy() {
    this->~PrgDisj();
    ::operator delete(this);
}

void PrgDisj::detach(const LogicProgram& prg, bool full) {
    PrgEdge edge = PrgEdge::newEdge(*this, PrgEdge::choice);
    for (auto a : atoms()) { prg.getAtom(a)->removeSupport(edge); }
    EdgeVec temp;
    temp.swap(supports_);
    for (auto e : temp) { prg.getBody(e.node())->removeHead(this, PrgEdge::normal); }
    if (full) {
        clearSupports();
        markRemoved();
    }
    else {
        supports_.swap(temp);
    }
}

bool PrgDisj::propagateAssigned(const LogicProgram& prg, PrgHead* head, EdgeType t) {
    assert(head->isAtom() && t == PrgEdge::choice);
    if (prg.isFact(node_cast<PrgAtom>(head)) || head->value() == value_false) {
        auto as = writable(atoms());
        if (auto it = std::ranges::find(as, head->id()); it != as.end()) {
            if (head->value() == value_true) {
                detach(prg);
            }
            else if (head->value() == value_false) {
                head->removeSupport(PrgEdge::newEdge(*this, t));
                std::copy(it + 1, as.end(), it);
                if (--data_ == 1u) {
                    PrgAtom* last = prg.getAtom(*as.begin());
                    EdgeVec  temp;
                    clearSupports(temp);
                    for (auto e : temp) {
                        prg.getBody(e.node())->removeHead(this, PrgEdge::normal);
                        prg.getBody(e.node())->addHead(last, PrgEdge::normal);
                    }
                    detach(prg);
                }
            }
        }
    }
    return true;
}
} // namespace Clasp::Asp
