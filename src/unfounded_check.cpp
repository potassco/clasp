//
// Copyright (c) 2010-present Benjamin Kaufmann
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
#include <clasp/unfounded_check.h>

#include <clasp/clause.h>

#include <algorithm>
#include <cmath>
namespace Clasp {
/////////////////////////////////////////////////////////////////////////////////////////
// DefaultUnfoundedCheck - Construction/Destruction
/////////////////////////////////////////////////////////////////////////////////////////
// Choice rules are handled like normal rules with one exception:
//  Since BFA does not apply to choice rules, we manually trigger the removal of source pointers
//  whenever an atom sourced by a choice rule becomes false.
//
// The major problems with card/weight-rules are:
//  1. subgoals can circularly depend on the body
//  2. subgoal false -> body false, does not hold
//
// Regarding the first point, consider: {b}. a:- 1{a,b}.
// Since b is external to 1{a,b}, the body is a valid source for a. Therefore, 1{a,b} can source a.
// After a's source pointer is set to 1{a,b}, both subgoals of 1{a,b} have a source. Nevertheless,
// we must not count a because it (circularly) depends on the body. I.e. as soon as b
// becomes false, a is unfounded, because the loop {a} no longer has external bodies.
//
// The second point means that we have to watch *all* subgoals because we
// may need to trigger source pointer removal whenever one of the subgoals becomes false.
// Consider: {a,b,c}. t :- 2 {b,t,x}. x :- t,c. x :- a.
// Now assume {t,c} is true and a becomes false. In this case, both x and t lose their
// source pointer and we get the (conflicting) unfounded set {x, t}.
// Further assume that after some backtracking we have that both {t,c} and a
// become false. Therefore x is false, too. Since we do not update source pointers on
// conflicts, x and t still have no source. Thus no removal of source pointers is triggered.
// If we would not watch x in 2 {b,t,x}, we could not add t to the todo queue and
// we would therefore miss the unfounded set {t}.
//
// The implementation for extended bodies works as follows:
// - It distinguishes between internal literals, those that are in the same SCC as B
//   and external literals, those that are not.
// - Let W(l) be the weight of literal l in B and W(WS) be the sum of W(l) for each l in a set WS.
// - The goal is to maintain a set WS of literals l, s.th l in Body and hasSource(l) AND W(WS) >= bound.
// - Initially WS contains all non-false external literals of B.
// - Whenever one of the internal literals of B becomes sourced, it is added to WS
//   *only if* W(WS) < bound. In that case, it is guaranteed that the literal
//   currently does not circularly depend on the body.
// - As soon as W(WS) >= bound, we declare the body as valid source for its heads.
// - Whenever one of the literals l in WS loses its source, it is removed from WS.
//   If l is an external literal, new valid external literals are searched and added to WS
//   until the source condition holds again.
// - If the condition cannot be restored, the body is marked as invalid source.

DefaultUnfoundedCheck::DefaultUnfoundedCheck(DependencyGraph& g, ReasonStrategy st)
    : solver_(nullptr)
    , graph_(&g)
    , mini_(nullptr)
    , reasons_(nullptr)
    , strategy_(st) {}
DefaultUnfoundedCheck::~DefaultUnfoundedCheck() {
    for (auto* ext : extended_) { ::operator delete(ext); }
}
/////////////////////////////////////////////////////////////////////////////////////////
// DefaultUnfoundedCheck - Initialization
/////////////////////////////////////////////////////////////////////////////////////////
void DefaultUnfoundedCheck::addWatch(Literal p, uint32_t data, WatchType type) {
    assert(data < var_max);
    solver_->addWatch(p, this, (data << 2) | type);
}

void DefaultUnfoundedCheck::setReasonStrategy(ReasonStrategy rs) {
    strategy_ = rs;
    if (strategy_ == only_reason && solver_ && not reasons_) {
        reasons_ = std::make_unique<LitVec[]>(solver_->numVars());
    }
}
// inits unfounded set checker with graph, i.e.
// - creates data objects for bodies and atoms
// - adds necessary watches to the solver
// - initializes source pointers
bool DefaultUnfoundedCheck::init(Solver& s) {
    assert(not solver_ || solver_ == &s);
    reasons_.reset();
    solver_ = &s;
    setReasonStrategy(s.searchMode() != SolverStrategies::no_learning ? strategy_ : no_reason);
    // process any leftovers from previous steps
    while (findUfs(s, false) != ufs_none) {
        while (not ufs_.empty()) {
            if (not s.force(~graph_->getAtom(ufs_.front()).lit, nullptr)) {
                return false;
            }
            atoms_[ufs_.pop_ret()].ufs = 0;
        }
    }
    auto startAtom = size32(atoms_);
    // set up new atoms
    atoms_.resize(graph_->numAtoms());
    AtomData& sentinel = atoms_[DependencyGraph::sentinel_atom];
    sentinel.resurrectSource();
    sentinel.todo = 1;
    sentinel.ufs  = 1;
    // set up new bodies
    for (auto i : irange(size32(bodies_), graph()->numBodies())) {
        bodies_.push_back(BodyData());
        BodyPtr n(getBody(i));
        if (not n.node->extended()) {
            initBody(n);
        }
        else {
            initExtBody(n);
        }
        // when a body becomes false, it can no longer be used as source
        addWatch(~n.node->lit, n.id, watch_source_false);
    }
    // check for initially unfounded atoms
    propagateSource();
    for (NodeId nId : irange(startAtom, size32(atoms_))) {
        const AtomNode& a = graph_->getAtom(nId);
        if (not atoms_[nId].hasSource() && not solver_->force(~a.lit, nullptr)) {
            return false;
        }
        if (a.inChoice()) {
            addWatch(~a.lit, nId, watch_head_false);
        }
    }
    if (graph_->numNonHcfs() != 0) {
        mini_ = std::make_unique<MinimalityCheck>(s.searchConfig().fwdCheck);
        if (const uint32_t sd = mini_->fwd.signDef) {
            for (NodeId i : irange(startAtom, size32(atoms_))) {
                const AtomNode& a = graph_->getAtom(i);
                if (a.inDisjunctive() && solver_->value(a.lit.var()) == value_free) {
                    auto p = a.lit;
                    if (sd == SolverStrategies::sign_pos || (sd == SolverStrategies::sign_rnd && (i & 1) != 0)) {
                        p = ~p;
                    }
                    solver_->setPref(a.lit.var(), ValueSet::def_value, falseValue(p));
                }
            }
        }
    }
    return true;
}

// initializes a "normal" body, i.e. a body where lower(B) == size(B)
void DefaultUnfoundedCheck::initBody(const BodyPtr& n) {
    assert(n.id < bodies_.size());
    BodyData& data = bodies_[n.id];
    // initialize lower to the number of predecessors from same scc that currently
    // have no source. Once lower is 0, the body can source successors in its scc
    data.lowerOrExt = n.node->countPreds();
    initSuccessors(n, static_cast<Weight_t>(data.lowerOrExt));
}

// initializes an "extended" body, i.e. a count/sum
// creates & populates WS and adds watches to all subgoals
void DefaultUnfoundedCheck::initExtBody(const BodyPtr& n) {
    assert(n.id < bodies_.size() && n.node->extended());
    BodyData& data  = bodies_[n.id];
    uint32_t  preds = n.node->countPreds();
    uint32_t  sets  = (preds + ExtData::SetType::max_count - 1) / ExtData::SetType::max_count;
    auto*     extra = new (::operator new(sizeof(ExtData) + (sets * sizeof(ExtData::SetType)))) ExtData();
    extra->lower    = n.node->extBound();
    extra->slack    = -extra->lower;
    std::uninitialized_fill_n(extra->flags, sets, ExtData::SetType());

    for (unsigned pos = 0; const auto& x : n.node->predecessors()) {
        auto weight   = x.weight();
        auto lit      = x.lit(*graph_);
        extra->slack += weight;
        addExtWatch(~lit, n, (pos << 1) + static_cast<uint32_t>(x.ext()));
        if (x.ext() && not solver_->isFalse(lit)) {
            extra->addToWs(pos, weight);
        }
        ++pos;
    }

    data.lowerOrExt = size32(extended_);
    extended_.push_back(extra);
    initSuccessors(n, extra->lower);
}

// set n as source for its heads if possible and necessary
void DefaultUnfoundedCheck::initSuccessors(const BodyPtr& n, Weight_t lower) {
    if (not solver_->isFalse(n.node->lit)) {
        for (auto aId : n.node->heads()) {
            const AtomNode& a = graph_->getAtom(aId);
            if (a.scc != n.node->scc || lower <= 0) {
                setSource(aId, n);
            }
        }
    }
}

// watches needed to implement extended rules
void DefaultUnfoundedCheck::addExtWatch(Literal p, const BodyPtr& n, uint32_t data) {
    addWatch(p, size32(watches_), watch_subgoal_false);
    ExtWatch w = {n.id, data};
    watches_.push_back(w);
}
/////////////////////////////////////////////////////////////////////////////////////////
// DefaultUnfoundedCheck - Base interface
/////////////////////////////////////////////////////////////////////////////////////////
void DefaultUnfoundedCheck::reason(Solver&, Literal p, LitVec& r) {
    LitView lits;
    if (not activeClause_.empty() && activeClause_[0] == p) {
        lits = {activeClause_.begin() + 1, activeClause_.end()};
    }
    else {
        assert(strategy_ == only_reason && reasons_);
        lits = reasons_[p.var() - 1];
    }
    for (auto lit : lits) { r.push_back(~lit); }
}

bool DefaultUnfoundedCheck::propagateFixpoint(Solver& s, PostPropagator* ctx) {
    bool checkMin = ctx == nullptr && mini_.get() && mini_->partialCheck(s.decisionLevel());
    for (UfsType t; (t = findUfs(s, checkMin)) != ufs_none;) {
        if (not falsifyUfs(t)) {
            resetTodo();
            return false;
        }
    }
    return true;
}

void DefaultUnfoundedCheck::reset() {
    assert(loopAtoms_.empty() && sourceQ_.empty() && ufs_.empty() && todo_.empty());
    // remember assignments from top-level -
    // the reset may come from a stop request and we might
    // want to continue later
    if (solver_->decisionLevel()) {
        invalid_.clear();
    }
}
bool DefaultUnfoundedCheck::valid(Solver& s) {
    if (not mini_.get() || findNonHcfUfs(s) == ufs_none) {
        return true;
    }
    falsifyUfs(ufs_non_poly);
    return false;
}
bool DefaultUnfoundedCheck::isModel(Solver& s) { return DefaultUnfoundedCheck::valid(s); }
bool DefaultUnfoundedCheck::simplify(Solver& s, bool) {
    graph_->simplify(s);
    if (mini_.get()) {
        mini_->scc = 0;
    }
    return false;
}
void DefaultUnfoundedCheck::destroy(Solver* s, bool detach) {
    if (s && detach) {
        s->removePost(this);
        for (uint32_t i : irange(bodies_)) {
            BodyPtr n(getBody(i));
            s->removeWatch(~n.node->lit, this);
            if (n.node->extended()) {
                for (const auto& x : n.node->predecessors()) { s->removeWatch(~x.lit(*graph_), this); }
            }
        }
        for (uint32_t i : irange(atoms_)) {
            if (const AtomNode& a = graph_->getAtom(i); a.inChoice()) {
                s->removeWatch(~a.lit, this);
            }
        }
    }
    PostPropagator::destroy(s, detach);
}
/////////////////////////////////////////////////////////////////////////////////////////
// DefaultUnfoundedCheck - source pointer propagation
/////////////////////////////////////////////////////////////////////////////////////////
// atom has a new source, check if successor bodies are now a valid source
void DefaultUnfoundedCheck::addSource(const AtomNode& atom) {
    for (const auto& x : atom.successors()) {
        BodyData&       data = bodies_[x.id()];
        const BodyNode& node = graph_->getBody(x.id());
        Weight_t        bnd  = 0;
        if (not node.extended()) { // normal body
            bnd = static_cast<Weight_t>(--data.lowerOrExt);
        }
        else { // extended body
            auto* ext = extended_[data.lowerOrExt];
            if (ext->lower > 0 || data.watches == 0) {
                // currently not a source - safely add pred to our watch set
                auto pos = x.position();
                ext->addToWs(pos, node.predWeight(pos, false));
            }
            bnd = ext->lower;
        }
        if (bnd <= 0 && not solver_->isFalse(node.lit)) {
            forwardSource({&node, x.id()});
        }
    }
}
// atom lost its source, check if successor bodies are still a valid source
void DefaultUnfoundedCheck::removeSource(const AtomNode& atom, bool addTodo) {
    for (const auto& x : atom.successors()) {
        BodyData&       data = bodies_[x.id()];
        const BodyNode& node = graph_->getBody(x.id());
        assert(x.normal() == not node.extended());
        if (x.normal()) { // normal body
            if (++data.lowerOrExt == 1 && data.watches != 0) {
                forwardUnsource({&node, x.id()}, addTodo);
            }
        }
        else { // extended body
            auto* ext = extended_[data.lowerOrExt];
            auto  pos = x.position();
            ext->removeFromWs(pos, node.predWeight(pos, false));
            if (ext->lower > 0 && data.watches != 0) {
                // extended bodies don't always become false if a predecessor becomes false
                // eagerly enqueue all successors watching this body
                forwardUnsource({&node, x.id()}, true);
            }
        }
    }
}

// propagates recently set source pointers within one strong component.
void DefaultUnfoundedCheck::propagateSource() {
    while (not sourceQ_.empty()) {
        if (auto atom = sourceQ_.pop_ret(); atoms_[atom].hasSource()) {
            // propagate a newly added source-pointer
            addSource(graph_->getAtom(atom));
        }
        else {
            removeSource(graph_->getAtom(atom), false);
        }
    }
    sourceQ_.clear();
}

// replaces current source of atom with n
void DefaultUnfoundedCheck::updateSource(AtomData& atom, const BodyPtr& n) {
    if (atom.watch() != AtomData::nil_source) {
        --bodies_[atom.watch()].watches;
    }
    atom.setSource(n.id);
    ++bodies_[n.id].watches;
}

// n is a valid source again, forward propagate this information to its heads
void DefaultUnfoundedCheck::forwardSource(const BodyPtr& n) {
    for (auto x : n.node->heads()) {
        if (x != DependencyGraph::sentinel_atom) {
            setSource(x, n);
        }
    }
}

// n is no longer a valid source, forward propagate this information to its heads
void DefaultUnfoundedCheck::forwardUnsource(const BodyPtr& n, bool add) {
    // Treat disjunctions as separate rules when it comes to source pointer propagation.
    // E.g. a | b :- B is (source) propagated as:
    // a :- B, and
    // b :- B
    for (auto aId : n.node->heads()) {
        if (aId != DependencyGraph::sentinel_atom) {
            if (graph_->getAtom(aId).scc != n.node->scc) {
                break;
            }
            if (atoms_[aId].hasSource() && atoms_[aId].watch() == n.id) {
                atoms_[aId].markSourceInvalid();
                sourceQ_.push(aId);
            }
            if (add && atoms_[aId].watch() == n.id) {
                pushTodo(aId);
            }
        }
    }
}

// sets body as source for head if necessary.
// PRE: value(body) != value_false
// POST: source(head) != 0
void DefaultUnfoundedCheck::setSource(NodeId head, const BodyPtr& body) {
    assert(not solver_->isFalse(body.node->lit));
    // For normal rules from not false B follows not false head, but
    // for choice rules this is not the case. Therefore, the
    // check for isFalse(head) is needed so that we do not inadvertently
    // source a head that is currently false.
    if (not atoms_[head].hasSource() && not solver_->isFalse(graph_->getAtom(head).lit)) {
        updateSource(atoms_[head], body);
        sourceQ_.push(head);
    }
}

// This function is called for each body that became invalid during propagation.
// Heads having the body as source have their source invalidated and are added
// to the todo queue. Furthermore, source pointer removal is propagated forward
void DefaultUnfoundedCheck::removeSource(NodeId bodyId) {
    const BodyNode& body = graph_->getBody(bodyId);
    for (auto x : body.heads()) {
        if (atoms_[x].watch() == bodyId) {
            if (atoms_[x].hasSource()) {
                atoms_[x].markSourceInvalid();
                sourceQ_.push(x);
            }
            pushTodo(x);
        }
    }
    propagateSource();
}

/////////////////////////////////////////////////////////////////////////////////////////
// DefaultUnfoundedCheck - Finding & propagating unfounded sets
/////////////////////////////////////////////////////////////////////////////////////////
void DefaultUnfoundedCheck::updateAssignment(const Solver& s) {
    assert(sourceQ_.empty() && ufs_.empty() && pickedExt_.empty());
    for (auto inv : invalid_) {
        uint32_t index = inv >> 2;
        uint32_t type  = inv & 3u;
        if (type == watch_source_false) {
            // a body became false - update atoms having the body as source
            removeSource(index);
        }
        else if (type == watch_head_false) {
            // an atom in the head of a choice rule became false
            // normally head false -> body false and hence the head has its source automatically removed
            // for choice rules we must force source removal explicitly
            if (atoms_[index].hasSource() && not s.isFalse(graph_->getBody(atoms_[index].watch()).lit)) {
                atoms_[index].markSourceInvalid();
                removeSource(graph_->getAtom(index), true);
                propagateSource();
            }
        }
        else if (type == watch_head_true) {
            // TODO: approx. ufs for disjunctive lp
        }
        else if (type == watch_subgoal_false) { // a literal p relevant to an extended body became false
            assert(index < watches_.size());
            const auto& [bodyId, data] = watches_[index];
            const auto& body           = graph_->getBody(bodyId);
            ExtData*    ext            = extended_[bodies_[bodyId].lowerOrExt];
            ext->removeFromWs(data >> 1, body.predWeight(data >> 1, Potassco::test_bit(data, 0)));
            if (ext->lower > 0 && bodies_[bodyId].watches && not bodies_[bodyId].picked && not s.isFalse(body.lit)) {
                // The body is not a valid source but at least one head atom
                // still depends on it: mark body as invalid source
                removeSource(bodyId);
                pickedExt_.push_back(bodyId);
                bodies_[bodyId].picked = 1;
            }
        }
    }
    for (auto e : pickedExt_) { bodies_[e].picked = 0; }
    pickedExt_.clear();
    invalid_.clear();
}

DefaultUnfoundedCheck::UfsType DefaultUnfoundedCheck::findUfs(Solver& s, bool checkMin) {
    // first: remove all sources that were recently falsified
    updateAssignment(s);
    // second: try to re-establish sources.
    while (not todo_.empty()) {
        NodeId head       = todo_.pop_ret();
        atoms_[head].todo = 0;
        if (not atoms_[head].hasSource() && not s.isFalse(graph_->getAtom(head).lit) && not findSource(head)) {
            return ufs_poly; // found an unfounded set - contained in unfounded_
        }
        assert(sourceQ_.empty());
    }
    todo_.clear();
    return not checkMin ? ufs_none : findNonHcfUfs(s);
}

// searches a new source for the atom node head.
// If a new source is found the function returns true.
// Otherwise, the function returns false and unfounded_ contains head
// as well as atoms with no source that circularly depend on head.
bool DefaultUnfoundedCheck::findSource(NodeId headId) {
    assert(ufs_.empty() && invalid_.empty());
    uint32_t newSource = 0;
    pushUfs(headId); // unfounded, unless we find a new source
    while (not ufs_.empty()) {
        headId         = ufs_.pop_ret(); // still marked and in vector!
        AtomData& head = atoms_[headId];
        if (not head.hasSource()) {
            const AtomNode& headNode = graph_->getAtom(headId);
            for (auto bId : headNode.bodies()) {
                BodyPtr bodyNode(getBody(bId));
                if (not solver_->isFalse(bodyNode.node->lit)) {
                    if (bodyNode.node->scc != headNode.scc || isValidSource(bodyNode)) {
                        head.ufs = 0;                // found a new source,
                        setSource(headId, bodyNode); // set the new source
                        propagateSource();           // and propagate it forward
                        ++newSource;
                        break;
                    }
                    else {
                        addUnsourced(bodyNode);
                    }
                }
            }
            if (not head.hasSource()) { // still no source - check again once we are done
                invalid_.push_back(headId);
            }
        }
        else { // head has a source and is thus not unfounded
            ++newSource;
            head.ufs = 0;
        }
    } // while unfounded_.emtpy() == false
    ufs_.rewind();
    if (newSource != 0) {
        // some atoms in unfounded_ have a new source
        // clear queue and check possible candidates for atoms that are still unfounded
        uint32_t visited = size32(ufs_.vec);
        ufs_.clear();
        if (visited != newSource) {
            // add elements that are still unfounded
            for (auto inv : invalid_) {
                if (atoms_[inv].ufs = 1u - atoms_[inv].validS; atoms_[inv].ufs) {
                    ufs_.push(inv);
                }
            }
        }
    }
    invalid_.clear();
    return ufs_.empty();
}

// checks whether the body can source its heads
bool DefaultUnfoundedCheck::isValidSource(const BodyPtr& n) {
    if (not n.node->extended()) {
        return bodies_[n.id].lowerOrExt == 0;
    }
    ExtData* ext = extended_[bodies_[n.id].lowerOrExt];
    if (ext->lower > 0) {
        // Since n is currently not a source, we here know that no literal with a source can depend on this body.
        // Hence, we can safely add all those literals to WS.

        // We check all internal literals here because there may be atoms
        // that were sourced *after* we established the watch set.
        // We check all external literals here because we do not update the body on backtracking.
        // Hence, some external literals that were false may now be true/free.
        for (uint32_t pos = 0; const auto& x : n.node->predecessors()) {
            if (not ext->inWs(pos) && (x.ext() || atoms_[x.id()].hasSource()) && not solver_->isFalse(x.lit(*graph_))) {
                ext->addToWs(pos, x.weight());
            }
            ++pos;
        }
    }
    return ext->lower <= 0;
}

// enqueues all predecessors of this body that currently lack a source
// PRE: isValidSource(n) == false
void DefaultUnfoundedCheck::addUnsourced(const BodyPtr& n) {
    for (const auto& x : n.node->predecessors(true)) {
        if (not atoms_[x.id()].hasSource() && not solver_->isFalse(graph_->getAtomLit(x.id()))) {
            pushUfs(x.id());
        }
    }
}

// falsifies the atoms one by one from the unfounded set stored in unfounded_
bool DefaultUnfoundedCheck::falsifyUfs(UfsType t) {
    activeClause_.clear();
    for (uint32_t dl = 0; not ufs_.empty();) {
        Literal a = graph_->getAtom(ufs_.front()).lit;
        if (not solver_->isFalse(a) && !(assertAtom(a, t) && solver_->propagateUntil(this))) {
            if (t == ufs_non_poly) {
                mini_->schedNext(solver_->decisionLevel(), false);
            }
            break;
        }
        assert(solver_->isFalse(a));
        atoms_[ufs_.pop_ret()].ufs = 0;
        if (ufs_.qFront == 1) {
            dl = solver_->decisionLevel();
        }
        else if (solver_->decisionLevel() != dl) {
            break; /* atoms may no longer be unfounded after backtracking */
        }
    }
    if (not loopAtoms_.empty()) {
        createLoopFormula();
    }
    resetUfs();
    activeClause_.clear();
    return not solver_->hasConflict();
}

// asserts an unfounded atom using the selected reason strategy
bool DefaultUnfoundedCheck::assertAtom(Literal a, UfsType t) {
    if (solver_->isTrue(a) || strategy_ == distinct_reason || activeClause_.empty()) {
        // Conflict, first atom of unfounded set, or distinct reason for each atom requested -
        // compute reason for a being unfounded.
        // We must flush any not yet created loop formula here - the
        // atoms in loopAtoms_ depend on the current reason which is about to be replaced.
        if (not loopAtoms_.empty()) {
            createLoopFormula();
        }
        activeClause_.assign(1, ~a);
        computeReason(t);
    }
    activeClause_[0] = ~a;
    bool tainted     = info_.tagged() || info_.aux();
    bool noClause    = solver_->isTrue(a) || strategy_ == no_reason || strategy_ == only_reason ||
                    (strategy_ == shared_reason && activeClause_.size() > 3 && not tainted);
    if (noClause) {
        if (not solver_->force(~a, this)) {
            return false;
        }
        if (strategy_ == only_reason) {
            reasons_[a.var() - 1].assign(activeClause_.begin() + 1, activeClause_.end());
        }
        else if (strategy_ != no_reason) {
            loopAtoms_.push_back(~a);
        }
        return true;
    }
    else { // learn nogood and assert ~a
        return ClauseCreator::create(*solver_, activeClause_, ClauseCreator::clause_no_prepare, info_).ok();
    }
}
void DefaultUnfoundedCheck::createLoopFormula() {
    assert(activeClause_.size() > 3 && not loopAtoms_.empty());
    Antecedent ante;
    activeClause_[0] = loopAtoms_[0];
    if (loopAtoms_.size() == 1) {
        ante = ClauseCreator::create(*solver_, activeClause_, ClauseCreator::clause_no_prepare, info_).local;
    }
    else {
        assert(not info_.tagged() && not info_.aux());
        ante = LoopFormula::newLoopFormula(*solver_, ClauseRep::prepared(activeClause_, info_), loopAtoms_);
        solver_->addLearnt(ante.constraint(), size32(loopAtoms_) + size32(activeClause_), ConstraintType::loop);
    }
    do {
        Literal p = loopAtoms_.back();
        assert(solver_->isTrue(p));
        if (solver_->reason(p).asUint() != ante.asUint()) {
            assert(solver_->reason(p) == this);
            solver_->setReason(p, ante);
        }
        loopAtoms_.pop_back();
    } while (not loopAtoms_.empty());
}

// computes the reason why a set of atoms is unfounded
void DefaultUnfoundedCheck::computeReason(UfsType t) {
    if (strategy_ == no_reason) {
        return;
    }
    uint32_t ufsScc = graph_->getAtom(ufs_.front()).scc;
    for (auto i = ufs_.qFront; i != ufs_.vec.size(); ++i) {
        if (const auto& atom = graph_->getAtom(ufs_.vec[i]); not solver_->isFalse(atom.lit)) {
            assert(atom.scc == ufsScc);
            for (auto bId : atom.bodies()) {
                if (BodyPtr body(getBody(bId)); t == ufs_poly || not body.node->delta()) {
                    addIfReason(body, ufsScc);
                }
                else {
                    addDeltaReason(body, ufsScc);
                }
            }
        }
    }
    for (auto ext : pickedExt_) { bodies_[ext].picked = 0; }
    pickedExt_.clear();
    info_       = ConstraintInfo(ConstraintType::loop);
    uint32_t rc = not solver_->isFalse(activeClause_[0]) && activeClause_.size() > 100 &&
                  activeClause_.size() > (solver_->decisionLevel() * 10);
    uint32_t dl      = solver_->finalizeConflictClause(activeClause_, info_, rc);
    uint32_t current = solver_->decisionLevel();
    POTASSCO_DEBUG_ASSERT(t == ufs_non_poly || dl == current,
                          "Loop nogood must contain a literal from current DL! (%u;%u)", current, dl);
    if (dl < current && solver_->isUndoLevel()) {
        // cancel active propagation on current level
        cancelPropagation();
        invalid_.clear();
        solver_->undoUntil(dl);
    }
}
// check whether n is external to the current unfounded set, i.e.
// does not depend on the atoms from the unfounded set
bool DefaultUnfoundedCheck::isExternal(const BodyPtr& n, Weight_t& slack) const {
    for (const auto& x : n.node->predecessors(true)) {
        if (atoms_[x.id()].ufs && not solver_->isFalse(graph_->getAtomLit(x.id())) && (slack -= x.weight()) < 0) {
            return false;
        }
    }
    return slack >= 0;
}

// check if n is part of the reason for the current unfounded set
void DefaultUnfoundedCheck::addIfReason(const BodyPtr& n, uint32_t uScc) {
    bool     inF   = solver_->isFalse(n.node->lit);
    Weight_t slack = 0;
    if (not n.node->extended() || n.node->scc != uScc) {
        if (inF && not solver_->seen(n.node->lit) && (n.node->scc != uScc || isExternal(n, slack))) {
            addReasonLit(n.node->lit);
        }
    }
    else if (bodies_[n.id].picked == 0) {
        slack = extended_[bodies_[n.id].lowerOrExt]->slack;
        if (isExternal(n, slack)) {
            if (inF) {
                addReasonLit(n.node->lit);
            }
            else {
                assert(slack >= 0);
                for (const auto& x : n.node->predecessors()) {
                    if (auto lit = x.lit(*graph_); solver_->isFalse(lit)) {
                        addReasonLit(lit);
                        if (slack -= x.weight(); slack < 0) {
                            break;
                        }
                    }
                }
            }
        }
        bodies_[n.id].picked = 1;
        pickedExt_.push_back(n.id);
    }
}

void DefaultUnfoundedCheck::addDeltaReason(const BodyPtr& n, uint32_t uScc) {
    if (bodies_[n.id].picked != 0) {
        return;
    }
    uint32_t bodyAbst =
        solver_->isFalse(n.node->lit) ? solver_->level(n.node->lit.var()) : solver_->decisionLevel() + 1;
    auto headSpan = n.node->heads();
    for (auto it = headSpan.begin(), end = headSpan.end(); it != end; ++it) {
        if (*it != DependencyGraph::sentinel_atom) { // normal head
            if (graph_->getAtom(*it).scc == uScc) {
                addIfReason(n, uScc);
            }
        }
        else { // disjunctive head
            uint32_t reasonAbst = bodyAbst;
            Literal  reasonLit  = n.node->lit;
            bool     inUfs      = false;
            for (++it; *it; ++it) {
                if (atoms_[*it].ufs == 1) {
                    inUfs = true;
                }
                else if (Literal aLit = graph_->getAtom(*it).lit;
                         solver_->isTrue(aLit) && solver_->level(aLit.var()) < reasonAbst) {
                    reasonLit  = ~aLit;
                    reasonAbst = solver_->level(reasonLit.var());
                }
            }
            if (inUfs && reasonAbst && reasonAbst <= solver_->decisionLevel()) {
                addReasonLit(reasonLit);
            }
        }
    }
    bodies_[n.id].picked = 1;
    pickedExt_.push_back(n.id);
}

void DefaultUnfoundedCheck::addReasonLit(Literal p) {
    if (not solver_->seen(p)) {
        solver_->markSeen(p);
        solver_->markLevel(solver_->level(p.var()));
        activeClause_.push_back(p);
        if (solver_->level(p.var()) > solver_->level(activeClause_[1].var())) {
            std::swap(activeClause_[1], activeClause_.back());
        }
    }
}

/////////////////////////////////////////////////////////////////////////////////////////
// DefaultUnfoundedCheck - Minimality check for disjunctive logic programs
/////////////////////////////////////////////////////////////////////////////////////////
DefaultUnfoundedCheck::UfsType DefaultUnfoundedCheck::findNonHcfUfs(Solver& s) {
    assert(invalid_.empty() && loopAtoms_.empty() && (not graph_->numNonHcfs() || mini_->scc < graph_->numNonHcfs()));
    auto components = graph_->nonHcfs();
    for (uint32_t checks = graph_->numNonHcfs(), n = mini_->scc, maxIdx = size32(components); checks--;) {
        s.stats.addTest(s.numFreeVars() != 0);
        const auto& comp = components[n];
        comp->assumptionsFromAssignment(s, loopAtoms_);
        if (not comp->test(s, loopAtoms_, invalid_) || s.hasConflict()) {
            uint32_t pos = 0, minLev = UINT32_MAX;
            for (auto inv : invalid_) {
                if (s.isTrue(graph_->getAtom(inv).lit) && s.level(graph_->getAtom(inv).lit.var()) < minLev) {
                    minLev = s.level(graph_->getAtom(inv).lit.var());
                    pos    = size32(ufs_.vec);
                }
                pushUfs(inv);
            }
            if (pos) {
                std::swap(ufs_.vec.front(), ufs_.vec[pos]);
            }
            invalid_.clear();
            loopAtoms_.clear();
            mini_->scc = n;
            return ufs_non_poly;
        }
        if (++n == maxIdx) {
            n = 0;
        }
        loopAtoms_.clear();
    }
    mini_->schedNext(s.decisionLevel(), true);
    return ufs_none;
}

DefaultUnfoundedCheck::MinimalityCheck::MinimalityCheck(const FwdCheck& afwd)
    : fwd(afwd)
    , high(UINT32_MAX)
    , low(0)
    , next(0)
    , scc(0) {
    if (fwd.highPct > 100) {
        fwd.highPct = 100;
    }
    if (fwd.highStep == 0) {
        fwd.highStep = ~fwd.highStep;
    }
    high = fwd.highStep;
}

bool DefaultUnfoundedCheck::MinimalityCheck::partialCheck(uint32_t level) {
    if (level < low) {
        next -= (low - level);
        low   = level;
    }
    return not next || next == level;
}

void DefaultUnfoundedCheck::MinimalityCheck::schedNext(uint32_t level, bool ok) {
    low  = 0;
    next = UINT32_MAX;
    if (not ok) {
        high = level;
        next = 0;
    }
    else if (fwd.highPct != 0) {
        double p = fwd.highPct / 100.0;
        high     = std::max(high, level);
        low      = level;
        if (low >= high) {
            high += fwd.highStep;
        }
        next = low + static_cast<uint32_t>(std::ceil((high - low) * p));
    }
}
} // namespace Clasp
