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
#include <clasp/asp_preprocessor.h>

#include <clasp/logic_program.h>
#include <clasp/shared_context.h>

namespace Clasp::Asp {
/////////////////////////////////////////////////////////////////////////////////////////
// simple preprocessing
//
// Simplifies the program by computing max consequences.
// Then assign variables to non-trivial supported bodies and atoms.
/////////////////////////////////////////////////////////////////////////////////////////
bool Preprocessor::preprocessSimple() {
    if (not prg_->propagate(true)) {
        return false;
    }
    auto startVar = prg_->ctx()->numVars() + 1;
    // start with initially supported bodies
    VarVec      unitBodies;
    const auto& supported = prg_->getSupportedBodies(true);
    // NOTE: adding heads might result in new supported bodies
    for (auto qFront = static_cast<std::size_t>(0); qFront < supported.size();) {
        auto     id = supported[qFront++];
        PrgBody* b  = prg_->getBody(id);
        if (not b->simplify(*prg_, false)) {
            return false;
        }
        if (b->var() < startVar) {
            if (b->size() != 1) {
                b->assignVar(*prg_);
            }
            else {
                unitBodies.push_back(id);
            }
        }
        // add all heads of b to the "upper"-closure and remove any false/removed atoms from head
        if (not addHeadsToUpper(b) || not b->simplifyHeads(*prg_, true)) {
            return false;
        }
    }
    for (auto id : unitBodies) { prg_->getBody(id)->assignVar(*prg_); }
    return prg_->propagate();
}

bool Preprocessor::addToUpper(PrgHead* head, PrgEdge support) {
    assert(head->relevant() && not head->inUpper());
    if (not head->simplifySupports(*prg_, false)) {
        return false;
    }
    head->assignVar(*prg_, support, eq());
    head->clearSupports();
    head->setInUpper(true);
    return true;
}
/////////////////////////////////////////////////////////////////////////////////////////
// equivalence preprocessing
//
// Computes max consequences and minimizes the number of necessary variables
// by computing equivalence-classes.
/////////////////////////////////////////////////////////////////////////////////////////
bool Preprocessor::preprocessEq(uint32_t maxIters) {
    pass_    = 0;
    maxPass_ = maxIters;
    bodyInfo_.resize(prg_->numBodies() + 1);
    for (auto startVar = prg_->ctx()->numVars();;) {
        ++pass_;
        if (not classifyProgram()) {
            return false;
        }
        if (auto r = simplifyClassifiedProgram(pass_ != maxPass_); r != value_free || pass_ == maxPass_) {
            return r != value_false;
        }
        for (PrgHead* h : prg_->oldAtoms()) { h->setInUpper(false); }
        for (const auto& range : {node_cast<PrgHead>(prg_->disjunctions()), node_cast<PrgHead>(prg_->newAtoms())}) {
            for (PrgHead* h : range) {
                h->setInUpper(false);
                h->clearLiteral(false);
            }
        }
        prg_->ctx()->popVars(prg_->ctx()->numVars() - startVar);
        litToNode_.clear();
    }
}
uint32_t Preprocessor::popFollow(uint32_t& idx) {
    assert(idx < size32(follow_));
    if (dfs_) {
        auto id = follow_.back();
        follow_.pop_back();
        return id;
    }
    return follow_[idx++];
}
// Computes necessary equivalence-classes starting from the supported bodies of a program.
bool Preprocessor::classifyProgram() {
    if (not prg_->propagate(true)) {
        return false;
    }
    VarVec& supported = prg_->getSupportedBodies(true);
    follow_.clear();
    // start from next unclassified supported body
    for (uint32_t root = 0u; root < size32(supported); ++root) { // NOTE: supported might change!
        auto  bodyId = supported[root];
        auto* body   = prg_->getBody(bodyId);
        if (bodyInfo_[bodyId].bSeen == 0 && body->relevant()) {
            for (uint32_t front = 0;;) { // classify body and all bodies following from it
                body = addBodyVar(bodyId);
                if (prg_->hasConflict() || not addHeadsToUpper(body)) {
                    return false;
                }
                if (front == size32(follow_)) {
                    follow_.clear();
                    break;
                }
                bodyId = popFollow(front);
            }
        }
        else if (not body->relevant() && body->hasVar()) {
            body->clearLiteral(false);
        }
    }
    assert(follow_.empty());
    return not prg_->hasConflict();
}

Val_t Preprocessor::simplifyClassifiedProgram(bool more) {
    if (not prg_->propagate()) {
        return value_false;
    }
    VarVec& supported = prg_->getSupportedBodies(false);
    supported.clear();
    // simplify supports
    auto res = value_true;
    for (uint32_t id = 0; auto* b : prg_->bodies()) {
        if (bodyInfo_[id].bSeen == 0 || not b->relevant()) {
            // not bodyInfo_[i].bSeen: body is unsupported
            // not b->relevant()     : body is eq to other body or was derived to false
            // In either case, body is no longer relevant and can be ignored.
            b->clearLiteral(true);
            b->markRemoved();
        }
        else if (auto simp = simplifyBody(b, more, supported); simp != value_true) {
            if (simp == value_false) {
                return simp;
            }
            res = value_free;
        }
        ++id;
    }
    if (not prg_->propagate()) {
        return value_false;
    }
    PrgEdge noSup = PrgEdge::noEdge();
    for (auto u : prg_->unfreeze()) {
        PrgAtom* a = prg_->getAtom(u);
        auto     v = a->value();
        if (not a->simplifySupports(*prg_, true)) {
            return value_false;
        }
        if (not a->inUpper() && v != value_false) {
            if (not prg_->assignValue(a, value_false, noSup)) {
                return value_false;
            }
            if (more && a->hasDep(PrgAtom::dep_all)) {
                res = value_free;
            }
        }
    }
    if (not prg_->propagate()) {
        return value_false;
    }
    bool strong = more && res == value_true;
    for (const auto& range : {node_cast<PrgHead>(prg_->disjunctions()), node_cast<PrgHead>(prg_->newAtoms())}) {
        for (PrgHead* head : range) {
            if (auto simp = simplifyHead(head, strong); simp != value_true) {
                if (simp == value_false) {
                    return simp;
                }
                if (strong) {
                    strong = false;
                    res    = value_free;
                }
            }
        }
    }
    if (not prg_->propagate()) {
        res = value_false;
    }
    return res;
}

// associates a variable with the body if necessary
PrgBody* Preprocessor::addBodyVar(uint32_t bodyId) {
    // make sure we don't add an irrelevant body
    PrgBody* body = prg_->getBody(bodyId);
    assert((body->isSupported() && not body->eq()) || body->hasVar());
    body->clearLiteral(false);   // clear var in case we are iterating
    bodyInfo_[bodyId].bSeen = 1; // mark as seen, so we don't classify the body again
    bool     known          = bodyInfo_[bodyId].known == body->size();
    uint32_t eqId;
    if (not body->simplifyBody(*prg_, known, &eqId) || not body->simplifyHeads(*prg_, false)) {
        prg_->setConflict();
        return body;
    }
    if (superfluous(body)) {
        body->markRemoved();
        return body;
    }
    if (eqId == bodyId) {
        // The body is unique
        body->assignVar(*prg_);
        PrgAtom* aEq = body->size() == 1 ? prg_->getAtom(body->goal(0).var()) : nullptr;
        if (not known) {
            body->markDirty();
        }
        else if (aEq && aEq->var() == body->var()) {
            // Body is equivalent to an atom or its negation
            // Check if the atom is itself equivalent to a body.
            // If so, the body is equivalent to the atom's body.
            if (body->goal(0).sign()) {
                auto dualAtom = getRootAtom(body->literal());
                aEq           = dualAtom != var_max ? prg_->getAtom(dualAtom) : nullptr;
            }
            if (aEq && aEq->support().isBody()) {
                auto rId = aEq->support().node();
                if (PrgBody* r = prg_->getBody(rId); r && r->var() == aEq->var()) {
                    mergeEqBodies(body, rId, false);
                }
            }
        }
    }
    else {
        // body is eq to eq body
        mergeEqBodies(body, eqId, true);
    }
    return body;
}

// Adds all heads of body to the upper closure if not yet present and
// associates variables with the heads if necessary.
// The body b is the supported body that provides a support for the heads.
// RETURN: true if no conflict
// POST  : the addition of atoms to the closure was propagated
bool Preprocessor::addHeadsToUpper(const PrgBody* body) {
    bool ok    = not prg_->hasConflict();
    int  dirty = 0;
    for (auto h : body->heads()) {
        if (not ok) {
            break;
        }
        auto* head    = prg_->getHead(h);
        auto  support = PrgEdge::newEdge(*body, h.type());
        if (head->relevant() && head->value() != value_false) {
            if (body->value() == value_true && head->isAtom()) {
                // Since b is true, it is always a valid support for head, head can never become unfounded.
                // So ignore it during SCC check and unfounded set computation.
                head->setIgnoreScc(true);
                if (support.isNormal() && head->isAtom()) {
                    ok = propagateAtomValue(node_cast<PrgAtom>(head), value_true, support);
                }
            }
            if (not head->inUpper()) {
                // first time we see this head - assign var...
                ok = head->isAtom() ? addAtomToUpper(node_cast<PrgAtom>(head), support)
                                    : addDisjToUpper(node_cast<PrgDisj>(head), support);
            }
            else if (head->support().isNormal()) {
                PrgEdge source = head->support();
                assert(source.isBody());
                if (prg_->getBody(source.node())->var() == body->var()) {
                    // Check if we really need a new variable for head.
                    head->markDirty();
                }
            }
            head->addSupport(support, PrgHead::no_simplify);
        }
        dirty += (head->eq() || head->value() == value_false);
    }
    if (dirty) {
        // remove eq atoms from head
        prg_->getBody(body->id())->markHeadsDirty();
    }
    return ok;
}

bool Preprocessor::addAtomToUpper(PrgAtom* atom, PrgEdge support) {
    return addToUpper(atom, support) && propagateAtomVar(atom, support);
}

bool Preprocessor::addDisjToUpper(PrgDisj* disj, PrgEdge support) {
    bool ok = addToUpper(disj, support);
    if (ok) {
        // add unseen atoms of disjunction to upper
        support = PrgEdge::newEdge(*disj, PrgEdge::choice);
        for (auto a : disj->atoms()) {
            if (PrgAtom* at = prg_->getAtom(a); at->relevant()) {
                ok = at->inUpper() || addAtomToUpper(at, support);
                at->addSupport(support);
                if (not ok) {
                    break;
                }
            }
        }
    }
    return ok;
}

// Propagates that `a` was added to the "upper"-closure.
// If atom a has a truth-value or is eq to a', we'll remove
// it from all bodies. If there is an atom x, s.th. a.lit == ~x.lit, we mark all
// bodies containing both a and x for simplification in order to detect
// duplicates/contradictory body-literals.
// In case that a == a', we also mark all bodies containing a
// for head simplification in order to detect rules like: a' :- a,B. and a' :- B,not a.
bool Preprocessor::propagateAtomVar(PrgAtom* a, PrgEdge source) {
    const auto aId        = a->id();
    PrgAtom*   comp       = nullptr;
    auto       value      = a->value();
    bool       fullEq     = eq();
    bool       removeAtom = value == value_true || value == value_false;
    bool       removeNeg  = removeAtom || value == value_weak_true;
    Literal    aLit       = a->literal();
    if (fullEq) {
        if (getRootAtom(aLit) == var_max) {
            setRootAtom(aLit, aId);
        }
        else if (prg_->mergeEqAtoms(a, getRootAtom(aLit))) {
            assert(source.isBody());
            removeAtom  = true;
            removeNeg   = true;
            value       = a->value();
            PrgBody* bn = prg_->getBody(source.node());
            a->setEqGoal(posLit(a->id()));
            // set positive eq goal - replace if a == {not a'}, replace a with not a' in bodies
            if (getRootAtom(~aLit) != var_max && bn->literal() == aLit && bn->size() == 1 && bn->goal(0).sign()) {
                a->setEqGoal(negLit(getRootAtom(~aLit)));
            }
            a->clearLiteral(true); // equivalent atoms don't need vars
        }
        else {
            return false;
        }
    }
    if (getRootAtom(~aLit) != var_max) {
        PrgAtom* negA = prg_->getAtom(getRootAtom(~aLit));
        assert(aLit == ~negA->literal());
        // propagate any truth-value to complementary eq-class
        auto     cv   = value_free;
        uint32_t mark = 0;
        if (value != value_free && (cv = (value_false | (value ^ value_true))) != negA->value()) {
            mark = 1;
            if (not propagateAtomValue(negA, cv, PrgEdge::noEdge())) {
                return false;
            }
        }
        if (not removeAtom) {
            for (auto dep : (comp = negA)->deps()) {
                bodyInfo_[dep.var()].mBody = 1;
                if (mark) {
                    prg_->getBody(dep.var())->markDirty();
                }
            }
        }
    }
    for (auto dep : a->deps()) {
        auto bodyId = dep.var();
        if (PrgBody* bn = prg_->getBody(bodyId); bn->relevant()) {
            bool wasSup = bn->isSupported();
            bool isSup  = wasSup || (value != value_false && not dep.sign() && bn->propagateSupported(aId));
            bool seen   = false;
            bool dirty  = removeAtom || (removeNeg && dep.sign());
            if (fullEq) {
                seen   = bodyInfo_[bodyId].bSeen != 0;
                dirty |= bodyInfo_[bodyId].mBody == 1;
                if (++bodyInfo_[bodyId].known == bn->size() && not seen && isSup) {
                    follow_.push_back(bodyId);
                    seen = true;
                }
            }
            if (not seen && isSup && not wasSup) {
                prg_->getSupportedBodies(false).push_back(bodyId);
            }
            if (dirty) {
                bn->markDirty();
                if (a->eq()) {
                    bn->markHeadsDirty();
                }
            }
        }
    }
    if (removeAtom) {
        a->clearDeps(PrgAtom::dep_all);
    }
    else if (removeNeg) {
        a->clearDeps(PrgAtom::dep_neg);
    }
    if (comp) {
        for (auto dep : comp->deps()) { bodyInfo_[dep.var()].mBody = 0; }
    }
    return true;
}

// Propagates the assignment of val to atom.
bool Preprocessor::propagateAtomValue(PrgAtom* atom, Val_t val, PrgEdge sup) {
    // No backpropagation possible because supports are not yet fully established.
    return prg_->assignValue(atom, val, sup) && prg_->propagate(false);
}

bool Preprocessor::mergeEqBodies(PrgBody* body, uint32_t rootId, bool equalLits) {
    PrgBody* root = prg_->mergeEqBodies(body, rootId, equalLits, false);
    if (root && root != body && bodyInfo_[root->id()].bSeen == 0) {
        // If root is not yet classified, we can ignore body.
        // The heads of body are added to the "upper"-closure
        // once root is eventually classified.
        body->clearHeads();
        body->markRemoved();
    }
    return root != nullptr;
}

bool Preprocessor::hasRootLiteral(const PrgBody* body) const {
    return body->size() >= 1 && getRootAtom(body->literal()) == var_max && getRootAtom(~body->literal()) == var_max;
}

// Pre: body is simplified!
bool Preprocessor::superfluous(const PrgBody* body) const {
    if (not body->relevant()) {
        return true;
    }
    if (not body->inRule()) {
        if (body->value() == value_free) {
            return true;
        }
        if (body->bound() <= 0) {
            return true;
        }
        if (body->size() == 1) {
            // unit constraint
            auto exp = static_cast<Val_t>(body->value() ^ static_cast<int>(body->goal(0).sign()));
            auto got = prg_->getAtom(body->goal(0).var())->value();
            assert(got != value_free || not prg_->options().backprop);
            return got != value_free && (got & value_true) == (exp & value_true);
        }
    }
    return false;
}

// Simplify the classified body with the given id.
// Return:
//  value_false    : conflict
//  value_true     : ok
//  value_weak_true: ok but program should be reclassified
Val_t Preprocessor::simplifyBody(PrgBody* b, bool reclass, VarVec& supported) {
    assert(b->relevant() && bodyInfo_[b->id()].bSeen == 1);
    bodyInfo_[b->id()].bSeen = 0;
    bodyInfo_[b->id()].known = 0;
    auto hadHeads            = b->hasHeads();
    auto hasRoot             = hasRootLiteral(b);
    auto eqId                = b->id();
    if (not b->simplify(*prg_, true, &eqId)) {
        return value_false;
    }
    auto ret = value_true;
    if (reclass) {
        if (hadHeads && b->value() == value_false) {
            assert(b->hasHeads() == false);
            // New false body. If it was derived to false, we can ignore the body.
            // Otherwise, we have a new integrity constraint.
            if (not b->relevant()) {
                b->clearLiteral(true);
            }
        }
        else if (b->var() != 0 && superfluous(b)) {
            // Body is no longer needed. All heads are either superfluous or equivalent
            // to other atoms.
            // Reclassify only if var is not used
            if (getRootAtom(b->literal()) == var_max) {
                ret = value_weak_true;
            }
            b->clearLiteral(true);
            b->markRemoved();
        }
        else if (b->value() == value_true && b->var() != 0) {
            // New fact body
            for (auto h : b->heads()) {
                if (h.isNormal() && prg_->getHead(h)->var() != 0) {
                    ret = value_weak_true;
                    break;
                }
            }
            b->markDirty();
        }
    }
    if (b->relevant() && eqId != b->id() && (reclass || prg_->getBody(eqId)->var() == b->var())) {
        // Body is now eq to some other body - reclassify if body var is not needed
        auto bVar = b->var();
        prg_->mergeEqBodies(b, eqId, true, true);
        if (hasRoot && bVar != b->var()) {
            ret = value_weak_true;
        }
    }
    if (b->relevant() && b->resetSupported()) {
        supported.push_back(b->id());
    }
    return ret;
}

// Simplify the classified head h.
// Update list of bodies defining this head and check
// if atom or disjunction has a distinct var, although it is eq to some rule body.
// Return:
//  value_false    : conflict
//  value_true     : ok
//  value_weak_true: ok but atom should be reclassified
Val_t Preprocessor::simplifyHead(PrgHead* h, bool reclassify) {
    if (not h->hasVar() || not h->relevant()) {
        // unsupported or eq
        h->clearLiteral(false);
        h->markRemoved();
        h->clearSupports();
        h->setInUpper(false);
        return value_true;
    }
    assert(h->inUpper());
    auto     v           = h->value();
    PrgEdge  support     = h->support();
    uint32_t numSuppLits = 0;
    if (not h->simplifySupports(*prg_, true, &numSuppLits)) {
        return value_false;
    }
    if (reclassify) {
        if (numSuppLits == 0 && h->hasVar()) {
            // unsupported head does not need a variable
            return value_weak_true;
        }
        if (h->support() != support) {
            // support for head has changed
            return value_weak_true;
        }
        if (auto numSupps = h->numSupports();
            (support.isNormal() && numSupps == 1) || (numSupps > 1 && numSuppLits == 1 && h->isAtom())) {
            assert(support.isBody());
            if (PrgBody* supBody = prg_->getBody(support.node()); supBody->literal() != h->literal()) {
                if (numSupps > 1) {
                    // atom is equivalent to one of its bodies
                    EdgeVec temp;
                    h->clearSupports(temp);
                    support = temp[0];
                    for (auto s : temp) {
                        assert(not s.isDisj());
                        PrgBody* bn = prg_->getBody(s.node());
                        if (s.isNormal() && bn->size() == 1 && bn->goal(0).sign()) {
                            support = s;
                        }
                        bn->removeHead(h, s.type());
                    }
                    supBody = prg_->getBody(support.node());
                    supBody->addHead(h, support.type());
                    if (not supBody->simplifyHeads(*prg_, true)) {
                        return value_false;
                    }
                }
                if (h->value() == value_weak_true || h->value() == value_true) {
                    supBody->assignValue(h->value());
                    supBody->propagateValue(*prg_, true);
                }
                return value_weak_true;
            }
        }
    }
    if (v != h->value() && (h->value() == value_false || (h->value() == value_true && h->var() != 0))) {
        return value_weak_true;
    }
    return value_true;
}

} // namespace Clasp::Asp
