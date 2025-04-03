//
// Copyright (c) 2009-present Benjamin Kaufmann
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
#include <clasp/lookahead.h>

#include <algorithm>
namespace Clasp {
/////////////////////////////////////////////////////////////////////////////////////////
// Lookahead scoring
/////////////////////////////////////////////////////////////////////////////////////////
constexpr bool isAny(VarType x, VarType y) { return Potassco::test_any(+x, +y); }

uint32_t ScoreLook::countNant(const Solver& s, LitView lits) {
    return static_cast<uint32_t>(1 + std::ranges::count_if(lits, [&](Literal x) { return s.varInfo(x.var()).nant(); }));
}
void ScoreLook::scoreLits(const Solver& s, LitView lits) {
    assert(not lits.empty());
    uint32_t sc = not nant ? size32(lits) : countNant(s, lits);
    auto     v  = lits[0].var();
    assert(validVar(v));
    score[v].setScore(lits[0], sc);
    if (addDeps) {
        if ((score[v].testedBoth() || mode == score_max) && greater(v, best)) {
            best = v;
        }
        for (auto lit : lits) {
            v = lit.var();
            if (validVar(v) && isAny(s.varInfo(v).type(), types)) {
                if (not score[v].seen()) {
                    deps.push_back(v);
                }
                score[v].setDepScore(lit, sc);
            }
        }
    }
}
void ScoreLook::clearDeps() {
    while (not deps.empty()) {
        score[deps.back()] = VarScore();
        deps.pop_back();
    }
    best  = 0;
    limit = UINT32_MAX;
}
bool ScoreLook::greater(Var_t lhs, Var_t rhs) const {
    uint32_t rhsMax, rhsMin;
    score[rhs].score(rhsMax, rhsMin);
    return mode == score_max ? greaterMax(lhs, rhsMax) : greaterMaxMin(lhs, rhsMax, rhsMin);
}
/////////////////////////////////////////////////////////////////////////////////////////
// Lookahead propagator
/////////////////////////////////////////////////////////////////////////////////////////
Lookahead::Lookahead(const Params& p)
    : nodes_(2, LitNode(lit_true))
    , last_(head_id) // circular list
    , pos_(head_id)  // lookahead start pos
    , top_(static_cast<uint32_t>(-2))
    , limit_(p.lim) {
    head()->next = head_id;
    undo()->next = UINT32_MAX;
    if (p.type != VarType::hybrid) {
        score.mode = ScoreLook::score_max_min;
    }
    else {
        score.mode = ScoreLook::score_max;
    }
    score.types = p.type;
    if (p.topLevelImps) {
        head()->lit.flag();
    }
    score.nant = p.restrictNant;
}

Lookahead::~Lookahead() = default;

void Lookahead::detach(Solver& s) {
    s.removePost(this);
    while (saved_.size() > 1) {
        s.removeUndoWatch(size32(saved_) - 1, this);
        saved_.pop_back();
    }
}
void Lookahead::destroy(Solver* s, bool detach) {
    if (s && detach) {
        Lookahead::detach(*s);
    }
    PostPropagator::destroy(s, detach);
}

uint32_t Lookahead::priority() const { return prio; }

void Lookahead::clear() {
    score.clearDeps();
    while (not saved_.empty()) {
        if (saved_.back() != UINT32_MAX) {
            splice(saved_.back());
        }
        saved_.pop_back();
    }
    LookList(2, *head()).swap(nodes_);
    head()->next = head_id;
    undo()->next = UINT32_MAX;
    last_        = head_id;
    top_         = UINT32_MAX;
}

bool Lookahead::init(Solver& s) {
    ScoreLook& sc = score;
    sc.clearDeps();
    Var_t start = size32(sc.score);
    sc.score.resize(s.numVars() + 1);
    uint32_t add   = 0;
    uint32_t nants = 0;
    if (start < size32(sc.score)) {
        const VarType types   = sc.types;
        const bool    uniform = types != VarType::hybrid;
        for (auto v : s.vars(start)) {
            if (s.value(v) == value_free && isAny(s.varInfo(v).type(), types)) {
                ++add;
                nants += s.varInfo(v).nant();
            }
        }
        nodes_.reserve(nodes_.size() + add);
        for (auto v : s.vars(start)) {
            if (s.value(v) == value_free && isAny(s.varInfo(v).type(), types)) {
                append(Literal(v, s.varInfo(v).preferredSign()), uniform || s.varInfo(v).type() == VarType::hybrid);
            }
        }
    }
    if (add && score.nant) {
        score.nant = add != nants && nants != 0;
    }
    return true;
}

void Lookahead::append(Literal p, bool testBoth) {
    node(last_)->next = static_cast<NodeId>(nodes_.size());
    nodes_.push_back(LitNode(p));
    last_             = node(last_)->next;
    node(last_)->next = head_id;
    // remember to also test ~p by setting watched-flag
    if (testBoth) {
        node(last_)->lit.flag();
    }
}

// test p and optionally ~p if necessary
bool Lookahead::test(Solver& s, Literal p) {
    return (score.score[p.var()].seen(p) || s.test(p, this)) &&
           (not p.flagged() || score.score[p.var()].seen(~p) || s.test(~p, this)) && (imps_.empty() || checkImps(s, p));
}

bool Lookahead::checkImps(Solver& s, Literal p) {
    assert(not imps_.empty());
    bool ok = not score.score[p.var()].testedBoth() ||
              std::ranges::all_of(imps_, [&](Literal x) { return not s.hasConflict() && s.force(x, lit_true); });
    imps_.clear();
    return ok && (s.queueSize() == 0 || s.propagateUntil(this));
}

// failed-literal detection - stop on failed-literal
bool Lookahead::propagateLevel(Solver& s) {
    assert(not s.hasConflict());
    saved_.resize(s.decisionLevel() + 1, UINT32_MAX);
    uint32_t undoId = saved_[s.decisionLevel()];
    if (undoId == UINT32_MAX) {
        undoId = undo_id;
        if (s.decisionLevel() != 0) {
            s.addUndoWatch(s.decisionLevel(), this);
        }
    }
    static constexpr uint32_t look_limit = 100;
    score.clearDeps();
    score.addDeps   = true;
    uint32_t& limit = score.limit;
    Literal   p     = node(pos_)->lit;
    bool      ok    = s.value(p.var()) != value_free || test(s, p);
    for (LitNode* r = node(pos_); r->next != pos_ && ok;) {
        if (not s.clearSplitRequest()) {
            limit = UINT32_MAX;
        }
        else if (limit == UINT32_MAX) {
            limit = look_limit;
        }
        else if (--limit == 0) {
            s.sharedContext()->report("Stopping lookahead", &s);
            break;
        }
        p = node(r->next)->lit;
        if (s.value(p.var()) == value_free) {
            if (test(s, p)) {
                r = node(r->next);
            }
            else {
                pos_ = r->next;
                ok   = false;
            }
        }
        else if (r->next != last_ && r->next != head_id) {
            // unlink from candidate list
            NodeId t = r->next;
            r->next  = node(t)->next;
            // append to undo list
            LitNode* u    = node(undoId);
            node(t)->next = u->next;
            u->next       = t;
            undoId        = t;
        }
        else {
            r = node(r->next);
        } // keep iterators valid; never unlink last node and dummy head
    }
    saved_.back() = undoId;
    return ok;
}

bool Lookahead::propagateFixpoint(Solver& s, PostPropagator* ctx) {
    if ((empty() || top_ == s.numAssignedVars()) && not score.deps.empty()) {
        // nothing to lookahead
        return true;
    }
    bool     ok = true;
    uint32_t dl;
    for (dl = s.decisionLevel(); not propagateLevel(s); dl = s.decisionLevel()) {
        // some literal failed
        // resolve and propagate conflict
        assert(s.decisionLevel() >= dl);
        if (not s.resolveConflict() || not s.propagateUntil(this)) {
            ok = false;
            score.clearDeps();
            break;
        }
    }
    if (ok && dl == 0 && score.limit > 0) {
        // remember top-level size - no need to redo lookahead
        // on level 0 unless we learn a new implication
        assert(s.queueSize() == 0);
        top_ = s.numAssignedVars();
        discardVec(imps_);
    }
    if (not ctx && limit_ && --limit_ == 0) {
        this->destroy(&s, true);
    }
    return ok;
}

// splice list [undo_.next, ul] back into candidate list
void Lookahead::splice(NodeId ul) {
    assert(ul != UINT32_MAX);
    if (ul != undo_id) {
        assert(undo()->next != UINT32_MAX);
        // unlink from undo list
        LitNode* ulNode = node(ul);
        NodeId   first  = undo()->next;
        undo()->next    = ulNode->next;
        // splice into look-list
        ulNode->next = head()->next;
        head()->next = first;
    }
}

void Lookahead::undoLevel(Solver& s) {
    if (s.decisionLevel() == saved_.size()) {
        cancelPropagation();
        auto lits = s.levelLits(s.decisionLevel());
        score.scoreLits(s, lits);
        if (s.decisionLevel() == static_cast<uint32_t>(head()->lit.flagged())) {
            if (const Literal* b = lits.data(); b->flagged()) {
                // remember current DL for b
                auto dist = size32(lits);
                imps_.assign(b + 1, b + std::min(dist, static_cast<uint32_t>(2048)));
            }
            else if (score.score[b->var()].testedBoth() && not imps_.empty()) {
                // all true lits in imps_ follow from both *b and ~*b
                // and are therefore implied
                erase_if(imps_, [&s](Literal lit) { return not s.isTrue(lit); });
            }
        }
    }
    else {
        assert(saved_.size() >= s.decisionLevel() + 1);
        saved_.resize(s.decisionLevel() + 1);
        NodeId n = saved_.back();
        saved_.pop_back();
        splice(n);
        assert(node(last_)->next == head_id);
        score.clearDeps();
    }
}

Literal Lookahead::heuristic(Solver& s) {
    if (s.value(score.best) != value_free) {
        // no candidate available
        return lit_true;
    }
    ScoreLook& sc     = score;
    Literal    choice = Literal(sc.best, sc.score[sc.best].prefSign());
    if (!sc.deps.empty() && sc.mode == ScoreLook::score_max_min && sc.limit > 0) {
        // compute heuristic values for candidates skipped during last lookahead
        uint32_t min, max;
        sc.score[sc.best].score(max, min);
        sc.addDeps           = false;
        bool              ok = true;
        LitVec::size_type i  = 0;
        do {
            auto      v  = sc.deps[i];
            VarScore& vs = sc.score[v];
            if (s.value(v) == value_free) {
                uint32_t vMin, vMax;
                vs.score(vMax, vMin);
                if (vMin == 0 || vMin > min || (vMin == min && vMax > max)) {
                    uint32_t neg = vs.score(negLit(v)) > 0 ? vs.score(negLit(v)) : max + 1;
                    uint32_t pos = vs.score(posLit(v)) > 0 ? vs.score(posLit(v)) : max + 1;
                    if (not vs.tested(negLit(v))) {
                        ok  = s.test(negLit(v), this);
                        neg = vs.score(negLit(v));
                        --sc.limit;
                    }
                    if (ok && (neg > min || (neg == min && pos > max)) && not vs.tested(posLit(v)) && sc.limit > 0) {
                        ok = s.test(posLit(v), this);
                        --sc.limit;
                    }
                }
                if (vs.testedBoth() && sc.greaterMaxMin(v, max, min)) {
                    vs.score(max, min);
                    choice = Literal(v, vs.prefSign());
                }
            }
        } while (++i != sc.deps.size() && ok && sc.limit > 0);
        if (not ok) {
            // One of the candidates failed. Since none of them failed
            // during previous propagation, this indicates that
            // either some post propagator has wrong priority or
            // parallel solving is active and a stop conflict was set.
            // Since we can't resolve the problem here, we simply return the
            // literal that caused the conflict
            assert(s.hasConflict());
            return lit_false;
        }
    }
    return choice;
}
/////////////////////////////////////////////////////////////////////////////////////////
// Lookahead heuristic
/////////////////////////////////////////////////////////////////////////////////////////
UnitHeuristic::UnitHeuristic() = default;
Lookahead* UnitHeuristic::getLookahead(const Solver& s) {
    return static_cast<Lookahead*>(s.getPost(Lookahead::priority_reserved_look));
}
void UnitHeuristic::endInit(Solver& s) {
    if (not getLookahead(s)) {
        s.addPost(new Lookahead(VarType::atom));
    }
}
Literal UnitHeuristic::doSelect(Solver& s) {
    auto* look = getLookahead(s);
    if (Literal x = look ? look->heuristic(s) : lit_true; x != lit_true) {
        return x;
    }
    return SelectFirst::doSelect(s);
}
/////////////////////////////////////////////////////////////////////////////////////////
// Restricted Lookahead heuristic - lookahead and heuristic for a limited number of ops
/////////////////////////////////////////////////////////////////////////////////////////
class UnitHeuristic::Restricted final : public UnitHeuristic {
public:
    static inline SelectFirst ignore;
    explicit Restricted(DecisionHeuristic* other) : other_(other) { assert(other_); }
    ~Restricted() override {
        if (other_ != &ignore) {
            delete other_;
        }
    }
    Literal doSelect(Solver& s) override {
        auto choice = lit_true;
        if (other_ != &ignore) {
            if (auto* look = getLookahead(s); not look || not look->hasLimit()) {
                choice = other_->doSelect(s);
                if (auto* h = std::exchange(other_, &ignore); s.heuristic() == this) {
                    s.setHeuristic(h);
                }
            }
            else {
                choice = look->heuristic(s);
            }
        }
        if (choice == lit_true) {
            choice = other_->doSelect(s);
        }
        return choice;
    }
    // heuristic interface - forward to other
    void startInit(const Solver& s) override { other_->startInit(s); }
    void endInit(Solver& s) override { other_->endInit(s); }
    void setConfig(const HeuParams& p) override { other_->setConfig(p); }
    void detach(Solver& s) override { other_->detach(s); }
    void simplify(const Solver& s, LitView sp) override { other_->simplify(s, sp); }
    void undo(const Solver& s, LitView undo) override { other_->undo(s, undo); }
    void updateReason(const Solver& s, LitView x, Literal r) override { other_->updateReason(s, x, r); }
    bool bump(const Solver& s, WeightLitView w, double d) override { return other_->bump(s, w, d); }
    void newConstraint(const Solver& s, LitView lits, ConstraintType t) override { other_->newConstraint(s, lits, t); }
    void updateVar(const Solver& s, Var_t v, uint32_t n) override { other_->updateVar(s, v, n); }
    Literal selectRange(Solver& s, LitView range) override { return other_->selectRange(s, range); }

private:
    DecisionHeuristic* other_;
};

UnitHeuristic* UnitHeuristic::restricted(DecisionHeuristic* other) { return new Restricted(other); }
} // namespace Clasp
