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

#include <clasp/weight_constraint.h>

#include <clasp/clause.h>
#include <clasp/solver.h>
#include <clasp/util/misc_types.h>

#include <algorithm>

#if defined(__GNUC__) && __GNUC__ >= 8
#pragma GCC diagnostic ignored "-Wclass-memaccess"
#endif

namespace Clasp {
/////////////////////////////////////////////////////////////////////////////////////////
// WeightLitsRep
/////////////////////////////////////////////////////////////////////////////////////////
// Removes assigned and merges duplicate/complementary literals.
// return: achievable weight
// post  : lits is sorted by decreasing weights
auto WeightLitsRep::create(Solver& s, WeightLitVec& lits, Weight_t bound) -> WeightLitsRep {
    // Step 0: Ensure s has all relevant problem variables
    if (s.numProblemVars() > s.numVars() && not lits.empty()) {
        s.acquireProblemVar(std::ranges::max_element(lits)->lit.var());
    }
    // Step 1: remove assigned/superfluous literals and merge duplicate/complementary ones
    auto oEnd = lits.begin(); // [lits.begin(), oEnd) is the output range
    for (auto& [x, weight] : lits) {
        if (weight < 0) {
            weight = -weight;
            x      = ~x;
            POTASSCO_CHECK_PRE(bound < 0 || (weight_max - bound) >= weight, "bound out of range");
            bound += weight;
        }
        if (weight == 0 || s.topValue(x.var()) != value_free) {
            bound -= weight * s.isTrue(x);
        }
        else if (not s.seen(x.var())) { // first time we see x, keep and mark x
            *oEnd++ = {x.unflag(), weight};
            s.markSeen(x);
        }
        else if (not s.seen(~x)) { // multi-occurrences of x, merge
            auto oIt = std::find_if(lits.begin(), oEnd, [c = x](const auto& o) { return o.lit == c; });
            POTASSCO_ASSERT(oIt != oEnd);
            oIt->weight += weight;
        }
        else { // complementary literals ~x x
            auto oIt = std::find_if(lits.begin(), oEnd, [c = ~x](const auto& o) { return o.lit == c; });
            POTASSCO_ASSERT(oIt != oEnd);
            bound       -= weight;        // decrease by min(w(~x), w(x)) ; assume w(~x) > w(x)
            oIt->weight -= weight;        // keep ~x,
            if (oIt->weight < 0) {        // actually, w(x) > w(~x),
                oIt->lit    = x.unflag(); // replace ~x with x
                oIt->weight = -oIt->weight;
                s.clearSeen(x.var());
                s.markSeen(x);
                bound += oIt->weight; // and correct the bound
            }
            else if (oIt->weight == 0) { // w(~x) == w(x) - drop both lits
                s.clearSeen(x.var());
                std::copy(oIt + 1, oEnd--, oIt);
            }
        }
    }
    truncateVec(lits, oEnd);
    // Step 2: compute min,max, achievable weight and clear flags set in step 1
    Weight_t sumW = 0;
    Weight_t minW = weight_max, maxW = 1;
    Weight_t bnd = std::max(bound, 1);
    for (auto& [lit, weight] : lits) {
        assert(weight > 0);
        s.clearSeen(lit.var());
        if (weight > maxW) {
            maxW = weight = std::min(weight, bnd);
        }
        if (weight < minW) {
            minW = weight;
        }
        POTASSCO_CHECK((weight_max - sumW) >= weight, EOVERFLOW, "Sum of weights out of range");
        sumW += weight;
    }
    // Step 3: sort by decreasing weight
    if (maxW != minW) {
        Potassco::radixSort(lits,
                            [maxW](const WeightLiteral& lit) { return static_cast<uint32_t>(maxW - lit.weight); });
    }
    else if (minW != 1) {
        // disguised cardinality constraint
        bound = (bound + (minW - 1)) / minW;
        sumW  = (sumW + (minW - 1)) / minW;
        for (auto& [_, weight] : lits) { weight = 1; }
    }
    return {.lits = lits.data(), .size = size32(lits), .bound = bound, .reach = sumW};
}
/////////////////////////////////////////////////////////////////////////////////////////
// WeightConstraint::WL
/////////////////////////////////////////////////////////////////////////////////////////
WeightConstraint::WL::WL(uint32_t s, bool shared, bool hasW) : sz(s), rc(shared), w(hasW) {}
auto WeightConstraint::WL::address() -> uint8_t* {
    return reinterpret_cast<unsigned char*>(this) - (sizeof(uint32_t) * rc);
}
auto WeightConstraint::WL::clone() -> WL* {
    if (shareable()) {
        reinterpret_cast<RefCount*>(address())->add();
        return this;
    }
    uint32_t litSize = (size() << static_cast<uint32_t>(weights())) * sizeof(Literal);
    WL*      x       = new (::operator new(sizeof(WL) + litSize)) WL(size(), false, weights());
    std::memcpy(x->lits, this->lits, litSize);
    return x;
}
void WeightConstraint::WL::release() {
    unsigned char* x = address();
    if (not shareable() || reinterpret_cast<RefCount*>(x)->release()) {
        ::operator delete(x);
    }
}
auto WeightConstraint::WL::refCount() const -> uint32_t {
    assert(shareable());
    return *reinterpret_cast<const RefCount*>(const_cast<WL*>(this)->address());
}
auto WeightConstraint::WL::maxVar() const -> Var_t {
    Var_t mx = 0;
    for (auto i : irange(size())) { mx = std::max(mx, var(i)); }
    return mx;
}
/////////////////////////////////////////////////////////////////////////////////////////
// WeightConstraint
/////////////////////////////////////////////////////////////////////////////////////////
auto WeightConstraint::create(Solver& s, Literal w, WeightLitVec& lits, Weight_t bound, CreateFlag flags) -> Result {
    WeightLitsRep rep = WeightLitsRep::create(s, lits, bound);
    return doCreate(s, w, rep, flags);
}
auto WeightConstraint::create(Solver& s, Literal w, WeightLitsRep& rep, CreateFlag flags) -> Result {
    return doCreate(s, w, rep, flags);
}
auto WeightConstraint::propagate(Solver& s, WeightLitsRep& rep, Literal w, uint32_t act) -> Val_t {
    auto rightImp = act == ffb_btb;
    if (rep.sat()) { // trivially SAT
        rightImp || s.force(w);
        return value_true;
    }
    if (rep.unsat()) { // trivially UNSAT
        act == ftb_bfb || s.force(~w);
        return value_false;
    }
    if (s.topValue(w.var()) == value_free || (act != both_active && s.isTrue(w) != rightImp)) {
        return value_free;
    }
    // backward propagate
    bool     bpTrue = s.isTrue(w);
    Weight_t bnd    = bpTrue ? (rep.reach - rep.bound) + 1 : rep.bound;
    while (rep.lits->weight >= bnd) {
        const auto& [lit, weight]  = *rep.lits;
        rep.reach                 -= weight;
        if (not s.force(bpTrue ? lit : ~lit, nullptr)) {
            return value_false;
        }
        if ((bpTrue && (rep.bound -= weight) <= 0) || --rep.size == 0) {
            return rep.sat() ? value_true : value_false;
        }
        ++rep.lits;
    }
    if (rep.lits->weight > 1 && rep.lits->weight == rep.lits[rep.size - 1].weight) {
        bnd       = rep.lits->weight;
        rep.bound = (rep.bound + (bnd - 1)) / bnd;
        rep.reach = (rep.reach + (bnd - 1)) / bnd;
        for (uint32_t i = 0; i != rep.size && rep.lits[i].weight != 1; ++i) { rep.lits[i].weight = 1; }
    }
    return value_free;
}

auto WeightConstraint::doCreate(Solver& s, Literal w, WeightLitsRep& rep, CreateFlag flags) -> Result {
    uint32_t act;
    switch (constexpr auto dirMask = create_only_btb | create_only_bfb; flags & dirMask) {
        default:
            act    = both_active;
            flags &= ~dirMask;
            break;
        case create_only_btb: act = ffb_btb; break;
        case create_only_bfb: act = ftb_bfb; break;
    }
    s.acquireProblemVar(w.var());
    if (s.decisionLevel() > 0 && s.isUndoLevel() && not Potassco::test(flags, create_no_imp)) {
        if (auto imp = implicationLevel(s, w, rep, flags); imp < s.decisionLevel()) {
            s.undoUntil(imp);
        }
    }
    // Propagate top-level assignment
    auto state = propagate(s, rep, w, act);
    if (s.hasConflict()) {
        return Result{nullptr, false};
    }
    if (state != value_free) {
        return Result{nullptr};
    }
    if (Potassco::test(flags, create_no_add)) {
        flags |= create_explicit;
    }
    if ((rep.bound == 1 || rep.bound == rep.reach) && not Potassco::test(flags, create_explicit) &&
        act == both_active) {
        LitVec clause;
        clause.reserve(1 + rep.size);
        Literal bin[2];
        bool    disj = rep.bound == 1; // con == disjunction or con == conjunction
        bool    sat  = false;
        clause.push_back(w ^ disj);
        for (const auto& [lit, _] : rep.literals()) {
            bin[0] = ~clause[0];
            bin[1] = lit ^ disj;
            if (bin[0] != ~bin[1]) {
                if (bin[0] != bin[1]) {
                    clause.push_back(~bin[1]);
                }
                if (not s.add(ClauseRep::create(bin))) {
                    return Result{nullptr, false};
                }
            }
            else {
                sat = true;
            }
        }
        return Result{nullptr, sat || ClauseCreator::create(s, clause, {})};
    }
    assert(rep.open());
    if (not s.sharedContext()->physicalShareProblem()) {
        flags |= create_no_share;
    }
    if (s.sharedContext()->frozen()) {
        flags |= (create_no_freeze | create_no_share);
    }
    bool     hasW = rep.hasWeights();
    uint32_t size = 1 + rep.size;
    uint32_t nb   = sizeof(WeightConstraint) + (size + static_cast<uint32_t>(hasW)) * sizeof(UndoInfo);
    uint32_t wls  = sizeof(WL) + (size << static_cast<uint32_t>(hasW)) * sizeof(Literal);
    void*    m;
    WL*      sL;
    if (Potassco::test(flags, create_no_share)) {
        nb = ((nb + 3) / 4) * 4;
        m  = ::operator new(nb + wls);
        sL = new (static_cast<unsigned char*>(m) + nb) WL(size, false, hasW);
    }
    else {
        static_assert(sizeof(RefCount) == sizeof(uint32_t), "Invalid size!");
        m       = ::operator new(nb);
        auto* t = static_cast<uint8_t*>(::operator new(wls + sizeof(uint32_t)));
        new (t) RefCount(1);
        sL = new (t + sizeof(uint32_t)) WL(size, true, hasW);
    }
    assert(m && (reinterpret_cast<uintptr_t>(m) & 7u) == 0);
    auto* ctx = not Potassco::test(flags, create_no_freeze) ? const_cast<SharedContext*>(s.sharedContext()) : nullptr;
    auto* c   = new (m) WeightConstraint(s, ctx, w, rep, sL, act);
    auto  ok  = c->integrateRoot(s);
    if (not ok && not Potassco::test(flags, create_conflicting)) {
        c->destroy(&s, true);
        return Result{nullptr, false};
    }
    if (not Potassco::test(flags, create_no_add)) {
        s.add(c);
    }
    return Result{c, ok};
}
WeightConstraint::WeightConstraint(Solver& s, SharedContext* ctx, Literal con, const WeightLitsRep& rep, WL* out,
                                   uint32_t act) {
    using Byte_t    = unsigned char;
    const bool hasW = rep.hasWeights();
    lits_           = out;
    active_         = act;
    ownsLit_        = not out->shareable();
    Literal* p      = lits_->lits;
    auto*    h      = new (reinterpret_cast<Byte_t*>(undo_)) Literal(con);
    bound_[ffb_btb] = (rep.reach - rep.bound) + 1; // ffb-btb
    bound_[ftb_bfb] = rep.bound;                   // ftb-bfb
    *p++            = ~con;                        // store constraint literal
    if (hasW) {
        *p++ = Literal::fromRep(1u); // and weight if necessary
    }
    if (ctx) {
        ctx->setFrozen(con.var(), true); // exempt from variable elimination
    }
    if (s.topValue(con.var()) != value_free) { // only one direction is relevant
        active_ = ffb_btb + s.isFalse(con);
    }
    watched_ = 3u - (active_ != both_active || ctx == nullptr);
    for (uint32_t j = 1; const auto& [lit, weight] : rep.literals()) {
        h    = new (h + 1) Literal(lit);
        *p++ = lit; // store constraint literal
        if (hasW) { // followed by weight if necessary
            *p++ = Literal::fromRep(static_cast<uint32_t>(weight));
        }
        addWatch(s, j, ftb_bfb); // watches  lits[idx]
        addWatch(s, j, ffb_btb); // watches ~lits[idx]
        if (ctx) {
            ctx->setFrozen(h->var(), true); // exempt from variable elimination
        }
        ++j;
    }
    // init heuristic
    h            -= rep.size;
    uint32_t off  = active_ != both_active;
    assert(static_cast<void*>(h) == static_cast<void*>(undo_));
    s.heuristic()->newConstraint(s, {h + off, rep.size + (1 - off)}, ConstraintType::static_);
    // init undo stack
    up_             = undoStart(); // undo stack is initially empty
    undo_[0].data   = 0;
    undo_[up_].data = 0;
    setBpIndex(1); // where to start back propagation
    if (s.topValue(con.var()) == value_free) {
        addWatch(s, 0, ftb_bfb); // watch con in both phases
        addWatch(s, 0, ffb_btb); // to allow for backpropagation
    }
    else {
        uint32_t d = active_; // propagate con
        WeightConstraint::propagate(s, ~lit(0, static_cast<ActiveConstraint>(active_)), d);
    }
}

WeightConstraint::WeightConstraint(Solver& s, const WeightConstraint& other) {
    using Byte_t = unsigned char;
    lits_        = other.lits_->clone();
    ownsLit_     = 0;
    auto* heu    = new (reinterpret_cast<Byte_t*>(undo_)) Literal(~lits_->lit(0));
    bound_[0]    = other.bound_[0];
    bound_[1]    = other.bound_[1];
    active_      = other.active_;
    watched_     = other.watched_;
    if (s.value(heu->var()) == value_free) {
        addWatch(s, 0, ftb_bfb); // watch con in both phases
        addWatch(s, 0, ffb_btb); // to allow for backpropagation
    }
    for (auto i : irange(1u, size())) {
        heu = new (heu + 1) Literal(lits_->lit(i));
        if (s.value(heu->var()) == value_free) {
            addWatch(s, i, ftb_bfb); // watches  lits[i]
            addWatch(s, i, ffb_btb); // watches ~lits[i]
        }
    }
    // Initialize heuristic with literals (no weights) in constraint.
    uint32_t off  = active_ != both_active;
    heu          -= (size() - 1);
    assert(static_cast<void*>(heu) == static_cast<void*>(undo_));
    s.heuristic()->newConstraint(s, {heu + off, size() - off}, ConstraintType::static_);
    // Init undo stack
    std::memcpy(undo_, other.undo_, sizeof(UndoInfo) * (size() + isWeight()));
    up_ = other.up_;
}

auto WeightConstraint::cloneAttach(Solver& other) -> Constraint* {
    void* m = ::operator new(sizeof(WeightConstraint) + (size() + isWeight()) * sizeof(UndoInfo));
    return new (m) WeightConstraint(other, *this);
}

bool WeightConstraint::integrateRoot(Solver& s) {
    POTASSCO_ASSERT(highestUndoLevel(s) == 0);
    if (not s.decisionLevel() || s.hasConflict()) {
        return not s.hasConflict();
    }
    // check if constraint has assigned literals
    uint32_t low = s.decisionLevel(), dl;
    uint32_t np  = 0;
    for (auto i : irange(size())) {
        if (auto v = lits_->var(i); s.value(v) != value_free && (dl = s.level(v)) != 0 && not s.seen(v)) {
            ++np;
            s.markSeen(v);
            low = std::min(low, dl);
        }
    }
    if (np) { // propagate assigned literals in assignment order
        LitVec todo;
        todo.reserve(np);
        const auto assigned = s.trailView(s.levelStart(low));
        for (auto idx = 0u, qStart = size32(assigned) - s.queueSize(); auto p : assigned) {
            if (s.seen(p)) {
                s.clearSeen(p.var());
                if (idx < qStart) {
                    todo.push_back(p);
                }
                if (--np == 0) {
                    break;
                }
            }
            ++idx;
        }
        POTASSCO_ASSERT(np == 0);
        for (auto p : todo) {
            POTASSCO_ASSERT(s.value(p.var()) != value_free);
            if (auto* data = s.getWatchData(p, this); data && not integrate(s, p, *data)) {
                break;
            }
        }
    }
    return not s.hasConflict();
}
void WeightConstraint::addWatch(Solver& s, uint32_t idx, ActiveConstraint c) {
    // Add watch only if c is relevant.
    if ((c ^ 1u) != active_) {
        // Use LSB to store the constraint that watches the literal.
        s.addWatch(~lit(idx, c), this, (idx << 1) + c);
    }
}

void WeightConstraint::destroy(Solver* s, bool detach) {
    if (s && detach) {
        for (auto i : irange(size())) {
            s->removeWatch(lits_->lit(i), this);
            s->removeWatch(~lits_->lit(i), this);
        }
        for (uint32_t last = 0, dl; (dl = highestUndoLevel(*s)) != 0; --up_) {
            if (dl != last) {
                s->removeUndoWatch(last = dl, this);
            }
        }
    }
    if (ownsLit_ == 0) {
        lits_->release();
    }
    void* mem = static_cast<Constraint*>(this);
    this->~WeightConstraint();
    ::operator delete(mem);
}

void WeightConstraint::setBpIndex(uint32_t n) {
    if (isWeight()) {
        undo_[0].data = (n << 1) + (undo_[0].data & 1);
    }
}

// Returns the numerical highest decision level watched by this constraint.
auto WeightConstraint::highestUndoLevel(const Solver& s) const -> uint32_t {
    return up_ != undoStart() ? s.level(lits_->var(undoTop().idx())) : 0;
}

// Updates the bound of sub-constraint c and adds the literal at index idx to the
// undo stack. If the current decision level is not watched, an undo watch is added
// so that the bound can be adjusted once the solver backtracks.
void WeightConstraint::updateConstraint(Solver& s, uint32_t level, uint32_t idx, ActiveConstraint c) {
    bound_[c] -= weight(idx);
    if (highestUndoLevel(s) != level) {
        s.addUndoWatch(level, this);
    }
    undo_[up_].data = (idx << 2) + (c << 1) + (undo_[up_].data & 1);
    ++up_;
    assert(not litSeen(idx));
    toggleLitSeen(idx);
}
template <bool Prop>
static constexpr auto force(Solver& s, Literal p, [[maybe_unused]] uint32_t lev, Constraint* c, uint32_t rd) {
    if constexpr (Prop) {
        POTASSCO_DEBUG_ASSERT(s.decisionLevel() == lev, "assignment not propagated");
        return s.force(p, c, rd);
    }
    else {
        return s.force(p, lev, c, rd);
    }
}
// Since clasp uses an eager assignment strategy where literals are assigned as soon
// as they are added to the propagation queue, we distinguish processed from unprocessed literals.
// Processed literals are those for which propagate was already called and the corresponding bound
// was updated; they are flagged in updateConstraint().
// Unprocessed literals are either free or were not yet propagated. During propagation,
// we treat all unprocessed literals as free. This way, conflicts are detected early.
// Consider: x :- 3 [a=3, b=2, c=1,d=1] and PropQ: b, ~Body, c.
// Initially b, ~Body, c are unprocessed and the bound is 3.
// Step 1: propagate(b)    : b is marked as processed and bound is reduced to 1.
//   Now, although we already know that the body is false, we do not backpropagate yet
//   because the body is unprocessed. Deferring backpropagation until the body is processed
//   makes reason computation easier.
// Step 2: propagate(~Body): ~body is marked as processed and bound is reduced to 0.
//   Since the body is now part of our reason set, we can start backpropagation.
//   First, we assign the unprocessed and free literal ~a. Literal ~b is skipped because
//   its complementary literal was already successfully processed. Finally, we force
//   the unprocessed but false literal ~c to true. This will generate a conflict and
//   propagation is stopped. Without the distinction between processed and unprocessed
//   lits, we would have to skip ~c. We would then have to manually trigger the conflict
//   {b, ~Body, c} in step 3, when propagate(c) sets the bound to -1.
template <bool Prop>
auto WeightConstraint::propagateImpl(Solver& s, Literal p, uint32_t data) -> PropResult {
    // determine the affected constraint and its body literal
    auto           c     = static_cast<ActiveConstraint>(data & 1);
    const uint32_t idx   = data >> 1;
    const Literal  body  = lit(0, c);
    const uint32_t level = s.level(p.var());
    if ((c ^ 1u) == active_ || (s.isTrue(body) && (Prop || s.level(body.var()) <= level))) {
        // the other constraint is active or this constraint is already satisfied;
        // nothing to do
        return PropResult(true, true);
    }
    if (idx == 0 && level <= s.rootLevel() && watched_ == both_active) {
        watched_ = c;
        for (auto i : irange(1u, size())) { s.removeWatch(lit(i, c), this); }
    }
    // the constraint is not yet satisfied; update it and
    // check if we can now propagate any literals.
    updateConstraint(s, level, idx, c);
    if (bound_[c] <= 0 || (isWeight() && litSeen(0))) {
        uint32_t reasonData = not isWeight() ? UINT32_MAX : up_;
        if (not litSeen(0)) {
            // forward propagate constraint to true
            active_ = c;
            return PropResult(force<Prop>(s, body, level, this, reasonData), true);
        }
        // backward propagate false constraint
        uint32_t n = getBpIndex();
        for (const uint32_t end = size(); n != end && (bound_[c] - weight(n)) < 0; ++n) {
            if (not litSeen(n)) {
                active_   = c;
                Literal x = lit(n, c);
                if (not force<Prop>(s, x, level, this, reasonData)) {
                    return PropResult(false, true);
                }
            }
        }
        assert(n == 1 || n == size() || isWeight());
        setBpIndex(n);
    }
    return PropResult(true, true);
}
auto WeightConstraint::propagate(Solver& s, Literal p, uint32_t& d) -> PropResult {
    return propagateImpl<true>(s, p, d);
}
bool WeightConstraint::integrate(Solver& s, Literal p, uint32_t d) {
    auto dl = s.decisionLevel();
    return propagateImpl<false>(s, p, d).ok && dl == s.decisionLevel();
}
// Builds the reason for p from the undo stack of this constraint.
// The reason will only contain literals processed by the
// active sub-constraint.
void WeightConstraint::reason(Solver& s, Literal p, LitVec& r) {
    assert(active_ != both_active);
    uint32_t stop = not isWeight() ? up_ : s.reasonData(p);
    assert(stop <= up_);
    for (auto i : irange(undoStart(), stop)) {
        UndoInfo u = undo_[i];
        // Consider only lits that are relevant to the active constraint
        if (u.constraint() == static_cast<ActiveConstraint>(active_)) {
            Literal x = lit(u.idx(), u.constraint());
            r.push_back(~x);
        }
    }
}

bool WeightConstraint::minimize(Solver& s, Literal p, CCMinRecursive* rec) {
    assert(active_ != both_active);
    uint32_t stop = not isWeight() ? up_ : s.reasonData(p);
    assert(stop <= up_);
    for (auto i = undoStart(); i != stop; ++i) {
        // Consider only lits that are relevant to the active constraint
        if (UndoInfo u = undo_[i]; u.constraint() == static_cast<ActiveConstraint>(active_)) {
            if (Literal x = lit(u.idx(), u.constraint()); not s.ccMinimize(~x, rec)) {
                return false;
            }
        }
    }
    return true;
}

// undoes processed assignments
void WeightConstraint::undoLevel(Solver& s) {
    setBpIndex(1);
    for (UndoInfo u; up_ != undoStart() && s.value(lits_->var((u = undoTop()).idx())) == value_free;) {
        assert(litSeen(u.idx()));
        toggleLitSeen(u.idx());
        bound_[u.constraint()] += weight(u.idx());
        --up_;
    }
    if (not litSeen(0)) {
        active_ = both_active;
        if (watched_ < 2u) {
            auto other = static_cast<ActiveConstraint>(watched_ ^ 1);
            for (auto i : irange(1u, size())) { addWatch(s, i, other); }
            watched_ = both_active;
        }
    }
}

bool WeightConstraint::simplify(Solver& s, bool) {
    if (bound_[0] <= 0 || bound_[1] <= 0) {
        for (auto i : irange(size())) {
            s.removeWatch(lits_->lit(i), this);
            s.removeWatch(~lits_->lit(i), this);
        }
        return true;
    }
    if (s.value(lits_->var(0)) != value_free && (active_ == both_active || isWeight())) {
        if (active_ == both_active) {
            Literal con = ~lits_->lit(0);
            active_     = ffb_btb + s.isFalse(con);
        }
        for (auto i : irange(size())) { s.removeWatch(lit(i, static_cast<ActiveConstraint>(active_)), this); }
    }
    if (lits_->unique() && size() > 4 && (up_ - undoStart()) > size() / 2) {
        Literal*       lits = lits_->lits;
        const uint32_t inc  = 1 + lits_->weights();
        uint32_t       end  = lits_->size() * inc;
        uint32_t       i, j, idx = 1;
        // find the first assigned literal - must be there otherwise undo stack would be empty
        for (i = inc; s.value(lits[i].var()) == value_free; i += inc) {
            assert(not litSeen(idx));
            ++idx;
        }
        // move unassigned literals down
        // update watches because indices have changed
        for (j = i, i += inc; i != end; i += inc) {
            if (s.value(lits[i].var()) == value_free) {
                lits[j] = lits[i];
                if (lits_->weights()) {
                    lits[j + 1] = lits[i + 1];
                }
                undo_[idx].data = 0;
                assert(not litSeen(idx));
                s.updateWatchData(lits[i], this, (idx << 1) + 1);
                s.updateWatchData(~lits[i], this, (idx << 1) + 0);
                j += inc;
                ++idx;
            }
            else {
                s.removeWatch(lits[i], this);
                s.removeWatch(~lits[i], this);
            }
        }
        // clear undo stack & update to new size
        up_ = undoStart();
        setBpIndex(1);
        lits_->sz = idx;
    }
    return false;
}

auto WeightConstraint::estimateComplexity(const Solver& s) const -> uint32_t {
    auto     bnd = std::min(bound_[0], bound_[1]);
    uint32_t r   = 2;
    for (uint32_t i = 1; i != size() && bnd > 0; ++i) {
        if (s.value(lits_->var(i)) == value_free) {
            ++r;
            bnd -= weight(i);
        }
    }
    return r;
}
auto WeightConstraint::implicationLevel(const Solver& s, Literal con, WeightLitsRep rep, CreateFlag flags) -> uint32_t {
    auto rightImp = Potassco::test(flags, create_only_btb);
    auto leftImp  = Potassco::test(flags, create_only_bfb);
    auto propLev  = 0u;
    if (rightImp && leftImp) {
        rightImp = leftImp = false;
    }
    if (rep.open()) {
        WeightLitVec assigned;
        auto         conLit = WeightLiteral{con, weight_max};
        auto         full   = not leftImp && not rightImp;
        for (const auto& [lit, weight] : rep.literals()) {
            if (s.value(lit.var()) != value_free && (full || s.isTrue(lit) != rightImp)) {
                assigned.push_back({lit, weight});
            }
        }
        std::span<WeightLiteral> assignedView;
        if (not assigned.empty()) {
            if (s.value(con.var()) != value_free) {
                assigned.push_back(conLit);
            }
            std::ranges::sort(assigned, [&](const WeightLiteral& lhs, const WeightLiteral& rhs) {
                auto l1 = s.level(lhs.lit.var());
                auto l2 = s.level(rhs.lit.var());
                return l1 != l2 ? l1 < l2 : lhs.weight > rhs.weight;
            });
            assignedView = assigned;
        }
        else if (s.value(con.var()) != value_free) {
            assignedView = Potassco::toSpan(conLit);
        }
        auto bpIdx  = 0u;
        auto actLev = 0u;
        auto active = both_active;
        for (auto [lit, weight] : assignedView) {
            if (active == both_active && lit == con) {
                if ((s.isTrue(con) && leftImp) || (s.isFalse(con) && rightImp)) {
                    return UINT32_MAX; // constraint is SAT
                }
                active = s.isTrue(con) ? ffb_btb : ftb_bfb;
                actLev = s.level(con.var());
            }
            else {
                rep.reach -= weight;
                if (s.isTrue(lit)) {
                    rep.bound -= weight;
                }
            }
            if (not rep.open()) {
                propLev = s.level(lit.var());
                break;
            }
            if (active != both_active && bpIdx < rep.size) {
                for (auto bpTrue = active == ffb_btb; bpIdx < rep.size; ++bpIdx) {
                    auto bpLit = rep.lits[bpIdx].lit;
                    auto bpLev = s.value(bpLit.var()) == value_free ? UINT32_MAX : s.level(bpLit.var());
                    if (bpLev > actLev || (bpLev < actLev && s.isTrue(bpLit) != bpTrue)) {
                        auto bnd = bpTrue ? (rep.reach - rep.bound) + 1 : rep.bound;
                        if (rep.lits[bpIdx].weight >= bnd) {
                            return s.level(lit.var());
                        }
                        break;
                    }
                }
            }
        }
    }
    if (rep.sat()) {
        return rightImp || (s.isTrue(con) && s.level(con.var()) <= propLev) ? UINT32_MAX : propLev;
    }
    if (rep.unsat()) {
        return leftImp || (s.isTrue(~con) && s.level(con.var()) <= propLev) ? UINT32_MAX : propLev;
    }
    return UINT32_MAX;
}

uint32_t WeightConstraint::implicationLevel(Solver& s, Literal con, WeightLitVec& lists, Weight_t bound,
                                            CreateFlag flags) {
    return implicationLevel(s, con, WeightLitsRep::create(s, lists, bound), flags);
}

} // namespace Clasp
