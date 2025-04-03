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
#include <clasp/minimize_constraint.h>

#include <clasp/clause.h>
#include <clasp/solver.h>
#include <clasp/weight_constraint.h>

#include <potassco/error.h>

#include <cmath>

namespace Clasp {
/////////////////////////////////////////////////////////////////////////////////////////
// SharedMinimizeData
/////////////////////////////////////////////////////////////////////////////////////////
SharedMinimizeData::SharedMinimizeData(SumView lhsAdjust, MinimizeMode m)
    : adjust_(lhsAdjust.data(), lhsAdjust.data() + lhsAdjust.size())
    , lower_(std::make_unique<LowerType[]>(lhsAdjust.size()))
    , mode_(m)
    , count_(1)
    , optGen_(0) {
    resetBounds();
    setMode(MinimizeMode::optimize);
}
SharedMinimizeData::~SharedMinimizeData() = default;

void SharedMinimizeData::destroy() const {
    this->~SharedMinimizeData();
    ::operator delete(const_cast<SharedMinimizeData*>(this));
}

void SharedMinimizeData::resetBounds() {
    gCount_.store(0);
    optGen_ = 0;
    for (auto& low : std::span{lower_.get(), numRules()}) { low.store(0); }
    lowPos_.store(numRules());
    up_[0].assign(numRules(), maxBound());
    up_[1].assign(numRules(), maxBound());
    const WeightLiteral* lit = lits;
    for (auto wIt = weights.begin(), end = weights.end(); wIt != end; ++wIt) {
        assert(wIt->weight >= 0);
        auto wPos = wIt - weights.begin();
        for (auto nLits = 0; wIt->next;) { // Any weight < 0? If so, reduce lower bound accordingly.
            if (++wIt; wIt->weight < 0) {
                if (nLits == 0) { // Get number of literals having this weight (i.e. all with same weight position).
                    for (; lit->weight <= wPos; ++lit) { nLits += (lit->weight == wPos); }
                }
                assert(nLits > 0 && lit->weight > wPos);
                lower_[wIt->level].add(static_cast<Wsum_t>(wIt->weight) * nLits);
            }
        }
    }
}

bool SharedMinimizeData::setMode(MinimizeMode m, SumView bound) {
    mode_ = m;
    if (not bound.empty()) {
        SumVec& opt = up_[0];
        bool    ok  = false;
        gCount_.store(0);
        optGen_        = 0;
        auto boundSize = std::min(size32(bound), numRules());
        for (uint32_t i : irange(boundSize)) {
            auto b = bound[i], a = adjust(i);
            b      = a >= 0 || (maxBound() + a) >= b ? b - a : maxBound();
            auto d = b - lower_[i].load();
            if (d < 0 && not ok) {
                return false;
            }
            opt[i] = b;
            ok     = ok || d > 0;
        }
        for (auto& b : drop(opt, boundSize)) { b = maxBound(); }
    }
    return true;
}

MinimizeConstraint* SharedMinimizeData::attach(Solver& s, const OptParams& params, bool addRef) {
    if (addRef) {
        this->share();
    }
    MinimizeConstraint* ret;
    if (params.type == OptParams::type_bb || mode() == MinimizeMode::enumerate) {
        ret = new DefaultMinimize(this, params);
    }
    else {
        ret = new UncoreMinimize(this, params);
    }
    ret->attach(s);
    return ret;
}

SumView SharedMinimizeData::setOptimum(const Wsum_t* newOpt) {
    if (optGen_) {
        return up_[(optGen_ & 1u)];
    }
    uint32_t g = gCount_.load();
    uint32_t n = 1u - (g & 1u);
    SumVec&  u = up_[n];
    u.assign(newOpt, newOpt + numRules());
    assert(mode() != MinimizeMode::enumerate || n == 1);
    if (mode() != MinimizeMode::enumerate) {
        if (++g == 0) {
            g = 2;
        }
        gCount_.store(g);
    }
    return u;
}
void   SharedMinimizeData::setLower(uint32_t lev, Wsum_t low) { lower_[lev].store(low); }
Wsum_t SharedMinimizeData::incLower(uint32_t lev, Wsum_t low) {
    for (auto stored = lower(lev);;) {
        if (stored >= low) {
            return stored;
        }
        if (lower_[lev].compare_exchange_weak(stored, low)) {
            auto storedLev = lowPos_.load();
            while (storedLev == numRules() || lev > storedLev) { lowPos_.compare_exchange_weak(storedLev, lev); }
            return low;
        }
    }
}
Wsum_t SharedMinimizeData::lower(uint32_t lev) const { return lower_[lev].load(); }
Wsum_t SharedMinimizeData::optimum(uint32_t lev) const {
    Wsum_t o = sum(lev);
    return o + (o != maxBound() ? adjust(lev) : 0);
}
void SharedMinimizeData::markOptimal() { optGen_ = generation(); }
void SharedMinimizeData::sub(Wsum_t* lhs, const LevelWeight* w, uint32_t& aLev) {
    if (w->level < aLev) {
        aLev = w->level;
    }
    do { lhs[w->level] -= w->weight; } while (w++->next);
}
bool SharedMinimizeData::imp(Wsum_t* lhs, const LevelWeight* w, const Wsum_t* rhs, uint32_t& lev) const {
    assert(lev <= w->level && std::equal(lhs, lhs + lev, rhs));
    while (lev != w->level && lhs[lev] == rhs[lev]) { ++lev; }
    for (uint32_t i = lev, end = numRules(); i != end; ++i) {
        Wsum_t temp = lhs[i];
        if (i == w->level) {
            temp += w->weight;
            if (w->next) {
                ++w;
            }
        }
        if (temp != rhs[i]) {
            return temp > rhs[i];
        }
    }
    return false;
}
LowerBound SharedMinimizeData::lowerBound() const {
    if (auto lev = lowPos_.load(); lev < numRules()) {
        return {.level = lev, .bound = lower(lev) + adjust(lev)};
    }
    return {};
}
/////////////////////////////////////////////////////////////////////////////////////////
// MinimizeConstraint
/////////////////////////////////////////////////////////////////////////////////////////
MinimizeConstraint::MinimizeConstraint(SharedData* d) : shared_(d) {}

MinimizeConstraint::~MinimizeConstraint() { assert(shared_ == nullptr && "MinimizeConstraint not destroyed!"); }
bool MinimizeConstraint::prepare(Solver& s, bool useTag) {
    POTASSCO_CHECK_PRE(not s.isFalse(tag_), "Tag literal must not be false!");
    if (useTag && tag_ == lit_true) {
        tag_ = posLit(s.pushTagVar(false));
    }
    if (s.isTrue(tag_) || s.hasConflict()) {
        return not s.hasConflict();
    }
    return useTag ? s.pushRoot(tag_) : s.force(tag_, nullptr);
}
void MinimizeConstraint::destroy(Solver* s, bool d) {
    shared_->release();
    shared_ = nullptr;
    Constraint::destroy(s, d);
}
/////////////////////////////////////////////////////////////////////////////////////////
// DefaultMinimize
/////////////////////////////////////////////////////////////////////////////////////////
struct DefaultMinimize::UndoInfo {
    uint32_t idx     : 30 {0}; // index of literal on stack
    uint32_t newDL   : 1 {0};  // first literal of new DL?
    uint32_t idxSeen : 1 {0};  // literal with idx already propagated?
};
DefaultMinimize::DefaultMinimize(SharedData* d, const OptParams& params)
    : MinimizeConstraint(d)
    , bounds_(nullptr)
    , pos_(d->lits)
    , undo_(nullptr)
    , undoTop_(0)
    , posTop_(0)
    , size_(d->numRules())
    , actLev_(0) {
    step_.type = params.algo;
    if (step_.type == OptParams::bb_hier && d->numRules() == 1) {
        step_.type = 0;
    }
}

DefaultMinimize::~DefaultMinimize() = default;

void DefaultMinimize::destroy(Solver* s, bool detach) {
    if (s && detach) {
        for (const auto& [lit, _] : *shared_) { s->removeWatch(lit, this); }
        for (uint32_t dl = 0; (dl = lastUndoLevel(*s)) != 0;) {
            s->removeUndoWatch(dl, this);
            DefaultMinimize::undoLevel(*s);
        }
    }
    MinimizeConstraint::destroy(s, detach);
}

bool DefaultMinimize::attach(Solver& s) {
    assert(s.decisionLevel() == 0 && not bounds_);
    uint32_t numL = 0;
    VarVec   up;
    for (const auto& [lit, _] : *shared_) {
        if (s.value(lit.var()) == value_free) {
            s.addWatch(lit, this, numL);
        }
        else if (s.isTrue(lit)) {
            up.push_back(numL);
        }
        ++numL;
    }
    bounds_ = std::make_unique<Wsum_t[]>(numRules() *
                                         (3 + static_cast<uint32_t>(step_.type != 0))); // upper, sum, temp, lower
    std::fill(this->opt(), this->sum(), SharedData::maxBound());
    std::fill(this->sum(), this->end(), static_cast<Wsum_t>(0));
    stepInit(0);
    // [0,numL+1)      : undo stack
    // [numL+1, numL*2): pos  stack
    undo_    = std::make_unique<UndoInfo[]>((numL * 2) + 1);
    undoTop_ = 0;
    posTop_  = numL + 1;
    actLev_  = 0;
    for (auto x : up) { DefaultMinimize::propagate(s, shared_->lits[x].lit, x); }
    return true;
}

// Returns the numerical highest decision level watched by this constraint.
uint32_t DefaultMinimize::lastUndoLevel(const Solver& s) const {
    return undoTop_ != 0 ? s.level(shared_->lits[undo_[undoTop_ - 1].idx].lit.var()) : 0;
}
bool DefaultMinimize::litSeen(uint32_t i) const { return undo_[i].idxSeen != 0; }

// Pushes the literal at index idx onto the undo stack
// and marks it as seen; if literal is first in current level
// adds a new undo watch.
void DefaultMinimize::pushUndo(Solver& s, uint32_t idx) {
    assert(idx >= static_cast<uint32_t>(pos_ - shared_->lits));
    undo_[undoTop_].idx   = idx;
    undo_[undoTop_].newDL = 0;
    if (lastUndoLevel(s) != s.decisionLevel()) {
        // remember current "look at" position and start
        // a new decision level on the undo stack
        undo_[posTop_++].idx = static_cast<uint32_t>(pos_ - shared_->lits);
        s.addUndoWatch(s.decisionLevel(), this);
        undo_[undoTop_].newDL = 1;
    }
    undo_[idx].idxSeen = 1;
    ++undoTop_;
}
auto DefaultMinimize::viewUndo(const Solver& s, Literal p) const -> SpanView<UndoInfo> {
    uint32_t stop = s.reasonData(p);
    assert(stop <= undoTop_);
    return std::span(undo_.get(), stop);
}
/////////////////////////////////////////////////////////////////////////////////////////
// MinimizeConstraint - arithmetic strategy implementation
//
// For now we use a simple "switch-on-type" approach.
// In the future, if new strategies emerge, we may want to use a strategy hierarchy.
/////////////////////////////////////////////////////////////////////////////////////////
#define STRATEGY(x) shared_->x
// set *lhs = *rhs, where lhs != rhs
void DefaultMinimize::assign(Wsum_t* lhs, const Wsum_t* rhs) const { std::memcpy(lhs, rhs, size_ * sizeof(Wsum_t)); }
// returns lhs > rhs
bool DefaultMinimize::greater(Wsum_t* lhs, Wsum_t* rhs, uint32_t len, uint32_t& aLev) {
    while (*lhs == *rhs && --len) {
        ++lhs, ++rhs;
        ++aLev;
    }
    return *lhs > *rhs;
}
/////////////////////////////////////////////////////////////////////////////////////////
Constraint::PropResult DefaultMinimize::propagate(Solver& s, Literal, uint32_t& data) {
    pushUndo(s, data);
    STRATEGY(add(sum(), shared_->lits[data]));
    return PropResult(propagateImpl(s, propagate_new_sum), true);
}

// Computes the set of literals implying p and returns
// the highest decision level of that set.
// PRE: p is implied on highest undo level
uint32_t DefaultMinimize::computeImplicationSet(const Solver& s, const WeightLiteral& p, uint32_t& undoPos) {
    Wsum_t * temp = this->temp(), *opt = this->opt();
    uint32_t up = undoTop_, lev = actLev_;
    uint32_t minLevel = std::max(s.level(tag_.var()), s.level(s.sharedContext()->stepLiteral().var()));
    // start from current sum
    assign(temp, sum());
    // start with full set
    for (UndoInfo u; up != 0; --up) {
        u = undo_[up - 1];
        // subtract last element from set
        STRATEGY(sub(temp, shared_->lits[u.idx], lev));
        if (not STRATEGY(imp(temp, p, opt, lev))) {
            // p is no longer implied after we removed last literal,
            // hence [0, up) implies p @ level of last literal
            undoPos = up;
            return std::max(s.level(shared_->lits[u.idx].lit.var()), minLevel);
        }
    }
    undoPos = 0;
    return minLevel;
}

bool DefaultMinimize::propagateImpl(Solver& s, PropMode m) {
    Iter     it  = pos_;
    auto     idx = static_cast<uint32_t>(it - shared_->lits);
    uint32_t dl  = s.decisionLevel();
    // current implication level or "unknown" if
    // we propagate a new optimum
    uint32_t impLevel = dl + (m == propagate_new_opt);
    Weight_t lastW    = -1;
    uint32_t undoPos  = undoTop_;
    bool     ok       = true;
    actLev_           = std::min(actLev_, shared_->level(idx));
    for (Wsum_t *sum = this->sum(), *opt = this->opt(); ok && not isSentinel(it->lit); ++it, ++idx) {
        // skip propagated/false literals
        if (litSeen(idx) || (m == propagate_new_sum && s.isFalse(it->lit))) {
            continue;
        }
        if (lastW != it->weight) {
            // check if the current weight is implied
            if (not STRATEGY(imp(sum, *it, opt, actLev_))) {
                // all good - current optimum is safe
                pos_ = it;
                return true;
            }
            // compute implication set and level of current weight
            if (m == propagate_new_opt) {
                impLevel = computeImplicationSet(s, *it, undoPos);
            }
            lastW = it->weight;
        }
        assert(active());
        // force implied literals
        if (not s.isFalse(it->lit) || (impLevel < dl && s.level(it->lit.var()) > impLevel)) {
            if (impLevel != dl) {
                dl = s.undoUntil(impLevel, Solver::undo_pop_bt_level);
            }
            ok = s.force(~it->lit, impLevel, this, undoPos);
        }
    }
    return ok;
}

// pops free literals from the undo stack and decreases current sum
void DefaultMinimize::undoLevel(Solver&) {
    assert(undoTop_ != 0 && posTop_ > undoTop_);
    uint32_t up  = undoTop_;
    uint32_t idx = undo_[--posTop_].idx;
    for (Wsum_t* sum = this->sum();;) {
        UndoInfo& u          = undo_[--up];
        undo_[u.idx].idxSeen = 0;
        STRATEGY(sub(sum, shared_->lits[u.idx], actLev_));
        if (u.newDL) {
            break;
        }
    }
    undoTop_ = up;
    if (Iter temp = shared_->lits + idx; temp < pos_) {
        pos_    = temp;
        actLev_ = std::min(actLev_, shared_->level(idx));
    }
}

// computes the reason for p -
// all literals that were propagated before p
void DefaultMinimize::reason(Solver& s, Literal p, LitVec& lits) {
    assert(s.isTrue(tag_));
    Literal x = s.sharedContext()->stepLiteral();
    if (not isSentinel(x) && s.isTrue(x)) {
        lits.push_back(x);
    }
    if (s.level(tag_.var())) {
        lits.push_back(tag_);
    }
    for (const auto& u : viewUndo(s, p)) {
        x = shared_->lits[u.idx].lit;
        lits.push_back(x);
    }
}

bool DefaultMinimize::minimize(Solver& s, Literal p, CCMinRecursive* rec) {
    assert(s.isTrue(tag_));
    Literal x = s.sharedContext()->stepLiteral();
    if (not s.ccMinimize(x, rec) || not s.ccMinimize(tag_, rec)) {
        return false;
    }
    for (const auto& u : viewUndo(s, p)) {
        x = shared_->lits[u.idx].lit;
        if (not s.ccMinimize(x, rec)) {
            return false;
        }
    }
    return true;
}
/////////////////////////////////////////////////////////////////////////////////////////
// DefaultMinimize - bound management
/////////////////////////////////////////////////////////////////////////////////////////
// Stores the current sum as the shared optimum.
void DefaultMinimize::commitUpperBound(const Solver&) {
    shared_->setOptimum(sum());
    if (step_.type == OptParams::bb_inc) {
        step_.size *= 2;
    }
}
bool DefaultMinimize::commitLowerBound(Solver&, bool upShared) {
    bool act  = active() && shared_->checkNext();
    bool more = step_.lev < size_ && (step_.size > 1 || step_.lev != size_ - 1);
    if (act && step_.type && step_.lev < size_) {
        uint32_t x = step_.lev;
        Wsum_t   l = opt()[x] + 1;
        if (upShared) {
            if (Wsum_t sv = shared_->incLower(x, l); sv != l) {
                l = sv;
            }
        }
        stepLow() = l;
        if (step_.type == OptParams::bb_inc) {
            step_.size = 1;
        }
    }
    return more;
}
bool DefaultMinimize::handleUnsat(Solver& s, bool up, LitVec& out) {
    bool     more = shared_->optimize() && commitLowerBound(s, up);
    uint32_t dl   = s.isTrue(tag_) ? s.level(tag_.var()) : 0;
    relaxBound(false);
    if (more && dl && dl <= s.rootLevel()) {
        s.popRootLevel(s.rootLevel() - dl, &out); // pop and remember new path
        return s.popRootLevel(1);                 // pop tag - disable constraint
    }
    return false;
}

// Disables the minimize constraint by clearing its upper bound.
bool DefaultMinimize::relaxBound(bool full) {
    if (active()) {
        std::fill_n(opt(), size_, SharedData::maxBound());
    }
    pos_    = shared_->lits;
    actLev_ = 0;
    if (full || not shared_->optimize()) {
        stepInit(0);
    }
    return true;
}

void DefaultMinimize::stepInit(uint32_t n) {
    step_.size = static_cast<uint32_t>(step_.type != OptParams::bb_dec);
    if (step_.type) {
        step_.lev = n;
        if (n != size_) {
            stepLow() = 0 - SharedMinimizeData::maxBound();
        }
    }
    else {
        step_.lev = shared_->maxLevel();
    }
}

// Integrates new (tentative) bounds from the ones stored in the shared data object.
bool DefaultMinimize::integrateBound(Solver& s) {
    bool useTag = shared_->optimize() && (step_.type != 0 || shared_->mode() == MinimizeMode::enum_opt);
    if (not prepare(s, useTag)) {
        return false;
    }
    if (useTag && s.level(tag_.var()) == 0) {
        step_.type = 0;
        stepInit(0);
    }
    if ((active() && not shared_->checkNext())) {
        return not s.hasConflict();
    }

    WeightLiteral min{lit_true, static_cast<Weight_t>(shared_->weights.empty() ? 0u : size32(shared_->weights) - 1u)};
    while (not s.hasConflict() && updateBounds(shared_->checkNext())) {
        uint32_t x  = 0;
        uint32_t dl = s.decisionLevel() + 1;
        if (not STRATEGY(imp(sum(), min, opt(), actLev_)) || (dl = computeImplicationSet(s, min, x)) > s.rootLevel()) {
            for (--dl; not s.hasConflict() || s.resolveConflict();) {
                if (s.undoUntil(dl, Solver::undo_pop_bt_level) > dl) {
                    s.backtrack();
                }
                else if (propagateImpl(s, propagate_new_opt)) {
                    return true;
                }
            }
        }
        if (not shared_->checkNext()) {
            break;
        }
        if (not step_.type) {
            ++step_.lev;
        }
        else {
            stepLow() = ++opt()[step_.lev];
        }
    }
    relaxBound(false);
    if (not s.hasConflict()) {
        s.undoUntil(0);
        s.setStopConflict();
    }
    return false;
}

// Loads bounds from the shared data object and (optionally) applies
// the current step to get the next tentative bound to check.
bool DefaultMinimize::updateBounds(bool applyStep) {
    for (;;) {
        const uint32_t seq    = shared_->generation();
        const Wsum_t*  upper  = shared_->upper();
        Wsum_t*        myLow  = step_.type ? end() : nullptr;
        Wsum_t*        bound  = opt();
        uint32_t       appLev = applyStep ? step_.lev : size_;
        for (uint32_t i : irange(size_)) {
            Wsum_t u = upper[i], b = bound[i];
            if (i != appLev) {
                Wsum_t l = shared_->lower(i);
                if (myLow) {
                    if (i > step_.lev || l > myLow[i]) {
                        myLow[i] = l;
                    }
                    else {
                        l = myLow[i];
                    }
                }
                if (i > appLev) {
                    bound[i] = SharedData::maxBound();
                }
                else if (u >= l) {
                    bound[i] = u;
                }
                else {
                    stepInit(size_);
                    return false;
                }
                continue;
            }
            if (step_.type) {
                Wsum_t l = (stepLow() = std::max(myLow[i], shared_->lower(i)));
                if (u < l) { // path exhausted?
                    stepInit(size_);
                    return false;
                }
                if (b < l) { // tentative bound too strong?
                    return false;
                }
                if (b < u) { // existing step?
                    assert(std::count(bound + i + 1, bound + size_, SharedData::maxBound()) ==
                           static_cast<int>(size_ - (i + 1)));
                    return true;
                }
                if (u == l) { // done with current level?
                    bound[i] = u;
                    stepInit(++appLev);
                    continue;
                }
                assert(u > l && b > l);
                Wsum_t diff = u - l;
                auto   half = static_cast<uint32_t>((diff >> 1) | (diff & 1));
                if (step_.type == OptParams::bb_inc) {
                    step_.size = std::min(step_.size, half);
                }
                else if (step_.type == OptParams::bb_dec) {
                    if (not step_.size) {
                        step_.size = static_cast<uint32_t>(diff);
                    }
                    else {
                        step_.size = half;
                    }
                }
            }
            assert(step_.size != 0);
            bound[i] = u - step_.size;
            actLev_  = 0;
            pos_     = shared_->lits;
        }
        if (seq == shared_->generation()) {
            break;
        }
    }
    return step_.lev != size_ || not applyStep;
}
#undef STRATEGY
/////////////////////////////////////////////////////////////////////////////////////////
// MinimizeBuilder
/////////////////////////////////////////////////////////////////////////////////////////
static inline auto lw(const SharedMinimizeData::WeightVec& weights, Weight_t pos) {
    assert(pos >= 0 && static_cast<uint32_t>(pos) < weights.size());
    return &weights[static_cast<uint32_t>(pos)];
}
static inline auto lw(const SharedMinimizeData::WeightVec& weights, const WeightLiteral& wl) {
    return lw(weights, wl.weight);
}
MinimizeBuilder::MinimizeBuilder() = default;
void             MinimizeBuilder::clear() { discardVec(lits_); }
bool             MinimizeBuilder::empty() const { return lits_.empty(); }
MinimizeBuilder& MinimizeBuilder::add(Weight_t prio, WeightLitView lits) {
    for (const auto& lit : lits) { add(prio, lit); }
    return *this;
}
MinimizeBuilder& MinimizeBuilder::add(Weight_t prio, WeightLiteral lit) {
    lits_.push_back(MLit(lit, prio));
    return *this;
}
MinimizeBuilder& MinimizeBuilder::add(Weight_t prio, Weight_t w) {
    lits_.push_back(MLit(WeightLiteral{lit_true, w}, prio));
    return *this;
}
MinimizeBuilder& MinimizeBuilder::add(const SharedData& con) {
    if (con.numRules() == 1) {
        const Weight_t p = not con.prios.empty() ? con.prios[0] : 0;
        for (const auto& wl : con) { add(p, wl); }
    }
    else {
        for (const auto& wl : con) {
            const auto* w = lw(con.weights, wl);
            do {
                add(w->level < con.prios.size() ? con.prios[w->level] : -static_cast<Weight_t>(w->level),
                    WeightLiteral{wl.lit, w->weight});
            } while (w++->next);
        }
    }
    for (uint32_t i : irange(con.numRules())) {
        if (Wsum_t w = con.adjust(i)) {
            const Weight_t p = i < con.prios.size() ? con.prios[i] : -static_cast<Weight_t>(i);
            while (w < weight_min) {
                add(p, weight_min);
                w -= weight_min;
            }
            while (w > weight_max) {
                add(p, weight_max);
                w -= weight_max;
            }
            add(p, static_cast<Weight_t>(w));
        }
    }
    return *this;
}

// Replaces integer priorities with increasing levels and merges duplicate/complementary literals.
void MinimizeBuilder::prepareLevels(const Solver& s, SumVec& adjust, WeightVec& prios) {
    // group first by decreasing priorities and then by variables, i.e. compare (prio, var, weight)
    std::ranges::stable_sort(lits_, [](const MLit& lhs, const MLit& rhs) {
        if (lhs.prio != rhs.prio) {
            return lhs.prio > rhs.prio;
        }
        if (lhs.lit.var() != rhs.lit.var()) {
            return lhs.lit < rhs.lit;
        }
        return lhs.weight > rhs.weight;
    });
    prios.clear();
    adjust.clear();
    // assign levels and simplify lits
    auto j = lits_.begin();
    for (LitVec::const_iterator it = lits_.begin(), end = lits_.end(); it != end;) {
        const Weight_t p = it->prio;
        Wsum_t         r = 0;
        for (LitVec::const_iterator k; it != end && it->prio == p; it = k) {
            Literal x(it->lit); // make literal unique wrt this level
            Wsum_t  w = it->weight;
            for (k = it + 1; k != end && k->lit.var() == x.var() && k->prio == p; ++k) {
                if (k->lit == x) {
                    w += k->weight;
                }
                else {
                    w -= k->weight;
                    r += k->weight;
                }
            }
            if (w < 0) {
                r += w;
                x  = ~x;
                w  = -w;
            }
            if (w && s.value(x.var()) == value_free) {
                POTASSCO_CHECK(static_cast<Weight_t>(w) == w, EOVERFLOW, "MinimizeBuilder: weight too large");
                *j++ = MLit(WeightLiteral{x, static_cast<Weight_t>(w)}, static_cast<Weight_t>(prios.size()));
            }
            else if (s.isTrue(x)) {
                r += w;
            }
        }
        prios.push_back(p);
        adjust.push_back(r);
    }
    lits_.erase(j, lits_.end());
}

void MinimizeBuilder::mergeLevels(SumVec& adjust, SharedData::WeightVec& weights) {
    // group first by variables and then by increasing levels, i.e. compare (var, level, weight)
    std::ranges::stable_sort(lits_, [](const MLit& lhs, const MLit& rhs) {
        if (lhs.lit.var() != rhs.lit.var()) {
            return lhs.lit < rhs.lit;
        }
        if (lhs.prio != rhs.prio) {
            return lhs.prio < rhs.prio;
        }
        return lhs.weight > rhs.weight;
    });
    LitVec::iterator j = lits_.begin();
    weights.clear();
    weights.reserve(lits_.size());
    for (LitVec::const_iterator it = lits_.begin(), end = lits_.end(), k; it != end; it = k) {
        // handle first occurrence of var
        assert(it->weight > 0 && "most important occurrence of lit must have positive weight");
        assert(it->prio >= 0 && "levels not prepared!");
        auto wpos = static_cast<Weight_t>(weights.size());
        weights.push_back(SharedData::LevelWeight(static_cast<uint32_t>(it->prio), it->weight));
        // handle remaining occurrences with lower prios
        for (k = it + 1; k != end && k->lit.var() == it->lit.var(); ++k) {
            assert(k->prio > it->prio && "levels not prepared!");
            auto kLev           = static_cast<uint32_t>(k->prio);
            weights.back().next = 1;
            weights.push_back(SharedData::LevelWeight(kLev, k->weight));
            if (k->lit.sign() != it->lit.sign()) {
                adjust[kLev]          += k->weight;
                weights.back().weight  = -k->weight;
            }
        }
        (*j = *it).weight = wpos;
        ++j;
    }
    lits_.erase(j, lits_.end());
}

MinimizeBuilder::SharedData* MinimizeBuilder::createShared(SharedContext& ctx, SumView adjust,
                                                           const SharedData::WeightVec* weights) {
    const auto nLits = size32(lits_);
    auto* ret = new (::operator new(sizeof(SharedData) + ((nLits + 1) * sizeof(WeightLiteral)))) SharedData(adjust);
    // sort literals by decreasing weight
    auto cmp = [weights](const MLit& lhs, const MLit& rhs) {
        if (not weights) {
            return lhs.weight > rhs.weight;
        }
        const auto* wLhs = lw(*weights, lhs.weight);
        const auto* wRhs = lw(*weights, rhs.weight);
        for (;; ++wLhs, ++wRhs) {
            if (wLhs->level != wRhs->level) {
                return wLhs->level < wRhs->level ? wLhs->weight > 0 : 0 > wRhs->weight;
            }
            if (wLhs->weight != wRhs->weight) {
                return wLhs->weight > wRhs->weight;
            }
            if (not wLhs->next) {
                return wRhs->next && (++wRhs)->weight < 0;
            }
            if (not wRhs->next) {
                ++wLhs;
                break;
            }
        }
        return wLhs->weight > 0;
    };
    std::ranges::stable_sort(lits_, cmp);
    WeightLiteral* out  = ret->lits;
    const MLit*    last = nullptr;
    Weight_t       wIdx = 0;
    for (const auto& lit : lits_) {
        WeightLiteral x{lit.lit, lit.weight};
        ctx.setFrozen(x.lit.var(), true);
        if (weights) {
            if (not last || cmp(*last, lit)) {
                last = &lit;
                wIdx = static_cast<Weight_t>(ret->weights.size());
                for (const auto* w = lw(*weights, x);; ++w) {
                    ret->weights.push_back(*w);
                    if (not w->next) {
                        break;
                    }
                }
            }
            x.weight = wIdx;
        }
        *out++ = x;
    }
    ret->lits[nLits] = WeightLiteral{lit_true, static_cast<Weight_t>(ret->weights.size())};
    if (weights) {
        ret->weights.push_back(SharedData::LevelWeight(size32(adjust) - 1, 0));
    }
    ret->resetBounds();
    return ret;
}

MinimizeBuilder::SharedData* MinimizeBuilder::build(SharedContext& ctx) {
    POTASSCO_CHECK_PRE(not ctx.frozen());
    if (not ctx.ok() || (ctx.master()->acquireProblemVars(), not ctx.master()->propagate()) || empty()) {
        clear();
        return nullptr;
    }
    using FlatVec = SharedData::WeightVec;
    WeightVec prios;
    SumVec    adjust;
    FlatVec   weights;
    prepareLevels(*ctx.master(), adjust, prios);
    if (prios.size() > 1) {
        mergeLevels(adjust, weights);
    }
    else if (prios.empty()) {
        prios.assign(1, 0);
        adjust.assign(1, 0);
    }
    auto* ret = createShared(ctx, adjust, prios.size() > 1 ? &weights : nullptr);
    ret->prios.swap(prios);
    clear();
    return ret;
}
/////////////////////////////////////////////////////////////////////////////////////////
// UncoreMinimize
/////////////////////////////////////////////////////////////////////////////////////////
UncoreMinimize::UncoreMinimize(SharedMinimizeData* d, const OptParams& params)
    : MinimizeConstraint(d)
    , enum_(nullptr)
    , sum_(std::make_unique<Wsum_t[]>(d->numRules()))
    , auxInit_(UINT32_MAX)
    , auxAdd_(0)
    , freeOpen_(0)
    , options_(params) {}
void UncoreMinimize::init() {
    releaseLits();
    fix_.clear();
    eRoot_ = 0;
    aTop_  = 0;
    upper_ = shared_->upper(0);
    lower_ = 0;
    gen_   = 0;
    level_ = 0;
    next_  = 0;
    disj_  = 0;
    path_  = 1;
    init_  = 1;
    actW_  = 1;
    nextW_ = 0;
}
bool UncoreMinimize::attach(Solver& s) {
    init();
    initRoot(s);
    auxInit_ = UINT32_MAX;
    auxAdd_  = 0;
    if (s.sharedContext()->concurrency() > 1 && shared_->mode() == MinimizeMode::enum_opt) {
        enum_ = new DefaultMinimize(shared_->share(), OptParams());
        enum_->attach(s);
        enum_->relaxBound(true);
    }
    return true;
}
// Detaches the constraint and all cores from s and removes
// any introduced aux vars.
void UncoreMinimize::detach(Solver* s, bool b) {
    releaseLits();
    if (s && auxAdd_ && s->numAuxVars() == (auxInit_ + auxAdd_)) {
        s->popAuxVar(auxAdd_, &closed_);
        auxInit_ = UINT32_MAX;
        auxAdd_  = 0;
    }
    Clasp::destroyDB(closed_, s, b);
    fix_.clear();
}
// Destroys this object and optionally detaches it from the given solver.
void UncoreMinimize::destroy(Solver* s, bool b) {
    detach(s, b);
    sum_.reset();
    if (enum_) {
        enum_->destroy(s, b);
        enum_ = nullptr;
    }
    MinimizeConstraint::destroy(s, b);
}
Constraint::PropResult UncoreMinimize::propagate(Solver& s, Literal p, uint32_t& other) {
    return PropResult(s.force(Literal::fromId(other), Antecedent(p)), true);
}
bool UncoreMinimize::simplify(Solver& s, bool) {
    if (s.decisionLevel() == 0) {
        simplifyDB(s, closed_, false);
    }
    return false;
}
void UncoreMinimize::reason(Solver& s, Literal, LitVec& out) {
    uint32_t r = initRoot(s);
    for (uint32_t i = 1; i <= r; ++i) { out.push_back(s.decision(i)); }
}

// Integrates any new information from this constraint into s.
bool UncoreMinimize::integrate(Solver& s) {
    assert(not s.isFalse(tag_));
    bool useTag = (shared_->mode() == MinimizeMode::enum_opt) || s.sharedContext()->concurrency() > 1;
    if (not prepare(s, useTag)) {
        return false;
    }
    if (enum_ && not shared_->optimize() && not enum_->integrateBound(s)) {
        return false;
    }
    for (uint32_t gGen = shared_->generation(); gGen != gen_;) {
        gen_   = gGen;
        upper_ = shared_->upper(level_);
        gGen   = shared_->generation();
    }
    if (init_ && not initLevel(s)) {
        return false;
    }
    if (next_ && not addNext(s)) {
        return false;
    }
    if (path_ && not pushPath(s)) {
        return false;
    }
    if (not validLowerBound()) {
        next_ = 1;
        s.setStopConflict();
        return false;
    }
    return true;
}

// Initializes the next optimization level to look at.
bool UncoreMinimize::initLevel(Solver& s) {
    initRoot(s);
    next_   = 0;
    disj_   = 0;
    actW_   = 1;
    nextW_  = 0;
    sum_[0] = -1;
    if (not fixLevel(s)) {
        return false;
    }
    for (auto lit : fix_) {
        if (not s.force(lit, eRoot_, this)) {
            return false;
        }
    }
    if (not shared_->optimize()) {
        level_ = shared_->maxLevel();
        lower_ = shared_->lower(level_);
        upper_ = shared_->upper(level_);
        path_  = 0;
        init_  = 0;
        return true;
    }
    Weight_t maxW = 1;
    uint32_t next = 1 - init_;
    for (uint32_t level = (level_ + next), n = 1; level <= shared_->maxLevel() && assume_.empty(); ++level) {
        level_ = level;
        lower_ = 0;
        upper_ = shared_->upper(level_);
        for (const auto& wl : *shared_) {
            if (Weight_t w = shared_->weight(wl, level_)) {
                Literal x = wl.lit;
                if (w < 0) {
                    lower_ += w;
                    w       = -w;
                    x       = ~x;
                }
                if (s.value(x.var()) == value_free || s.level(x.var()) > eRoot_) {
                    newAssumption(~x, w);
                    if (w > maxW) {
                        maxW = w;
                    }
                }
                else if (s.isTrue(x)) {
                    lower_ += w;
                }
            }
        }
        if (n == 1) {
            if (lower_ > upper_) {
                next = 1;
                break;
            }
            else if (lower_ < upper_) {
                next = (n = 0);
            }
            else {
                n    = shared_->checkNext() || level != shared_->maxLevel();
                next = n;
                while (not assume_.empty()) {
                    fixLit(s, assume_.back().lit);
                    assume_.pop_back();
                }
                litData_.clear();
                assume_.clear();
                maxW = 1;
            }
        }
    }
    init_ = 0;
    path_ = 1;
    disj_ = options_.hasOption(OptParams::usc_disjoint);
    actW_ = options_.hasOption(OptParams::usc_stratify) ? maxW : 1;
    if (next && not s.hasConflict()) {
        s.force(~tag_, Antecedent(nullptr));
        disj_ = 0;
    }
    if (auxInit_ == UINT32_MAX) {
        auxInit_ = s.numAuxVars();
    }
    return not s.hasConflict();
}

Literal UncoreMinimize::newLit(Solver& s) {
    ++auxAdd_;
    return posLit(s.pushAuxVar());
}
UncoreMinimize::LitPair UncoreMinimize::newAssumption(Literal p, Weight_t w) {
    assert(w > 0);
    if (nextW_ && w > nextW_) {
        nextW_ = w;
    }
    litData_.push_back(LitData(w, true, 0));
    assume_.push_back(LitPair(p, size32(litData_)));
    return assume_.back();
}
bool UncoreMinimize::push(Solver& s, Literal p, uint32_t id) {
    assert(conflict_.empty());
    if (s.pushRoot(p)) {
        return true;
    }
    else if (not s.hasConflict()) {
        conflict_.assign(1, ~p);
        conflict_.push_back(Literal::fromRep(id));
        if (s.level(p.var()) > eRoot_) {
            s.force(p, Antecedent(nullptr));
        }
        else {
            s.setStopConflict();
        }
    }
    return false;
}
// Pushes the active assumptions from the active optimization level to
// the root path.
bool UncoreMinimize::pushPath(Solver& s) {
    assert(not next_);
    for (bool push = path_ != 0; not s.hasConflict() && push;) {
        path_ = 0;
        if (not s.propagate() || not s.simplify()) {
            path_ = 1;
            return false;
        }
        initRoot(s);
        if (todo_.shrink()) {
            return pushTrim(s);
        }
        Wsum_t   fixW = upper_ - lower_, low = 0;
        Weight_t maxW = 0;
        uint32_t j = 0, i = 0, end = size32(assume_);
        bool     ok = true;
        nextW_      = 0;
        for (uint32_t dl; i != end && ok; ++i) {
            LitData& x = getData(assume_[i].id);
            if (x.assume) {
                Literal  p   = assume_[i].lit;
                Weight_t w   = x.weight;
                assume_[j++] = assume_[i];
                if (w < actW_) {
                    nextW_ = std::max(nextW_, w);
                }
                else if (w > fixW) {
                    --j;
                    ok       = fixLit(s, p);
                    push     = false;
                    x.assume = 0;
                    x.weight = 0;
                    if (hasCore(x)) {
                        closeCore(s, x, false);
                    }
                }
                else if (not s.isFalse(p) || s.level(p.var()) > eRoot_) {
                    maxW = std::max(maxW, w);
                    ok   = not push || this->push(s, p, assume_[i].id);
                }
                else {
                    LitPair core(~p, assume_[i].id);
                    --j;
                    dl    = s.decisionLevel();
                    ok    = addCore(s, Potassco::toSpan(core), w, true);
                    low  += w;
                    fixW  = fixW - w;
                    end   = size32(assume_);
                    push  = push && s.decisionLevel() == dl;
                }
            }
        }
        if (i != j) {
            moveDown(assume_, i, j);
        }
        if (low) {
            shared_->incLower(level_, lower_);
        }
        push  = not push || maxW > fixW;
        aTop_ = s.rootLevel();
        POTASSCO_CHECK_PRE(s.decisionLevel() == s.rootLevel(), "pushPath must be called on root level (%u:%u)",
                           s.rootLevel(), s.decisionLevel());
    }
    return not s.hasConflict();
}

// Removes invalid assumptions from the root path.
bool UncoreMinimize::popPath(Solver& s, uint32_t dl) {
    POTASSCO_CHECK_PRE(dl <= aTop_ && eRoot_ <= aTop_ && s.rootLevel() <= aTop_,
                       "You must not mess with my root level!");
    if (dl < eRoot_) {
        dl = eRoot_;
    }
    sum_[0] = -1;
    path_   = 1;
    return s.popRootLevel(s.rootLevel() - (aTop_ = dl));
}

bool UncoreMinimize::relax(Solver& s, bool reset) {
    if (next_ && not reset) {
        // commit cores of last model
        if (todo_.shrink()) {
            resetTrim(s);
        }
        addNext(s, false);
    }

    if (reset && shared_->optimize()) {
        POTASSCO_ASSERT(not auxAdd_ || s.numAuxVars() == (auxInit_ + auxAdd_), "Cannot safely detach constraint");
        detach(&s, true);
        init();
    }
    else {
        releaseLits();
    }
    if (not shared_->optimize()) {
        gen_ = shared_->generation();
    }
    init_ = 1;
    next_ = 0;
    return not enum_ || enum_->relax(s, reset);
}

// Computes the costs of the current assignment.
Wsum_t* UncoreMinimize::computeSum(const Solver& s) const {
    std::fill_n(sum_.get(), shared_->numRules(), static_cast<Wsum_t>(0));
    for (const auto& wl : *shared_) {
        if (s.isTrue(wl.lit)) {
            shared_->add(sum_.get(), wl);
        }
    }
    return sum_.get();
}
// Checks whether the current assignment in s is valid w.r.t the
// bound stored in the shared data object.
bool UncoreMinimize::valid(Solver& s) {
    if (shared_->upper(level_) == SharedData::maxBound()) {
        return true;
    }
    if (sum_[0] < 0) {
        std::ignore = computeSum(s);
    }
    uint32_t end = shared_->numRules();
    Wsum_t   cmp = 0;
    do {
        gen_            = shared_->generation();
        const auto* rhs = shared_->upper();
        upper_          = rhs[level_];
        for (uint32_t i = level_; i != end && (cmp = sum_[i] - rhs[i]) == 0; ++i) {}
    } while (gen_ != shared_->generation());
    if (s.numFreeVars() != 0) {
        sum_[0] = -1;
    }
    if (cmp < static_cast<Wsum_t>(not shared_->checkNext())) {
        return true;
    }
    next_ = 1;
    s.setStopConflict();
    return false;
}
// Sets the current sum as the current shared optimum.
bool UncoreMinimize::handleModel(Solver& s) {
    if (not valid(s)) {
        return false;
    }
    if (sum_[0] < 0) {
        std::ignore = computeSum(s);
    }
    shared_->setOptimum(sum_.get());
    next_  = shared_->checkNext();
    gen_   = shared_->generation();
    upper_ = shared_->upper(level_);
    POTASSCO_ASSERT(not next_ || disj_ || todo_.shrink() || nextW_ || lower_ == sum_[level_],
                    "Unexpected lower bound on model!");
    return true;
}

// Tries to recover from either a model or a root-level conflict.
bool UncoreMinimize::handleUnsat(Solver& s, bool up, LitVec&) {
    assert(s.hasConflict());
    if (enum_) {
        enum_->relaxBound(true);
    }
    bool trimCore = options_.trim != 0u;
    do {
        if (next_ == 0) {
            if (s.hasStopConflict()) {
                return false;
            }
            if (todo_.shrink()) {
                lower_ -= todo_.weight();
                todo_.clear(false);
            }
            uint32_t cs = analyze(s);
            if (not cs) {
                todo_.clear();
                return false;
            }
            lower_ += todo_.weight();
            if (disj_) { // preprocessing: remove assumptions and remember core
                for (const auto& x : todo_.last(cs)) { getData(x.id).assume = 0; }
                todo_.terminate(); // null-terminate core
            }
            else if (trimCore && validLowerBound() && todo_.shrinkNext(*this, value_false)) {
                popPath(s, 0);
            }
            else {
                resetTrim(s);
            }
            next_ = not validLowerBound();
            if (up) {
                shared_->incLower(level_, lower_);
            }
        }
        else {
            s.clearStopConflict();
            addNext(s);
        }
    } while (next_ || s.hasConflict());
    return true;
}

bool UncoreMinimize::addNext(Solver& s, bool allowInit) {
    popPath(s, 0);
    const Wsum_t cmp = (lower_ - upper_);
    if (disj_) {
        for (auto cores = todo_.view(); not cores.empty();) {
            // find end of next (null-terminated) core
            auto cs   = 0u;
            auto minW = weight_max;
            for (; cores[cs].id; ++cs) { minW = std::min(minW, getData(cores[cs].id).weight); }
            if (not addCore(s, cores.subspan(0, cs), minW, false)) {
                break;
            }
            cores = cores.subspan(cs + 1); // pop core
        }
        todo_.clear(false);
    }
    else if (todo_.shrink() && (not todo_.shrinkNext(*this, value_true) || cmp >= 0)) {
        resetTrim(s);
    }
    next_ = 0;
    disj_ = 0;
    if (cmp >= 0) {
        fixLevel(s);
        if (cmp > 0) {
            s.hasConflict() || s.force(~tag_, Antecedent(nullptr));
        }
        else if (level_ != shared_->maxLevel() || shared_->checkNext()) {
            if (allowInit) {
                initLevel(s);
            }
            else if (level_ != shared_->maxLevel()) {
                level_ += (1u - init_);
            }
        }
    }
    else if (not todo_.shrink() && nextW_) {
        actW_ = nextW_;
        disj_ = options_.hasOption(OptParams::usc_disjoint);
    }
    return not s.hasConflict();
}

// Analyzes the current root level conflict and stores the set of our assumptions
// that caused the conflict in todo_.
uint32_t UncoreMinimize::analyze(Solver& s) {
    uint32_t cs    = 0;
    uint32_t minDl = s.decisionLevel();
    if (not conflict_.empty()) {
        LitPair p(conflict_[0], conflict_[1].rep());
        assert(s.isTrue(p.lit));
        todo_.add(p, getData(p.id).weight);
        minDl = s.level(p.lit.var());
        cs    = 1;
    }
    conflict_.clear();
    if (s.decisionLevel() <= eRoot_) {
        return cs;
    }
    s.resolveToCore(conflict_);
    for (auto lit : conflict_) { s.markSeen(lit); }
    // map marked root decisions back to our assumptions
    uint32_t roots  = size32(conflict_), dl;
    cs             += roots;
    for (auto it = assume_.begin(), end = assume_.end(); it != end && roots; ++it) {
        if (Literal p = it->lit; s.seen(p) && (dl = s.level(p.var())) > eRoot_ && dl <= aTop_) {
            assert(p == s.decision(dl) && getData(it->id).assume);
            if (dl < minDl) {
                minDl = dl;
            }
            todo_.add(LitPair(~p, it->id), getData(it->id).weight);
            assert(s.isFalse(~p));
            s.clearSeen(p.var());
            --roots;
        }
    }
    popPath(s, minDl - (minDl != 0));
    if (roots) { // clear remaining levels - can only happen if someone messed with our assumptions
        cs -= roots;
        for (auto lit : conflict_) { s.clearSeen(lit.var()); }
    }
    conflict_.clear();
    return cs;
}

// Eliminates the given core by adding suitable constraints to the solver.
bool UncoreMinimize::addCore(Solver& s, LitView lits, Weight_t w, bool updateLower) {
    assert(s.decisionLevel() == s.rootLevel());
    assert(w && not lits.empty());
    // apply weight and check for subcores
    if (updateLower) {
        lower_ += w;
    }
    for (const auto& [lit, id] : lits) {
        LitData& x = getData(id);
        if (x.weight -= w; x.weight <= 0) {
            x.assume = 0;
            x.weight = 0;
        }
        else if (disj_ && not x.assume) {
            x.assume = 1;
            assume_.push_back(LitPair(~lit, id));
        }
        if (x.weight == 0 && hasCore(x)) {
            Core& core = getCore(x);
            temp_.start(core.bound + 1);
            for (uint32_t k : irange(core)) {
                Literal p = core.at(k);
                while (s.topValue(p.var()) != s.value(p.var()) && s.rootLevel() > eRoot_) {
                    s.popRootLevel(s.rootLevel() - std::max(s.level(p.var()) - 1, eRoot_));
                    aTop_ = std::min(aTop_, s.rootLevel());
                }
                temp_.add(s, p);
            }
            Weight_t cw = core.weight;
            if (not closeCore(s, x, temp_.bound <= 1) || not addOllCon(s, temp_, cw)) {
                return false;
            }
        }
    }
    if (lits.size() == 1) {
        return fixLit(s, lits[0].lit);
    }
    // add new core
    switch (options_.algo) {
        default:
        case OptParams::usc_oll: return addOll(s, lits, w);
        case OptParams::usc_one: return addK(s, size32(lits), lits, w);
        case OptParams::usc_k  : return addK(s, options_.kLim, lits, w);
        case OptParams::usc_pmr: return addPmr(s, lits, w);
    }
}
bool UncoreMinimize::addOll(Solver& s, LitView lits, Weight_t w) {
    temp_.start(2);
    for (const auto& [lit, _] : lits) { temp_.add(s, lit); }
    if (not temp_.unsat()) {
        return addOllCon(s, temp_, w);
    }
    Literal fix = not temp_.lits.empty() ? temp_.lits[0].lit : lits[0].lit;
    return temp_.bound < 2 || fixLit(s, fix);
}

static constexpr auto clause_flags =
    ClauseCreator::clause_explicit | ClauseCreator::clause_not_root_sat | ClauseCreator::clause_no_add;
static constexpr auto weight_flags = WeightConstraint::create_explicit | WeightConstraint::create_no_add |
                                     WeightConstraint::create_no_freeze | WeightConstraint::create_no_share;

bool UncoreMinimize::addK(Solver& s, uint32_t k, LitView lits, Weight_t w) {
    const bool concise = options_.hasOption(OptParams::usc_succinct);
    const auto size    = size32(lits);
    const auto x       = k            ? (size + (k - 1)) / k
                         : size <= 8u ? 1u
                                      : static_cast<unsigned>(std::ceil(size / (((std::log10(size) * 16) - 2) / 2.0)));
    k                  = (size + (x - 1)) / x;
    uint32_t idx       = 1;
    Literal  cp        = ~lits[0].lit, bin[2];
    do {
        uint32_t n = k, connect = idx + k < size;
        if (not connect) {
            n = size - idx;
        }
        temp_.start(static_cast<Weight_t>(n + connect));
        temp_.add(s, cp);
        for (uint32_t i = 0; i != n; ++i) { temp_.add(s, ~lits[idx++].lit); }
        if (connect) {
            bin[0] = newLit(s);
            temp_.add(s, ~bin[0]);
            cp = bin[0];
        }
        for (uint32_t i = 0, b = connect; i != n; ++i, b = 1) {
            Literal ri = newAssumption(newLit(s), w).lit;
            bin[b]     = ri;
            temp_.add(s, ~ri);
            if (b) { // bin[0] -> bin[1];
                addImplication(s, bin[0], bin[1], concise);
                bin[0] = bin[1];
            }
        }
        if (not addConstraint(s, temp_.data(), temp_.size(), temp_.bound)) {
            return false;
        }
    } while (idx != size);
    if (not concise && not s.hasConflict()) {
        for (const auto& [lit, _] : lits) { conflict_.push_back(lit); }
        for (uint32_t i = 1; i <= eRoot_; ++i) { conflict_.push_back(~s.decision(i)); }
        if (auto res = ClauseCreator::create(s, conflict_, clause_flags, ConstraintType::other); res.local) {
            closed_.push_back(res.local);
        }
        conflict_.clear();
    }
    return not s.hasConflict();
}
bool UncoreMinimize::addPmr(Solver& s, LitView lits, Weight_t w) {
    assert(lits.size() > 1);
    uint32_t i  = size32(lits) - 1;
    Literal  bp = lits[i].lit;
    while (--i != 0) {
        Literal an = lits[i].lit;
        Literal bn = newLit(s);
        Literal cn = newLit(s);
        newAssumption(~cn, w);
        if (not addPmrCon(comp_disj, s, bn, an, bp)) {
            return false;
        }
        if (not addPmrCon(comp_conj, s, cn, an, bp)) {
            return false;
        }
        bp = bn;
    }
    Literal an = lits[i].lit;
    Literal cn = newLit(s);
    newAssumption(~cn, w);
    return addPmrCon(comp_conj, s, cn, an, bp);
}
bool UncoreMinimize::addPmrCon(CompType c, Solver& s, Literal head, Literal body1, Literal body2) {
    using Result     = ClauseCreator::Result;
    const bool sign  = c == comp_conj;
    uint32_t   first = 0, last = 3;
    if (options_.hasOption(OptParams::usc_succinct)) {
        first = c == comp_disj;
        last  = first + (1 + (c == comp_disj));
    }
    Literal temp[3][3] = {{(~head) ^ sign, body1 ^ sign, body2 ^ sign},
                          {head ^ sign, (~body1) ^ sign, lit_false},
                          {head ^ sign, (~body2) ^ sign, lit_false}};
    for (uint32_t i = first, sz = 3; i != last; ++i) {
        Result res = ClauseCreator::create(s, ClauseRep::create({temp[i], sz}, ConstraintType::other), clause_flags);
        if (res.local) {
            closed_.push_back(res.local);
        }
        if (not res.ok()) {
            return false;
        }
        sz = 2;
    }
    return true;
}
bool UncoreMinimize::addOllCon(Solver& s, WCTemp& wc, Weight_t weight) {
    Weight_t b = wc.bound;
    if (b <= 0) {
        // constraint is sat and hence conflicting w.r.t new assumption -
        // relax core
        lower_ += ((1 - b) * weight);
        b       = 1;
    }
    if (static_cast<uint32_t>(b) > size32(wc.lits)) {
        // constraint is unsat and hence the new assumption is trivially satisfied
        return true;
    }
    // create new var for this core
    LitPair       aux  = newAssumption(newLit(s), weight);
    WeightLitsRep rep  = {wc.data(), wc.size(), b, static_cast<Weight_t>(wc.size())};
    auto          fset = weight_flags;
    if (options_.hasOption(OptParams::usc_succinct)) {
        fset |= WeightConstraint::create_only_bfb;
    }
    auto res = WeightConstraint::create(s, ~aux.lit, rep, fset);
    if (res.ok() && res.first()) {
        getData(aux.id).coreId = allocCore(res.first(), b, weight, rep.bound != rep.reach);
    }
    return not s.hasConflict();
}
// Adds implication: a -> b either via a single watch on a or as a clause -a v b.
bool UncoreMinimize::addImplication(Solver& s, Literal a, Literal b, bool concise) {
    if (concise) {
        POTASSCO_ASSERT(s.auxVar(a.var()));
        s.addWatch(a, this, b.id());
    }
    else {
        using Result     = ClauseCreator::Result;
        Literal clause[] = {~a, b};
        Result  res      = ClauseCreator::create(s, ClauseRep::create(clause, ConstraintType::other), clause_flags);
        if (res.local) {
            closed_.push_back(res.local);
        }
        if (not res.ok()) {
            return false;
        }
    }
    return true;
}
// Adds the cardinality constraint lits[0] + ... + lits[size-1] >= bound.
bool UncoreMinimize::addConstraint(Solver& s, WeightLiteral* lits, uint32_t size, Weight_t bound) {
    using ResPair     = WeightConstraint::CPair;
    WeightLitsRep rep = {lits, size, bound, static_cast<Weight_t>(size)};
    ResPair       res = WeightConstraint::create(s, lit_true, rep, weight_flags);
    if (res.first()) {
        closed_.push_back(res.first());
    }
    return res.ok();
}

// Computes the solver's initial root level, i.e. all assumptions that are not from us.
uint32_t UncoreMinimize::initRoot(const Solver& s) {
    if (eRoot_ == aTop_ && not s.hasStopConflict()) {
        eRoot_ = s.rootLevel();
        aTop_  = eRoot_;
    }
    return eRoot_;
}

// Assigns p at the solver's initial root level.
bool UncoreMinimize::fixLit(Solver& s, Literal p) {
    assert(s.decisionLevel() >= eRoot_);
    if (s.decisionLevel() > eRoot_ && (not s.isTrue(p) || s.level(p.var()) > eRoot_)) {
        // go back to root level
        s.popRootLevel(s.rootLevel() - eRoot_);
        aTop_ = s.rootLevel();
    }
    if (eRoot_ && s.topValue(p.var()) != trueValue(p)) {
        fix_.push_back(p);
    }
    return not s.hasConflict() && s.force(p, this);
}
// Fixes any remaining assumptions of the active optimization level.
bool UncoreMinimize::fixLevel(Solver& s) {
    for (const auto& [lit, id] : assume_) {
        if (getData(id).assume) {
            fixLit(s, lit);
        }
    }
    releaseLits();
    return not s.hasConflict();
}
void UncoreMinimize::releaseLits() {
    // remaining cores are no longer open - move to closed list
    for (const auto& c : open_) {
        if (c.con) {
            closed_.push_back(c.con);
        }
    }
    open_.clear();
    litData_.clear();
    assume_.clear();
    todo_.clear();
    freeOpen_ = 0;
}

uint32_t UncoreMinimize::allocCore(WeightConstraint* con, Weight_t bound, Weight_t weight, bool open) {
    if (not open) {
        closed_.push_back(con);
        return 0;
    }
    if (freeOpen_) { // pop next slot from free list
        uint32_t fp = freeOpen_ - 1;
        assert(open_[fp].con == nullptr && open_[fp].bound == static_cast<Weight_t>(0xDEADC0DE));
        freeOpen_ = static_cast<uint32_t>(open_[fp].weight);
        open_[fp] = Core(con, bound, weight);
        return fp + 1;
    }
    open_.push_back(Core(con, bound, weight));
    return size32(open_);
}
bool UncoreMinimize::closeCore(Solver& s, LitData& x, bool sat) {
    if (uint32_t coreId = x.coreId) {
        Core& core = open_[coreId - 1];
        x.coreId   = 0;
        // close by moving to closed list
        if (not sat) {
            closed_.push_back(core.con);
        }
        else {
            fixLit(s, core.tag());
            core.con->destroy(&s, true);
        }
        // link slot to free list
        core      = Core(nullptr, static_cast<Weight_t>(0xDEADC0DE), static_cast<Weight_t>(freeOpen_));
        freeOpen_ = coreId;
    }
    return not s.hasConflict();
}
bool UncoreMinimize::pushTrim(Solver& s) {
    assert(not s.hasConflict() && s.rootLevel() == aTop_ && conflict_.empty());
    uint32_t top = aTop_;
    todo_.shrinkPush(*this, s);
    if (aTop_ = s.rootLevel(); aTop_ != top && not s.hasConflict() && options_.tLim) {
        struct Limit : PostPropagator {
            Limit(UncoreMinimize& s, uint64_t lim) : self(&s), limit(lim) {}
            [[nodiscard]] uint32_t priority() const override { return priority_reserved_ufs + 2; }
            bool                   propagateFixpoint(Solver& s, PostPropagator* ctx) override {
                if (ctx || s.stats.conflicts < limit) {
                    return true;
                }
                s.setStopConflict();
                self->next_ = 1;
                self        = nullptr;
                s.removePost(this);
                return false;
            }
            void undoLevel(Solver& s) override {
                if (self) {
                    s.removePost(this);
                }
                this->destroy();
            }
            UncoreMinimize* self;
            uint64_t        limit;
        }* limit = new Limit(*this, s.stats.conflicts + (static_cast<uint64_t>(1) << options_.tLim));
        s.addPost(limit);
        s.addUndoWatch(aTop_, limit);
    }
    else if (s.hasStopConflict() && conflict_.size() == 2) {
        assert(getData(conflict_[1].rep()).assume);
        lower_ -= todo_.weight();
        todo_.clear(true);
        s.clearStopConflict();
        conflict_.clear();
        popPath(s, 0);
        pushPath(s);
    }
    return not s.hasConflict();
}
void UncoreMinimize::resetTrim(Solver& s) {
    if (todo_.size()) {
        addCore(s, todo_.view(), todo_.weight(), false);
        todo_.clear();
    }
}
uint32_t UncoreMinimize::Core::size() const { return con->size() - 1; }
Literal  UncoreMinimize::Core::at(uint32_t i) const { return con->lit(i + 1, WeightConstraint::ffb_btb); }
Literal  UncoreMinimize::Core::tag() const { return con->lit(0, WeightConstraint::ftb_bfb); }
void     UncoreMinimize::WCTemp::add(const Solver& s, Literal p) {
    if (s.topValue(p.var()) == value_free) {
        lits.push_back(WeightLiteral{p, 1});
    }
    else if (s.isTrue(p)) {
        --bound;
    }
}
void UncoreMinimize::Todo::clear(bool withShrink) {
    lits_.clear();
    minW_ = weight_max;
    if (withShrink) {
        shrinkReset();
    }
}
void UncoreMinimize::Todo::shrinkReset() {
    core_.clear();
    last_ = next_ = step_ = 0;
}
void UncoreMinimize::Todo::terminate() {
    lits_.push_back(LitPair(lit_true, 0));
    minW_ = weight_max;
}
void UncoreMinimize::Todo::add(const LitPair& x, Weight_t w) {
    lits_.push_back(x);
    if (w < minW_) {
        minW_ = w;
    }
}
void UncoreMinimize::Todo::shrinkPush(UncoreMinimize& self, Solver& s) {
    const uint32_t skip = step_ < size32(core_) ? core_[step_].id : 0u;
    uint32_t       n    = next_;
    for (auto it = lits_.end(); n--;) {
        const LitPair& x = *--it;
        if (x.id != skip && not self.push(s, ~x.lit, x.id)) {
            break;
        }
    }
}
bool UncoreMinimize::Todo::shrinkNext(UncoreMinimize& self, Val_t result) {
    if (self.options_.trim == OptParams::usc_trim_min) {
        return subsetNext(self, result);
    }
    if (result == value_false) {
        next_ = last_;
        step_ = 0u;
    }
    else {
        last_ = next_;
    }
    const uint32_t t  = self.options_.trim;
    const uint32_t mx = size();
    uint32_t       s  = step_;
    switch (t) {
        default:
        case OptParams::usc_trim_lin: step_ = s = 1; break;
        case OptParams::usc_trim_inv: step_ = s = (mx - next_) - 1; break;
        case OptParams::usc_trim_bin: step_ = s = (mx - next_) / 2; break;
        case OptParams::usc_trim_rgs: // fallthrough
        case OptParams::usc_trim_exp:
            if (s == 0u) {
                step_ = s = static_cast<uint32_t>(last_ == 0u);
            }
            else if ((next_ + s) < mx) {
                step_ = s * 2;
            }
            else if (t == OptParams::usc_trim_rgs) {
                step_ = 2;
                s     = 1;
            }
            else {
                s = (mx - next_) / 2;
            }
            break;
    }
    return s && (next_ += s) < mx;
}
bool UncoreMinimize::Todo::subsetNext(UncoreMinimize& self, Val_t result) {
    if (result == value_true) {
        ++step_;
    }
    else if (not core_.empty()) {
        for (const auto& lit : lits_) { self.setFlag(lit.id, true); }
        auto     j      = core_.begin();
        uint32_t marked = 0u;
        for (LitSet::const_iterator it = j, s = j + step_, end = core_.end(); it != end; ++it) {
            if (self.flagged(it->id)) {
                self.setFlag(it->id, false);
                ++marked;
                *j++ = *it;
            }
            else if (j < s) {
                --s, --step_;
            }
        }
        assert(marked == size());
        core_.erase(j, core_.end());
        next_ = marked;
    }
    else {
        for (auto it = lits_.end(), end = lits_.begin(); it != end;) { core_.push_back(*--it); }
        step_ = 0;
        next_ = size();
    }
    return step_ < size() && size() > 1;
}
} // namespace Clasp
