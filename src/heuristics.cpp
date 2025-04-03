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
#include <clasp/heuristics.h>

#include <clasp/clause.h>

#include <potassco/basic_types.h>
#include <potassco/error.h>

#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <limits>
#include <string>
#include <utility>
namespace Clasp {
/////////////////////////////////////////////////////////////////////////////////////////
// Lookback selection strategies
/////////////////////////////////////////////////////////////////////////////////////////
uint32_t momsScore(const Solver& s, Var_t v) {
    uint32_t sc[2];
    if (s.sharedContext()->numBinary()) {
        sc[0] = s.estimateBCP(posLit(v), 0) - 1;
        sc[1] = s.estimateBCP(negLit(v), 0) - 1;
    }
    else {
        // problem does not contain binary constraints - fall back to counting watches
        sc[0] = s.numWatches(posLit(v));
        sc[1] = s.numWatches(negLit(v));
    }
    return ((sc[0] * sc[1]) << 10) + (sc[0] + sc[1]);
}
static void addOther(TypeSet& t, uint32_t other) {
    if (other != HeuParams::other_no) {
        t.add(ConstraintType::loop);
    }
    if (other == HeuParams::other_all) {
        t.add(ConstraintType::other);
    }
}
/////////////////////////////////////////////////////////////////////////////////////////
// Berkmin selection strategy
/////////////////////////////////////////////////////////////////////////////////////////
static constexpr auto berk_num_candidates = 5;
static constexpr auto berk_cache_grow     = 2.0;
static constexpr auto berk_max_moms_vars  = 9999;
static constexpr auto berk_max_moms_decs  = 50;
static constexpr auto berk_max_decay      = 65534;

ClaspBerkmin::ClaspBerkmin(const HeuParams& params)
    : topConflict_(UINT32_MAX)
    , topOther_(UINT32_MAX)
    , front_(1)
    , cacheFront_()
    , cacheSize_(5)
    , numVsids_(0)
    , maxBerkmin_(0) {
    ClaspBerkmin::setConfig(params);
}

void ClaspBerkmin::setConfig(const HeuParams& params) {
    maxBerkmin_  = params.param == 0 ? UINT32_MAX : params.param;
    order_.nant  = params.nant != 0;
    order_.huang = params.huang != 0;
    order_.resScore =
        params.score == HeuParams::score_auto ? static_cast<uint32_t>(HeuParams::score_multi_set) : params.score;
    addOther(types_ = TypeSet(), params.other);
    if (params.moms) {
        types_.add(ConstraintType::static_);
    }
}

Var_t ClaspBerkmin::getMostActiveFreeVar(const Solver& s) {
    ++numVsids_;
    // first: check for a cache hit
    for (Pos end = cache_.end(); cacheFront_ != end; ++cacheFront_) {
        if (s.value(*cacheFront_) == value_free) {
            return *cacheFront_;
        }
    }
    // Second: cache miss - refill cache with most active vars
    if (not cache_.empty() && cacheSize_ < s.numFreeVars() / 10) {
        cacheSize_ = static_cast<uint32_t>((cacheSize_ * berk_cache_grow) + .5); // NOLINT(*-incorrect-roundings)
    }
    cache_.clear();
    Order::Compare comp(&order_);
    // Pre: At least one unassigned var!
    for (; s.value(front_) != value_free; ++front_) { ; }
    auto v = front_;
    assert(cacheSize_);
    for (auto cs = std::min(cacheSize_, s.numFreeVars());;) { // add first cs free variables to cache
        cache_.push_back(v);
        std::ranges::push_heap(cache_, comp);
        if (--cs == 0) {
            for (auto n : s.vars(v + 1)) {
                // replace vars with low activity
                if (s.value(n) == value_free && comp(n, cache_[0])) {
                    std::ranges::pop_heap(cache_, comp);
                    cache_.back() = n;
                    std::ranges::push_heap(cache_, comp);
                }
            }
            std::ranges::sort_heap(cache_, comp);
            return *(cacheFront_ = cache_.begin());
        }
        while (s.value(++v) != value_free) { ; } // skip over assigned vars
    }
}

Var_t ClaspBerkmin::getTopMoms(const Solver& s) {
    // Pre: At least one unassigned var!
    for (; s.value(front_) != value_free; ++front_) { ; }
    Var_t    var = front_;
    uint32_t ms  = momsScore(s, var);
    for (auto v = var + 1; v <= s.numProblemVars(); ++v) {
        if (uint32_t ls = s.value(v) == value_free ? momsScore(s, v) : 0u; ls > ms) {
            var = v;
            ms  = ls;
        }
    }
    if (++numVsids_ >= berk_max_moms_decs || ms < 2) {
        // Scores are not relevant or too many moms-based decisions
        // - disable MOMS
        hasActivities(true);
    }
    return var;
}

void ClaspBerkmin::startInit(const Solver& s) {
    if (order_.score.empty()) {
        rng_.srand(s.rng.seed());
    }
    order_.score.resize(s.numVars() + 1);
    initHuang(order_.huang);

    cache_.clear();
    cacheSize_  = 5;
    cacheFront_ = cache_.end();

    freeLits_.clear();
    freeOtherLits_.clear();
    topConflict_ = topOther_ = static_cast<uint32_t>(-1);

    front_    = 1;
    numVsids_ = 0;
}

void ClaspBerkmin::endInit(Solver& s) {
    if (initHuang()) {
        const bool clearScore = types_.contains(ConstraintType::static_);
        // initialize preferred values of vars
        cache_.clear();
        for (auto v : s.vars()) {
            order_.decayedScore(v);
            if (order_.occ(v) != 0 && s.pref(v).get(ValueSet::saved_value) == value_free) {
                s.setPref(v, ValueSet::saved_value, order_.occ(v) > 0 ? value_true : value_false);
            }
            if (clearScore) {
                order_.score[v] = HScore(order_.decay);
            }
            else {
                cache_.push_back(v);
            }
        }
        initHuang(false);
    }
    if (not types_.contains(ConstraintType::static_) || s.numFreeVars() > berk_max_moms_vars) {
        hasActivities(true);
    }
    std::ranges::stable_sort(cache_, Order::Compare(&order_));
    cacheFront_ = cache_.begin();
}

void ClaspBerkmin::updateVar(const Solver& s, Var_t v, uint32_t n) {
    if (s.validVar(v)) {
        growVecTo(order_.score, v + n);
    }
    front_ = 1;
    cache_.clear();
    cacheFront_ = cache_.end();
}

void ClaspBerkmin::newConstraint(const Solver& s, LitView lits, ConstraintType t) {
    if (t == ConstraintType::conflict) {
        hasActivities(true);
    }
    if ((t == ConstraintType::conflict && order_.resScore == HeuParams::score_min) ||
        (t == ConstraintType::static_ && order_.huang)) {
        for (const auto& lit : lits) { order_.inc(lit, s.varInfo(lit.var()).nant()); }
    }
    if (t != ConstraintType::static_ && not order_.huang) {
        for (const auto& lit : lits) { order_.incOcc(lit); }
    }
}

void ClaspBerkmin::updateReason(const Solver& s, LitView lits, Literal r) {
    if (order_.resScore > HeuParams::score_min) {
        const bool ms = order_.resScore == HeuParams::score_multi_set;
        for (auto lit : lits) {
            if (ms || not s.seen(lit)) {
                order_.inc(~lit, s.varInfo(lit.var()).nant());
            }
        }
    }
    if ((order_.resScore & 1u) != 0 && not isSentinel(r)) {
        order_.inc(r, s.varInfo(r.var()).nant());
    }
}

bool ClaspBerkmin::bump(const Solver& s, WeightLitView lits, double adj) {
    for (const auto& lit : lits) {
        if (not order_.nant || s.varInfo(lit.lit.var()).nant()) {
            auto     sc = lit.weight * adj;
            uint32_t xf = order_.decayedScore(lit.lit.var()) + (sc > 0 ? static_cast<uint32_t>(sc) : 0u);
            order_.score[lit.lit.var()].act = static_cast<uint16_t>(std::min(xf, UINT32_MAX >> 16));
        }
    }
    return true;
}

void ClaspBerkmin::undo(const Solver&, LitView) {
    topConflict_ = topOther_ = static_cast<uint32_t>(-1);
    front_                   = 1;
    cache_.clear();
    cacheFront_ = cache_.end();
    if (cacheSize_ > 5 && numVsids_ > 0 && (numVsids_ * 3) < cacheSize_) {
        cacheSize_ = static_cast<uint32_t>(cacheSize_ / berk_cache_grow);
    }
    numVsids_ = 0;
}

bool ClaspBerkmin::hasTopUnsat(const Solver& s) {
    static constexpr auto conflict_set = TypeSet{ConstraintType::conflict};

    topConflict_ = std::min(s.numLearntConstraints(), topConflict_);
    topOther_    = std::min(s.numLearntConstraints(), topOther_);
    assert(topConflict_ <= topOther_);
    freeOtherLits_.clear();
    freeLits_.clear();
    TypeSet ts = types_;
    if (ts > conflict_set) {
        while (topOther_ > topConflict_) {
            if (s.getLearnt(topOther_ - 1).isOpen(s, ts, freeLits_) != 0) {
                freeLits_.swap(freeOtherLits_);
                ts.clear();
                break;
            }
            --topOther_;
            freeLits_.clear();
        }
    }
    ts.add(ConstraintType::conflict);
    uint32_t stopAt = topConflict_ < maxBerkmin_ ? 0 : topConflict_ - maxBerkmin_;
    while (topConflict_ != stopAt) {
        if (uint32_t x = s.getLearnt(topConflict_ - 1).isOpen(s, ts, freeLits_); x != 0) {
            if (x == ConstraintType::conflict) {
                break;
            }
            topOther_ = topConflict_;
            freeLits_.swap(freeOtherLits_);
            ts = conflict_set;
        }
        --topConflict_;
        freeLits_.clear();
    }
    if (freeOtherLits_.empty()) {
        topOther_ = topConflict_;
    }
    if (freeLits_.empty()) {
        freeOtherLits_.swap(freeLits_);
    }
    return not freeLits_.empty();
}

Literal ClaspBerkmin::doSelect(Solver& s) {
    const uint32_t decayMask = order_.huang ? 127 : 511;
    if (not Potassco::test_any(s.stats.choices + 1, decayMask)) {
        if (auto dec = order_.decay += (1 + not order_.huang); dec == berk_max_decay) {
            order_.resetDecay();
        }
    }
    if (hasTopUnsat(s)) { // Berkmin based decision
        assert(not freeLits_.empty());
        Literal x = selectRange(s, freeLits_);
        return selectLiteral(s, x.var(), false);
    }
    if (hasActivities()) { // Vsids based decision
        return selectLiteral(s, getMostActiveFreeVar(s), true);
    }
    // Moms based decision
    return selectLiteral(s, getTopMoms(s), true);
}

Literal ClaspBerkmin::selectRange(Solver& s, LitView range) {
    Literal candidates[berk_num_candidates];
    candidates[0] = range[0];
    uint32_t c    = 1;
    auto     ms   = static_cast<uint32_t>(-1);
    for (auto lit : drop(range, 1u)) {
        auto v = lit.var();
        assert(s.value(v) == value_free);
        if (int cmp = order_.compare(v, candidates[0].var()); cmp > 0) {
            candidates[0] = lit;
            c             = 1;
            ms            = static_cast<uint32_t>(-1);
        }
        else if (cmp == 0) {
            if (ms == static_cast<uint32_t>(-1)) {
                ms = momsScore(s, candidates[0].var());
            }
            if (uint32_t ls = momsScore(s, v); ls > ms) {
                candidates[0] = lit;
                c             = 1;
                ms            = ls;
            }
            else if (ls == ms && c != berk_num_candidates) {
                candidates[c++] = lit;
            }
        }
    }
    return c == 1 ? candidates[0] : candidates[rng_.irand(c)];
}

Literal ClaspBerkmin::selectLiteral(const Solver& s, Var_t v, bool vsids) const {
    ValueSet pref      = s.pref(v);
    int      signScore = order_.occ(v);
    if (order_.huang && std::abs(signScore) > 32 && not pref.has(ValueSet::user_value)) {
        return {v, signScore < 0};
    }
    // compute expensive sign score only if necessary
    if (vsids && not pref.has(ValueSet::user_value | ValueSet::pref_value | ValueSet::saved_value)) {
        auto w0 = static_cast<int32_t>(s.estimateBCP(posLit(v), 5));
        auto w1 = static_cast<int32_t>(s.estimateBCP(negLit(v), 5));
        if (w1 != 1 || w0 != w1) {
            signScore = w0 - w1;
        }
    }
    return DecisionHeuristic::selectLiteral(s, v, signScore);
}

void ClaspBerkmin::Order::resetDecay() {
    for (auto i : irange(1u, size32(score))) {
        decayedScore(i);
        score[i].dec = 0;
    }
    decay = 0;
}
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspVmtf selection strategy
/////////////////////////////////////////////////////////////////////////////////////////
ClaspVmtf::ClaspVmtf(const HeuParams& params) { ClaspVmtf::setConfig(params); }

void ClaspVmtf::setConfig(const HeuParams& params) {
    nMove_  = params.param ? std::max(params.param, 2u) : 8u;
    scType_ = params.score != HeuParams::score_auto ? params.score : static_cast<uint32_t>(HeuParams::score_min);
    nant_   = params.nant != 0;
    addOther(types_ = TypeSet(),
             params.other != HeuParams::other_auto ? params.other : static_cast<uint32_t>(HeuParams::other_no));
    if (params.moms) {
        types_.add(ConstraintType::static_);
    }
    if (scType_ == HeuParams::score_min) {
        types_.add(ConstraintType::conflict);
    }
}

void ClaspVmtf::startInit(const Solver& s) { score_.resize(s.numVars() + 1, VarInfo()); }

void ClaspVmtf::addToList(Var_t v) {
    assert(v && v < score_.size() && not score_[v].inList());
    VarInfo& link   = score_[v];
    Var_t    tl     = score_[0].prev;
    link.next       = 0;
    link.prev       = tl;
    score_[tl].next = v;
    score_[0].prev  = v;
    ++nList_;
}

void ClaspVmtf::removeFromList(Var_t v) {
    assert(v && v < score_.size() && score_[v].inList());
    VarInfo& link          = score_[v];
    score_[link.next].prev = link.prev;
    score_[link.prev].next = link.next;
    link.prev = link.next = 0;
    --nList_;
}

void ClaspVmtf::moveToFront(Var_t v) {
    if (score_[0].next == v) {
        return;
    }
    removeFromList(v);
    Var_t ph        = score_[0].next;
    score_[v].next  = ph;
    score_[ph].prev = v;
    score_[0].next  = v;
    score_[v].prev  = 0;
    ++nList_;
}

void ClaspVmtf::endInit(Solver& s) {
    bool moms     = types_.contains(ConstraintType::static_);
    auto varRange = s.vars();
    if (not moms) {
        // - add all new vars
        for (auto v : varRange) {
            if (s.value(v) == value_free) {
                score_[v].activity(decay_);
                if (not score_[v].inList()) {
                    addToList(v);
                }
            }
        }
    }
    else {
        // - set activity of all vars not in list to moms
        // - append new vars in moms-activity order
        const uint32_t momsStamp = decay_ + 1;
        const uint32_t assumeNew = (s.numVars() + 1) - nList_;
        VarVec         vars;
        vars.reserve(assumeNew);
        for (auto v : varRange) {
            if (s.value(v) == value_free) {
                score_[v].activity(decay_);
                if (not score_[v].inList()) {
                    score_[v].act   = momsScore(s, v);
                    score_[v].decay = momsStamp;
                    vars.push_back(v);
                }
            }
        }
        std::ranges::stable_sort(vars, LessLevel(s, score_));
        for (auto var : vars) {
            addToList(var);
            if (score_[var].decay == momsStamp) {
                score_[var].act   = 0;
                score_[var].decay = decay_;
            }
        }
    }
    front_ = getFront();
}

void ClaspVmtf::updateVar(const Solver& s, Var_t v, uint32_t n) {
    if (s.validVar(v)) {
        growVecTo(score_, v + n, VarInfo());
        for (auto end = v + n; v != end; ++v) {
            if (not score_[v].inList()) {
                addToList(v);
            }
            else {
                front_ = getFront();
            }
        }
    }
    else if (auto sz = size32(score_); v < sz) {
        if ((v + n) > sz) {
            n = sz - v;
        }
        for (uint32_t x = v + n; x-- != v;) {
            if (score_[x].inList()) {
                removeFromList(x);
            }
        }
    }
}

void ClaspVmtf::simplify(const Solver&, LitView facts) {
    for (auto lit : facts) {
        if (score_[lit.var()].inList()) {
            removeFromList(lit.var());
        }
    }
    front_ = getFront();
}

void ClaspVmtf::newConstraint(const Solver& s, LitView lits, ConstraintType t) {
    if (t != ConstraintType::static_) {
        LessLevel  comp(s, score_);
        const bool upAct = types_.contains(t);
        const auto mtf   = t == ConstraintType::conflict ? nMove_ : (nMove_ * static_cast<uint32_t>(upAct)) / 2;
        for (const auto& lit : lits) {
            auto v         = lit.var();
            score_[v].occ += 1 - (static_cast<int>(lit.sign()) << 1);
            if (upAct) {
                ++score_[v].activity(decay_);
            }
            if (mtf && (not nant_ || s.varInfo(v).nant())) {
                if (size32(mtf_) < mtf) {
                    mtf_.push_back(v);
                    std::ranges::push_heap(mtf_, comp);
                }
                else if (comp(v, mtf_[0])) {
                    assert(s.level(v) <= s.level(mtf_[0]));
                    std::ranges::pop_heap(mtf_, comp);
                    mtf_.back() = v;
                    std::ranges::push_heap(mtf_, comp);
                }
            }
        }
        for (auto v : mtf_) {
            if (score_[v].inList()) {
                moveToFront(v);
            }
        }
        mtf_.clear();
        front_ = getFront();
    }
}

void ClaspVmtf::undo(const Solver&, LitView) { front_ = getFront(); }

void ClaspVmtf::updateReason(const Solver& s, LitView lits, Literal r) {
    if (scType_ > HeuParams::score_min) {
        const bool     ms  = scType_ == HeuParams::score_multi_set;
        const uint32_t dec = decay_;
        for (auto lit : lits) {
            if (ms || not s.seen(lit)) {
                ++score_[lit.var()].activity(dec);
            }
        }
    }
    if (scType_ & 1u) {
        ++score_[r.var()].activity(decay_);
    }
}

bool ClaspVmtf::bump(const Solver&, WeightLitView lits, double adj) {
    for (const auto& [lit, w] : lits) { score_[lit.var()].activity(decay_) += static_cast<uint32_t>(w * adj); }
    return true;
}

Literal ClaspVmtf::doSelect(Solver& s) {
    decay_ += ((s.stats.choices + 1) & 511) == 0;
    for (; s.value(front_) != value_free; front_ = getNext(front_)) { ; }
    Literal c;
    if (s.numFreeVars() > 1) {
        auto     v2       = front_;
        uint32_t distance = 0;
        do {
            v2 = getNext(v2);
            ++distance;
        } while (s.value(v2) != value_free);
        c = (score_[front_].activity(decay_) + (distance << 1) + 3) > score_[v2].activity(decay_)
                ? selectLiteral(s, front_, score_[front_].occ)
                : selectLiteral(s, v2, score_[v2].occ);
    }
    else {
        c = selectLiteral(s, front_, score_[front_].occ);
    }
    return c;
}

Literal ClaspVmtf::selectRange(Solver&, LitView range) {
    return *std::ranges::max_element(range, [this](Literal best, Literal current) {
        return score_[current.var()].activity(decay_) > score_[best.var()].activity(decay_);
    });
}
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspVsids selection strategy
/////////////////////////////////////////////////////////////////////////////////////////
static bool   isDom(const VsidsScore&) { return false; }
static bool   isDom(const DomScore& s) { return s.isDom(); }
static double initDecay(uint32_t p) {
    double m = p ? static_cast<double>(p) : 0.95;
    while (m > 1.0) { m /= 10.0; }
    return m;
}

template <typename ScoreType>
ClaspVsidsBase<ScoreType>::ClaspVsidsBase(const HeuParams& params) : vars_(CmpScore(score_)) {
    ClaspVsidsBase::setConfig(params);
}

template <typename ScoreType>
void ClaspVsidsBase<ScoreType>::setConfig(const HeuParams& params) {
    addOther(types_ = TypeSet(),
             params.other != HeuParams::other_auto ? params.other : static_cast<uint32_t>(HeuParams::other_no));
    scType_ = params.score != HeuParams::score_auto ? params.score : static_cast<uint32_t>(HeuParams::score_min);
    dyn_    = {};
    auto d  = initDecay(params.param);
    if (params.decay.init && params.decay.init != params.param && params.decay.freq) {
        auto b    = initDecay(params.decay.init);
        dyn_.curr = std::min(d, b);
        dyn_.stop = std::max(d, b);
        dyn_.bump = params.decay.bump;
        dyn_.freq = dyn_.next = params.decay.freq;
        d                     = dyn_.curr;
    }
    decay_ = 1.0 / d;
    acids_ = params.acids != 0;
    nant_  = params.nant != 0;
    if (params.moms) {
        types_.add(ConstraintType::static_);
    }
    if (scType_ == HeuParams::score_min) {
        types_.add(ConstraintType::conflict);
    }
}

template <typename ScoreType>
void ClaspVsidsBase<ScoreType>::startInit(const Solver& s) {
    score_.resize(s.numVars() + 1);
    occ_.resize(s.numVars() + 1);
    vars_.reserve(s.numVars() + 1);
}

template <typename ScoreType>
void ClaspVsidsBase<ScoreType>::endInit(Solver& s) {
    vars_.clear();
    initScores(s, types_.contains(ConstraintType::static_));
    double   mx   = 0;
    unsigned warn = 0;
    for (auto v : s.vars()) {
        if (s.value(v) != value_free) {
            if (s.sharedContext()->eliminated(v) && isDom(score_[v])) {
                ++warn;
            }
            continue;
        }
        mx = std::max(mx, score_[v].get());
        if (not vars_.is_in_queue(v)) {
            vars_.push(v);
        }
    }
    if (acids_ && mx > inc_) {
        inc_ = std::ceil(mx);
    }
    if (warn && s.isMaster()) {
        s.sharedContext()->warn("heuristic modifications on eliminated variables - results may be unexpected");
    }
}
template <typename ScoreType>
void ClaspVsidsBase<ScoreType>::updateVarActivity(const Solver& s, Var_t v, double f) {
    if (not nant_ || s.varInfo(v).nant()) {
        double o = score_[v].get(), n;
        f        = ScoreType::applyFactor(score_, v, f);
        if (not acids_) {
            n = o + (f * inc_);
        }
        else if (f == 1.0) {
            n = (o + inc_) / 2.0;
        }
        else if (f != 0.0) {
            n = std::max((o + inc_ + f) / 2.0, f + o);
        }
        else {
            return;
        }
        score_[v].set(n);
        if (n > 1e100) {
            normalize();
        }
        if (vars_.is_in_queue(v)) {
            if (n >= o) {
                vars_.increase(v);
            }
            else {
                vars_.decrease(v);
            }
        }
    }
}
template <typename ScoreType>
void ClaspVsidsBase<ScoreType>::updateVar(const Solver& s, Var_t v, uint32_t n) {
    if (s.validVar(v)) {
        growVecTo(score_, v + n);
        growVecTo(occ_, v + n);
        for (uint32_t end = v + n; v != end; ++v) { vars_.update(v); }
    }
    else {
        for (uint32_t end = v + n; v != end; ++v) { vars_.remove(v); }
    }
}
template <typename ScoreType>
void ClaspVsidsBase<ScoreType>::initScores(Solver& s, bool moms) {
    if (not moms) {
        return;
    }
    double maxS     = 0.0;
    auto   varRange = s.vars();
    for (auto v : varRange) {
        if (s.value(v) != value_free || score_[v].get() != 0.0) {
            continue;
        }
        if (auto ms = static_cast<double>(momsScore(s, v)); ms != 0.0) {
            maxS = std::max(maxS, ms);
            score_[v].set(-ms);
        }
    }
    for (auto v : varRange) {
        if (double d = score_[v].get(); d < 0) {
            d *= -1.0;
            d /= maxS;
            score_[v].set(d);
        }
    }
}
template <typename ScoreType>
void ClaspVsidsBase<ScoreType>::simplify(const Solver&, LitView facts) {
    for (auto lit : facts) { vars_.remove(lit.var()); }
}

template <typename ScoreType>
void ClaspVsidsBase<ScoreType>::normalize() {
    constexpr double min   = std::numeric_limits<double>::min();
    constexpr double minD  = min * 1e100;
    inc_                  *= 1e-100;
    for (ScoreType& sc : score_) {
        double d = sc.get();
        if (d > 0) {
            // keep relative ordering but
            // actively avoid denormals
            d += minD;
            d *= 1e-100;
        }
        sc.set(d);
    }
}
template <typename ScoreType>
void ClaspVsidsBase<ScoreType>::newConstraint(const Solver& s, LitView lits, ConstraintType t) {
    if (t != ConstraintType::static_) {
        const bool upAct = types_.contains(t);
        for (const auto& lit : lits) {
            incOcc(lit);
            if (upAct) {
                updateVarActivity(s, lit.var());
            }
        }
        if (t == ConstraintType::conflict) {
            if (dyn_.next && --dyn_.next == 0) {
                dyn_.curr += dyn_.bump / 100.0;
                decay_     = 1.0 / dyn_.curr;
                if (dyn_.curr < dyn_.stop) {
                    dyn_.next = dyn_.freq;
                }
            }
            if (not acids_) {
                inc_ *= decay_;
            }
            else {
                inc_ += 1.0;
            }
        }
    }
}
template <typename ScoreType>
void ClaspVsidsBase<ScoreType>::updateReason(const Solver& s, LitView lits, Literal r) {
    if (scType_ > HeuParams::score_min) {
        const bool ms = scType_ == HeuParams::score_multi_set;
        for (auto lit : lits) {
            if (ms || not s.seen(lit)) {
                updateVarActivity(s, lit.var());
            }
        }
    }
    if ((scType_ & 1u) != 0 && r.var() != 0) {
        updateVarActivity(s, r.var());
    }
}
template <typename ScoreType>
bool ClaspVsidsBase<ScoreType>::bump(const Solver& s, WeightLitView lits, double adj) {
    double mf = 1.0, f;
    for (const auto& [lit, weight] : lits) {
        updateVarActivity(s, lit.var(), (f = weight * adj));
        if (acids_ && f > mf) {
            mf = f;
        }
    }
    if (acids_ && mf > 1.0) {
        inc_ = std::ceil(mf + inc_);
    }
    return true;
}
template <typename ScoreType>
void ClaspVsidsBase<ScoreType>::undo(const Solver&, LitView undo) {
    for (auto lit : undo) {
        if (not vars_.is_in_queue(lit.var())) {
            vars_.push(lit.var());
        }
    }
}
template <typename ScoreType>
Literal ClaspVsidsBase<ScoreType>::doSelect(Solver& s) {
    while (s.value(vars_.top()) != value_free) { vars_.pop(); }
    return selectLiteral(s, vars_.top(), occ(vars_.top()));
}
template <typename ScoreType>
Literal ClaspVsidsBase<ScoreType>::selectRange(Solver&, LitView range) {
    return *std::ranges::max_element(
        range, [&cmp = vars_.key_compare()](Literal best, Literal current) { return cmp(current.var(), best.var()); });
}
template class ClaspVsidsBase<VsidsScore>;

/////////////////////////////////////////////////////////////////////////////////////////
// DomainHeuristic selection strategy
/////////////////////////////////////////////////////////////////////////////////////////
DomainHeuristic::DomainHeuristic(const HeuParams& params)
    : ClaspVsidsBase(params)
    , domSeen_(0)
    , defMax_(0)
    , defMod_(0)
    , defPref_(0) {
    frames_.push_back(Frame(0, DomAction::undo_nil));
    setDefaultMod(static_cast<HeuParams::DomMod>(params.domMod), params.domPref);
}
DomainHeuristic::~DomainHeuristic() = default;

void DomainHeuristic::setConfig(const HeuParams& params) {
    ClaspVsidsBase::setConfig(params);
    setDefaultMod(static_cast<HeuParams::DomMod>(params.domMod), params.domPref);
}
void DomainHeuristic::setDefaultMod(HeuParams::DomMod mod, uint32_t prefSet) {
    defMod_  = static_cast<uint16_t>(mod);
    defPref_ = prefSet;
}
void DomainHeuristic::detach(Solver& s) {
    if (not actions_.empty()) {
        for (const auto& dom : s.sharedContext()->heuristic) {
            if (dom.hasCondition()) {
                s.removeWatch(dom.cond(), this);
            }
        }
    }
    while (frames_.back().dl != 0) {
        s.removeUndoWatch(frames_.back().dl, this);
        frames_.pop_back();
    }
    for (auto v : irange(std::min(size32(score_), s.numVars() + 1))) {
        if (score_[v].sign) {
            s.setPref(v, ValueSet::user_value, value_free);
        }
    }
    actions_.clear();
    prios_.clear();
    domSeen_ = 0;
    defMax_  = 0;
}
void DomainHeuristic::startInit(const Solver& s) {
    BaseType::startInit(s);
    domSeen_ = std::min(domSeen_, s.sharedContext()->heuristic.size());
}
void DomainHeuristic::initScores(Solver& s, bool moms) {
    const DomainTable& domTab = s.sharedContext()->heuristic;
    BaseType::initScores(s, moms);
    auto nKey = size32(prios_);
    if (defMax_) {
        defMax_ = std::min(defMax_, s.numVars()) + 1;
        for (auto v : irange(1u, defMax_)) {
            if (score_[v].domP >= nKey) {
                bool sign = score_[v].sign;
                score_[v] = DomScore(score_[v].value);
                if (sign) {
                    s.setPref(v, ValueSet::user_value, value_free);
                }
            }
        }
        defMax_ = 0;
    }
    if (domSeen_ < domTab.size()) {
        // apply new domain modifications
        VarScoreVec saved;
        Literal     lastW = lit_true;
        uint32_t    dKey  = nKey;
        for (const auto& dom : domTab.dropView(domSeen_)) {
            if (s.topValue(dom.var()) != value_free || s.isFalse(dom.cond())) {
                continue;
            }
            if (score_[dom.var()].domP >= nKey) {
                score_[dom.var()].setDom(nKey++);
                prios_.push_back(DomPrio());
                prios_.back().clear();
            }
            if (uint32_t k = addDomAction(dom, s, saved, lastW); k > dKey) {
                dKey = k;
            }
        }
        while (not saved.empty()) {
            const auto& [var, score]  = saved.back();
            score_[var].value        += score;
            score_[var].init          = 0;
            saved.pop_back();
        }
        if (not actions_.empty()) {
            actions_.back().next = 0;
        }
        if ((nKey - dKey) > dKey && s.sharedContext()->solveMode() == SharedContext::solve_once) {
            PrioVec(prios_.begin(), prios_.begin() + dKey).swap(prios_);
        }
        domSeen_ = domTab.size();
    }
    // apply default modification
    if (defMod_) {
        unsigned key = nKey + 1;
        DomainTable::applyDefault(
            *s.sharedContext(),
            [&](Literal p, HeuParams::DomPref pref, uint32_t b) {
                assert(std::in_range<int16_t>(b));
                addDefAction(s, p, static_cast<int16_t>(b ? b : 1), key + Potassco::log2(static_cast<unsigned>(pref)));
            },
            defPref_);
    }
}

uint32_t DomainHeuristic::addDomAction(const DomMod& e, Solver& s, VarScoreVec& initOut, Literal& lastW) {
    bool isStatic = not e.hasCondition() || s.topValue(e.cond().var()) == trueValue(e.cond());
    if (not isStatic && e.type() == DomModType::init) {
        return 0;
    }
    POTASSCO_ASSERT(e.comp() || +e.type() <= 3u, "Invalid dom modifier!");
    DomAction a = {e.var(), not e.comp() ? +e.type() : +DomModType::level, DomAction::undo_nil, 0u, e.bias(), e.prio()};
    DomScore& es = score_[a.var];
    for (uint32_t res = 0;;) {
        if (auto& sPrio = prio(a.var, a.mod); a.prio >= sPrio) {
            if (a.mod == DomModType::init && es.init == 0) {
                initOut.push_back({a.var, es.value});
                es.init = 1;
            }
            else if (a.mod == DomModType::sign && a.bias != 0) {
                a.bias = a.bias > 0 ? value_true : value_false;
            }
            if (isStatic) {
                applyAction(s, a, sPrio);
                es.sign |= static_cast<uint32_t>(a.mod == DomModType::sign);
            }
            else {
                if (e.cond() != lastW) {
                    s.addWatch(lastW = e.cond(), this, size32(actions_));
                }
                else {
                    actions_.back().next = 1;
                }
                actions_.push_back(a);
                res = es.domP + 1u;
            }
        }
        if (not e.comp() || a.mod == DomModType::sign) {
            return res;
        }
        POTASSCO_ASSERT(e.comp(), "Invalid dom modifier!");
        a.mod  = +DomModType::sign;
        a.bias = e.type() == DomModType::true_ ? 1 : -1;
        a.prio = e.prio();
    }
}

void DomainHeuristic::addDefAction(Solver& s, Literal x, int16_t lev, uint32_t domKey) {
    if (s.value(x.var()) != value_free || score_[x.var()].domP < domKey) {
        return;
    }
    const bool signMod = defMod_ < HeuParams::mod_init && ((defMod_ & HeuParams::mod_init) != 0);
    const bool valMod  = defMod_ >= HeuParams::mod_init || ((defMod_ & HeuParams::mod_level) != 0);
    DomScore&  xs      = score_[x.var()];
    if (xs.domP > domKey && lev && valMod) {
        if (defMod_ < HeuParams::mod_init) {
            auto nl  = xs.level + lev;
            xs.level = Clasp::saturate_cast<int16_t>(nl);
        }
        else if (defMod_ == HeuParams::mod_init) {
            xs.value += (lev * 100);
        }
        else if (defMod_ == HeuParams::mod_factor) {
            auto nf   = xs.factor + 1 + (lev > 3) + (lev > 15);
            xs.factor = Clasp::saturate_cast<int16_t>(nf);
        }
    }
    if (signMod) {
        auto oPref = s.pref(x.var()).get(ValueSet::user_value);
        auto nPref = (defMod_ & HeuParams::mod_spos) != 0 ? trueValue(x) : falseValue(x);
        if (oPref == value_free || (xs.sign == 1 && domKey != xs.domP)) {
            s.setPref(x.var(), ValueSet::user_value, nPref);
            xs.sign = 1;
        }
        else if (xs.sign == 1 && oPref != nPref) {
            s.setPref(x.var(), ValueSet::user_value, value_free);
            xs.sign = 0;
        }
    }
    if (x.var() > defMax_) {
        defMax_ = x.var();
    }
    xs.setDom(domKey);
}

Literal DomainHeuristic::doSelect(Solver& s) {
    Literal x = BaseType::doSelect(s);
    s.stats.addDomChoice(isDom(score_[x.var()]));
    return x;
}

Constraint::PropResult DomainHeuristic::propagate(Solver& s, Literal, uint32_t& aId) {
    uint32_t n  = aId;
    uint32_t dl = s.decisionLevel();
    do {
        DomAction& a    = actions_[n];
        uint16_t&  prio = this->prio(a.var, a.mod);
        if (s.value(a.var) == value_free && a.prio >= prio) {
            applyAction(s, a, prio);
            if (dl != frames_.back().dl) {
                s.addUndoWatch(dl, this);
                frames_.push_back(Frame(dl, DomAction::undo_nil));
            }
            pushUndo(frames_.back().head, n);
        }
    } while (actions_[n++].next);
    return PropResult(true, true);
}

void DomainHeuristic::applyAction(Solver& s, DomAction& a, uint16_t& gPrio) {
    std::swap(gPrio, a.prio);
    switch (static_cast<DomModType>(a.mod)) {
        default                : POTASSCO_ASSERT_NOT_REACHED("unexpected domain modification");
        case DomModType::init  : score_[a.var].value = a.bias; break;
        case DomModType::factor: std::swap(score_[a.var].factor, a.bias); break;
        case DomModType::level:
            std::swap(score_[a.var].level, a.bias);
            if (vars_.is_in_queue(a.var)) {
                vars_.update(a.var);
            }
            break;
        case DomModType::sign:
            auto old = s.pref(a.var).get(ValueSet::user_value);
            s.setPref(a.var, ValueSet::user_value, static_cast<Val_t>(a.bias));
            a.bias = old;
            break;
    }
}
void DomainHeuristic::pushUndo(uint32_t& head, uint32_t actionId) {
    actions_[actionId].undo = head;
    head                    = actionId;
}

void DomainHeuristic::undoLevel(Solver& s) {
    while (frames_.back().dl >= s.decisionLevel()) {
        for (uint32_t n = frames_.back().head; n != DomAction::undo_nil;) {
            DomAction& a = actions_[n];
            n            = a.undo;
            applyAction(s, a, prio(a.var, a.mod));
        }
        frames_.pop_back();
    }
}
} // namespace Clasp
