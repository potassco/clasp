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
#include <clasp/satelite.h>

#include <clasp/clause.h>

#include <potassco/error.h>

namespace Clasp {
/////////////////////////////////////////////////////////////////////////////////////////
// SatElite preprocessing
//
/////////////////////////////////////////////////////////////////////////////////////////
SatElite::SatElite() : elimHeap_(LessOccCost(occurs_)) {}

SatElite::~SatElite() { SatElite::doCleanUp(); }

void SatElite::reportProgress(Progress::EventOp id, uint32_t curr, uint32_t max) {
    ctx().report(Progress(this, id, curr, max));
}
void SatElite::resizeOcc(uint32_t ns) {
    if (ns > nOcc_) {
        auto gs = std::max(ns, saturate_cast<uint32_t>(static_cast<uint64_t>(nOcc_) * 3 / 2));
        assert(gs >= ns);
        auto occ = std::make_unique<OccurList[]>(gs);
        if (nOcc_ && occurs_) {
            std::move(occurs_.get(), occurs_.get() + nOcc_, occ.get());
            occurs_.reset();
        }
        occurs_ = std::move(occ);
        nOcc_   = gs;
    }
}
SatPreprocessor* SatElite::clone() { return new SatElite(); }

void SatElite::doCleanUp() {
    occurs_.reset();
    discardVec(resCands_);
    discardVec(occT_[occ_pos]);
    discardVec(occT_[occ_neg]);
    discardVec(resolvent_);
    queue_ = IdQueue();
    elimHeap_.clear();
    facts_ = 0;
}

SatPreprocessor::Clause* SatElite::popSubQueue() {
    if (Clause* c = clause(queue_.pop_ret())) {
        c->setInQ(false);
        return c;
    }
    return nullptr;
}

void SatElite::addToSubQueue(uint32_t clauseId) {
    POTASSCO_ASSERT(clause(clauseId) != nullptr);
    if (not clause(clauseId)->inQ()) {
        queue_.push(clauseId);
        clause(clauseId)->setInQ(true);
    }
}

void SatElite::attach(uint32_t clauseId, bool initialClause) {
    Clause& c       = *clause(clauseId);
    c.abstraction() = 0;
    assert(c.size() > 1);
#if SAT_ALGO == SAT_ALGO_FIX_2 || SAT_ALGO == SAT_ALGO_OCC_3 || SAT_ALGO == SAT_ALGO_FULL
    auto best = 0u;
    auto pos  = 0u;
#endif
    for (auto lit : c.lits()) {
        auto v = lit.var();
#if SAT_ALGO == SAT_ALGO_FIX_2 || SAT_ALGO == SAT_ALGO_OCC_3 || SAT_ALGO == SAT_ALGO_FULL
        if (occurs_[v].numOcc() < occurs_[c[best].var()].numOcc()) {
            best = pos;
        }
        ++pos;
#endif
        occurs_[v].add(clauseId, lit.sign());
        occurs_[v].unmark();
        c.abstraction() |= Clause::abstractLit(lit);
        if (elimHeap_.is_in_queue(v)) {
            elimHeap_.decrease(v);
        }
        else if (initialClause) {
            updateHeap(v);
        }
    }
#if SAT_ALGO == SAT_ALGO_FIX_2 || SAT_ALGO == SAT_ALGO_OCC_3 || SAT_ALGO == SAT_ALGO_FULL
    if (best != 0u) {
        std::swap(c[0], c[best]);
    }
#endif
#if SAT_ALGO == SAT_ALGO_OCC_3 || SAT_ALGO == SAT_ALGO_FULL
    assert(not occurs_[c[0].var()].refs.back().flagged());
    assert(occurs_[c[0].var()].refs.back().var() == clauseId);
    occurs_[c[0].var()].refs.back().flag();
#endif
    occurs_[c[0].var()].addWatch(clauseId);
    addToSubQueue(clauseId);
    stats.clAdded += not initialClause;
}

void SatElite::detach(uint32_t id) {
    Clause& c = *clause(id);
    occurs_[c[0].var()].removeWatch(id);
    for (auto lit : c.lits()) {
        auto v = lit.var();
        occurs_[v].remove(id, lit.sign(), false);
        updateHeap(v);
    }
    destroyClause(id);
}

void SatElite::bceVeRemove(uint32_t id, bool freeId, Var_t ev, bool blocked) {
    Clause& c = *clause(id);
    occurs_[c[0].var()].removeWatch(id);
    uint32_t rp = 0, n = 0;
    for (auto& lit : c.lits()) {
        if (auto v = lit.var(); v != ev) {
            occurs_[v].remove(id, lit.sign(), freeId);
            updateHeap(v);
        }
        else {
            occurs_[ev].remove(id, lit.sign(), false);
            rp = n;
        }
        ++n;
    }
    std::swap(c[0], c[rp]);
    c.setMarked(blocked);
    eliminateClause(id);
}

bool SatElite::initPreprocess(Options& opts) {
    reportProgress(Progress::event_algorithm, 0, 100);
    opts_ = opts;
    resizeOcc(ctx().numVars() + 1);
    occurs_[0].bce = (opts.type == Options::sat_pre_full);
    if (opts.bceLimit(numClauses())) {
        opts_.disableBce();
#if SAT_ALGO >= SAT_ALGO_OCC_1
        bce_.clear();
#else
        occurs_[0].refs.shrink_right(occurs_[0].refs.right_begin());
#endif
    }
    return true;
}
bool SatElite::doAttachClauses(Range32 clauseRange, bool propagate) {
    resizeOcc(ctx().numVars() + 1);
    if (clauseRange.lo == 0) {
        queue_.clear();
    }
    for (uint32_t i : irange(clauseRange.lo, clauseRange.hi)) { attach(i, true); }
    return not propagate || propagateFacts();
}
bool SatElite::doPreprocess() {
    // remove subsumed clauses, eliminate vars by clause distribution
    timeout_ = opts_.limTime ? time(nullptr) + opts_.limTime : std::numeric_limits<std::time_t>::max();
    for (uint32_t i = 0, end = opts_.limIters ? opts_.limIters : UINT32_MAX; queue_.size() + elimHeap_.size() > 0;
         ++i) {
        if (not backwardSubsume()) {
            return false;
        }
        if (timeout() || i == end) {
            break;
        }
        if (not eliminateVars()) {
            return false;
        }
    }
    reportProgress(Progress::event_algorithm, 100, 100);
    return true;
}

// (Destructive) unit propagation on clauses.
// Removes satisfied clauses and shortens clauses w.r.t. false literals.
// Pre: Assignment is propagated w.r.t other non-clause constraints
// Post: Assignment is fully propagated and no clause contains an assigned literal
bool SatElite::propagateFacts() {
    Solver* s = ctx().master();
    assert(s->queueSize() == 0);
    while (facts_ != s->numAssignedVars()) {
        Literal    l  = s->trailLit(facts_++);
        OccurList& ov = occurs_[l.var()];
        for (auto x : ov.clauseRange()) {
            if (clause(x.var())) {
                if (x.sign() == l.sign()) {
                    detach(x.var());
                }
                else if (not strengthenClause(x.var(), ~l)) {
                    return false;
                }
            }
        }
        ov.clear();
        ov.mark(not l.sign());
    }
    assert(s->queueSize() == 0);
    return true;
}

// Backward subsumption and self-subsumption resolution until fixpoint
bool SatElite::backwardSubsume() {
    if (not propagateFacts()) {
        return false;
    }
    while (not queue_.empty()) {
        if (auto qf = toU32(queue_.qFront); (qf & 8191) == 0) {
            if (timeout()) {
                break;
            }
            if (auto max = size32(queue_.vec); max > 1000) {
                reportProgress(Progress::event_subsumption, qf, max);
            }
        }
        Clause* c = popSubQueue();
        if (c == nullptr) {
            continue;
        }
        // Try to minimize effort by testing against the var in c that occurs least often;
        Literal best = *std::ranges::min_element(c->lits(), [&](Literal lhs, Literal rhs) {
            return occurs_[lhs.var()].numOcc() < occurs_[rhs.var()].numOcc();
        });
        // Test against all clauses containing best
        auto&    cls = occurs_[best.var()];
        Literal  res;
        uint32_t j = 0;
        // must use index access because cls might change!
        for (uint32_t i : irange(cls.left_size())) {
            Literal  cl      = cls.left(i);
            uint32_t otherId = cl.var();
            Clause*  other   = clause(otherId);
            if (other && other != c &&
                (res = subsumes(*c, *other, best.sign() == cl.sign() ? lit_true : best)) != lit_false) {
                if (res == lit_true) {
                    // other is subsumed - remove it
                    detach(otherId);
                    other = nullptr;
                }
                else {
                    // self-subsumption resolution; other is subsumed by c\{res} U {~res}
                    // remove ~res from other, add it to subQ so that we can check if it now subsumes c
                    res = ~res;
                    occurs_[res.var()].remove(otherId, res.sign(), res.var() != best.var());
                    updateHeap(res.var());
                    if (not strengthenClause(otherId, res)) {
                        return false;
                    }
                    if (res.var() == best.var() || not clause(otherId)) {
                        other = nullptr;
                    }
                }
            }
            if (other && j++ != i) {
                cls.left(j - 1) = cl;
            }
        }
        cls.shrink_left(j);
        occurs_[best.var()].dirty = 0;
        assert(occurs_[best.var()].numOcc() == toU32(cls.left_size()));
        if (not propagateFacts()) {
            return false;
        }
    }
    queue_.clear();
    return true;
}

// checks if 'c' subsumes 'other', and at the same time, if it can be used to
// simplify 'other' by subsumption resolution.
// Return:
//  - lit_false - No subsumption or simplification
//  - lit_true - 'c' subsumes 'other'
//  - l         - The literal l can be deleted from 'other'
Literal SatElite::subsumes(const Clause& c, const Clause& other, Literal res) const {
    if (other.size() < c.size() || (c.abstraction() & ~other.abstraction()) != 0) {
        return lit_false;
    }
    auto otherLits = other.lits();
    if (c.size() < 10 || other.size() < 10) {
        for (auto lhs : c.lits()) {
            auto oIt = std::ranges::find_if(otherLits, [v = lhs.var()](Literal x) { return x.var() == v; });
            if (oIt != otherLits.end()) {
                if (lhs.sign() == oIt->sign()) {
                    continue;
                }
                if (res == lit_true || res == lhs) {
                    res = lhs;
                    continue;
                }
            }
            return lit_false;
        }
    }
    else {
        markAll(otherLits);
        for (auto lit : c.lits()) {
            if (occurs_[lit.var()].litMark == 0) {
                res = lit_false;
                break;
            }
            if (occurs_[lit.var()].marked(not lit.sign())) {
                if (res != lit_true && res != lit) {
                    res = lit_false;
                    break;
                }
                res = lit;
            }
        }
        unmarkAll(otherLits);
    }
    return res;
}
#if SAT_ALGO == SAT_ALGO_BASE
uint32_t SatElite::findUnmarkedLit(const Clause& c, uint32_t x) const {
    while (x != c.size() && occurs_[c[x].var()].marked(c[x].sign())) { ++x; }
    return x;
}

// checks if 'cl' is subsumed by one of the existing clauses and at the same time
// strengthens 'cl' if possible.
// Return:
//  - true  - 'cl' is subsumed
//  - false - 'cl' is not subsumed but may itself subsume other clauses
// Pre: All literals of l are marked, i.e.
// for each literal l in cl, occurs_[l.var()].marked(l.sign()) == true
bool SatElite::subsumed(LitVec& cl) {
    auto str = 0u;
    auto j   = 0u;
    for (auto i : irange(cl)) {
        Literal l = cl[i];
        if (occurs_[l.var()].litMark == 0) {
            --str;
            continue;
        }
        ClWList& cls = occurs_[l.var()].refs; // right: all clauses watching either l or ~l
        WIter    wj  = cls.right_begin();
        for (WIter w = wj, end = cls.right_end(); w != end; ++w) {
            Clause& c = *clause(*w);
            if (c[0] == l) {
                auto x = findUnmarkedLit(c, 1);
                if (x == c.size()) {
                    while (w != end) { *wj++ = *w++; }
                    cls.shrink_right(wj);
                    return true;
                }
                c[0] = c[x];
                c[x] = l;
                occurs_[c[0].var()].addWatch(*w);
                if (occurs_[c[0].var()].litMark != 0 && findUnmarkedLit(c, x + 1) == c.size()) {
                    occurs_[c[0].var()].unmark(); // no longer part of cl
                    ++str;
                }
            }
            else if (findUnmarkedLit(c, 1) == c.size()) {
                occurs_[l.var()].unmark(); // no longer part of cl
                while (w != end) { *wj++ = *w++; }
                cls.shrink_right(wj);
                goto removeLit;
            }
            else {
                *wj++ = *w;
            }
        }
        cls.shrink_right(wj);
        if (j++ != i) {
            cl[j - 1] = cl[i];
        }
    removeLit:;
    }
    shrinkVecTo(cl, j);
    if (str > 0) {
        auto it = cl.begin();
        do {
            it = std::find_if(it, cl.end(), [&](Literal x) { return occurs_[x.var()].litMark == 0; });
            POTASSCO_ASSERT(it != cl.end());
            *it = cl.back();
            cl.pop_back();
        } while (--str);
    }
    return false;
}
#elif SAT_ALGO == SAT_ALGO_FIX_1 || SAT_ALGO == SAT_ALGO_FIX_2
bool SatElite::subsumed(LitVec& cl) {
    auto clSize = cl.size();
    for (auto l : cl) {
        if (occurs_[l.var()].litMark == 0) {
            continue;
        }
        for (auto clId : occurs_[l.var()].refs.right_view()) {
            if (Clause& c = *clause(clId); c.size() <= clSize) {
                auto str = lit_true;
                for (auto x : c.lits()) {
                    if (not occurs_[x.var()].marked(x.sign())) {
                        if (occurs_[x.var()].litMark == 0 || str != lit_true) {
                            str = lit_false;
                            break;
                        }
                        str = ~x;
                    }
                }
                if (str != lit_false) {
                    if (str == lit_true) {
                        return true;
                    }
                    POTASSCO_DEBUG_ASSERT(occurs_[str.var()].marked(str.sign()));
                    occurs_[str.var()].unmark();
                    --clSize;
                    if (str == l) {
                        break;
                    }
                }
            }
        }
    }
    if (auto diff = cl.size() - clSize; diff > 0) {
        [[maybe_unused]] auto rem = erase_if(cl, [&](Literal x) { return occurs_[x.var()].litMark == 0; });
        POTASSCO_DEBUG_ASSERT(rem == diff);
    }
    return false;
}
#elif SAT_ALGO == SAT_ALGO_DYN_1 || SAT_ALGO == SAT_ALGO_DYN_2
bool SatElite::subsumed(LitVec& cl) {
    auto clSize = cl.size();
    for (auto l : cl) {
        if (occurs_[l.var()].litMark == 0) {
            continue;
        }
        auto& refs = occurs_[l.var()].refs;
        auto  wOut = refs.right_begin();
        for (auto w = wOut, wEnd = refs.right_end(); w != wEnd;) {
            auto clId   = *w++;
            *wOut++     = clId; // keep clause in the occur-list
            Clause& c   = *clause(clId);
            auto    str = lit_true;
            for (auto pos : irange(c)) {
                if (auto& x = c[pos]; not occurs_[x.var()].marked(x.sign())) {
                    if (occurs_[x.var()].litMark == 0 || str != lit_true) {
                        str = lit_false;
                        if (SAT_ALGO == SAT_ALGO_DYN_1 || occurs_[x.var()].numOcc() < occurs_[l.var()].numOcc()) {
                            occurs_[x.var()].addWatch(clId);
                            std::swap(c[0], x);
                            --wOut; // remove clause from the occur-list
                        }
                        break;
                    }
                    str = ~x;
                }
            }
            if (str != lit_false) {
                if (str == lit_true) {
                    // copy remaining
                    while (w != wEnd) { *wOut++ = *w++; }
                    refs.shrink_right(wOut);
                    return true;
                }
                POTASSCO_DEBUG_ASSERT(occurs_[str.var()].marked(str.sign()));
                occurs_[str.var()].unmark();
                --clSize;
                if (str == l) {
                    break;
                }
            }
        }
        refs.shrink_right(wOut);
    }
    if (auto diff = cl.size() - clSize; diff > 0) {
        [[maybe_unused]] auto rem = erase_if(cl, [&](Literal x) { return occurs_[x.var()].litMark == 0; });
        POTASSCO_DEBUG_ASSERT(rem == diff);
    }
    return false;
}
#elif SAT_ALGO < SAT_ALGO_NO_FWD
auto SatElite::checkSubsumed(Literal ref, [[maybe_unused]] Literal l, uint32_t sz) const -> const Clause* {
    if constexpr (SAT_ALGO == SAT_ALGO_OCC_3) {
        if (not ref.flagged()) {
            return nullptr;
        }
    }
    auto* c = clause(ref.var());
    if constexpr (SAT_ALGO == SAT_ALGO_OCC_2) {
        return c && not Potassco::test_bit(reinterpret_cast<uintptr_t>(c), 0) && c->size() <= sz ? c : nullptr;
    }
    if constexpr (SAT_ALGO == SAT_ALGO_OCC_1) {
        return c && c->size() <= sz && (*c)[0].var() == l.var() ? c : nullptr;
    }
    return c && c->size() <= sz ? c : nullptr;
}

bool SatElite::subsumed(LitVec& cl) {
    auto clSize = cl.size();
#if SAT_ALGO == SAT_ALGO_OCC_2
    POTASSCO_SCOPE_EXIT({
        while (not seen_.empty()) {
            Potassco::store_clear_bit(reinterpret_cast<uintptr_t&>(clauses_[seen_.back()]), 0);
            seen_.pop_back();
        }
    });
#endif
    for (auto l : cl) {
        if (occurs_[l.var()].litMark == 0) {
            continue;
        }
        for (auto ref : occurs_[l.var()].refs) {
            if (auto* c = checkSubsumed(ref, l, clSize)) {
#if SAT_ALGO == SAT_ALGO_OCC_2
                Potassco::store_set_bit(reinterpret_cast<uintptr_t&>(clauses_[ref.var()]), 0);
                seen_.push_back(ref.var());
#endif
                auto lits = c->lits();
                auto str  = lit_true;
                if (l == ~lits[0]) {
                    str  = l;
                    lits = lits.subspan(1);
                }
                for (auto x : lits) {
                    if (not occurs_[x.var()].marked(x.sign())) {
                        if (occurs_[x.var()].litMark == 0 || str != lit_true) {
                            str = lit_false;
                            break;
                        }
                        str = ~x;
                    }
                }
                if (str != lit_false) {
                    if (str == lit_true) {
                        return true;
                    }
                    POTASSCO_DEBUG_ASSERT(occurs_[str.var()].marked(str.sign()));
                    occurs_[str.var()].unmark();
                    --clSize;
                    if (str == l) {
                        break;
                    }
                }
            }
        }
    }
    if (auto diff = cl.size() - clSize; diff > 0) {
        [[maybe_unused]] auto rem = erase_if(cl, [&](Literal x) { return occurs_[x.var()].litMark == 0; });
        POTASSCO_DEBUG_ASSERT(rem == diff);
    }
    return false;
}
#elif SAT_ALGO == SAT_ALGO_NO_FWD
bool SatElite::subsumed(LitVec& cl) {
    for (auto l : cl) {
        if (not std::exchange(occurs_[l.var()].touched, true)) {
            touched_.push_back(l.var());
        }
    }
    return false;
}
#else
bool SatElite::subsumed(LitVec& cl) {
    auto clSize = cl.size();
    refs_.clear();
    // Step 1: check if cl is subsumed by an existing clause
    for (auto l : cl) {
        for (auto ref : occurs_[l.var()].refs) {
            if (not ref.flagged() || not clause(ref.var())) {
                continue;
            }
            if (auto* c = clause(ref.var()); c->size() <= clSize) {
                if (l == (*c)[0]) {
                    auto lits = c->lits();
                    auto it =
                        std::ranges::find_if(lits, [&](Literal x) { return not occurs_[x.var()].marked(x.sign()); });
                    if (it == lits.end()) {
                        return true;
                    }
                    if (occurs_[it->var()].litMark != 0) {
                        auto str = ~*it;
                        if (std::ranges::all_of(it + 1, lits.end(),
                                                [&](Literal x) { return occurs_[x.var()].marked(x.sign()); })) {
                            assert(not str.flagged() && occurs_[str.var()].marked(str.sign()));
                            refs_.push_back(str);
                        }
                    }
                }
                else {
                    refs_.push_back(ref);
                }
            }
        }
    }
    // Step 2: check if cl can be strengthened by an existing clause
    for (auto r : refs_) {
        if (r.flagged()) {
            auto& c = *clause(r.var());
            if (c.size() <= clSize) {
                auto lits = c.lits();
                auto str  = lit_true;
                for (auto x : lits) {
                    if (not occurs_[x.var()].marked(x.sign())) {
                        if (occurs_[x.var()].litMark == 0 || str != lit_true) {
                            str = lit_false;
                            break;
                        }
                        str = ~x;
                    }
                }
                if (str != lit_false) {
                    POTASSCO_DEBUG_ASSERT(occurs_[str.var()].marked(str.sign()));
                    occurs_[str.var()].unmark();
                    --clSize;
                }
            }
        }
        else if (occurs_[r.var()].marked(r.sign())) {
            occurs_[r.var()].unmark();
            --clSize;
        }
    }
    if (auto diff = cl.size() - clSize; diff > 0) {
        [[maybe_unused]] auto rem = erase_if(cl, [&](Literal x) { return occurs_[x.var()].litMark == 0; });
        POTASSCO_DEBUG_ASSERT(rem == diff);
    }
    return false;
}
#endif

// Pre: c contains l
// Pre: c was already removed from l's occur-list
bool SatElite::strengthenClause(uint32_t clauseId, Literal l) {
    Clause& c   = *clause(clauseId);
    bool    upW = false;
    if (c[0] == l) {
        occurs_[c[0].var()].removeWatch(clauseId);
        upW = true;
    }
    ++stats.litsRemoved;
    c.strengthen(l);
    if (c.size() == 1) {
        Literal unit = c[0];
        detach(clauseId);
        return ctx().addUnary(unit) && ctx().master()->propagate();
    }
    if (upW) {
        // Note: Clause::strengthen shifts literals after l to the left. Thus,
        // c[1] will be c[0] after strengthen
        occurs_[c[0].var()].addWatch(clauseId);
#if SAT_ALGO == SAT_ALGO_OCC_3 || SAT_ALGO == SAT_ALGO_FULL
        auto it = std::ranges::find(occurs_[c[0].var()].refs, Literal(clauseId, c[0].sign()));
        assert(it != occurs_[c[0].var()].refs.end() && not it->flagged());
        it->flag();
#endif
    }
    addToSubQueue(clauseId);
    return true;
}

// Split occurrences of v into pos and neg and
// mark all clauses containing v
SatElite::ClRange SatElite::splitOcc(Var_t v, bool mark) {
    ClRange cls      = occurs_[v].clauseRange();
    occurs_[v].dirty = 0;
    occT_[occ_pos].clear();
    occT_[occ_neg].clear();
    auto j = cls.data();
    for (auto x : cls) {
        if (Clause* c = clause(x.var())) {
            assert(c->marked() == false);
            c->setMarked(mark);
            int sign = x.sign();
            occT_[sign].push_back(x.var());
            *j++ = x;
        }
    }
#if SAT_ALGO < SAT_ALGO_OCC_1
    occurs_[v].refs.shrink_left(j);
#else
    occurs_[v].refs.erase(j, occurs_[v].refs.end());
#endif
    return occurs_[v].clauseRange();
}

void SatElite::markAll(LitView lits) const {
    for (auto lit : lits) { occurs_[lit.var()].mark(lit.sign()); }
}
void SatElite::unmarkAll(LitView lits) const {
    for (auto lit : lits) { occurs_[lit.var()].unmark(); }
}

// Run variable and/or blocked clause elimination on var v.
// If the number of non-trivial resolvents is <= maxCnt,
// v is eliminated by clause distribution. If bce is enabled,
// clauses blocked on a literal of v are removed.
bool SatElite::bceVe(Var_t v, uint32_t maxCnt) {
    Solver* s = ctx().master();
    if (s->value(v) != value_free) {
        return true;
    }
    assert(allowElim(v));
    resCands_.clear();
    // distribute clauses on v
    // check if the number of clauses decreases if we eliminate v
    uint32_t bce     = opts_.bce();
    ClRange  cls     = splitOcc(v, bce > 1);
    uint32_t cnt     = 0;
    uint32_t markMax = size32(occT_[occ_neg]) * (bce > 1);
    uint32_t blocked = 0;
    bool     stop    = false;
    for (auto pId : occT_[occ_pos]) {
        auto* lhs = clause(pId);
        markAll(lhs->lits());
        lhs->setMarked(bce != 0);
        for (auto nId : occT_[occ_neg]) {
            if (auto* rhs = clause(nId); not trivialResolvent(*rhs, v)) {
                markMax -= rhs->marked();
                rhs->setMarked(false); // not blocked on v
                lhs->setMarked(false); // not blocked on v
                if (++cnt <= maxCnt) {
                    resCands_.push_back(lhs);
                    resCands_.push_back(rhs);
                }
                else if (not markMax) {
                    stop = (bce == 0);
                    break;
                }
            }
        }
        unmarkAll(lhs->lits());
        if (lhs->marked()) {
            occT_[occ_pos][blocked++] = pId;
        }
        if (stop) {
            break;
        }
    }
    if (cnt <= maxCnt) {
        // eliminate v by clause distribution
        ctx().eliminate(v); // mark var as eliminated
        // remove old clauses, store them in the elimination table so that
        // (partial) models can be extended.
        for (auto x : cls) {
            // reuse first cnt ids for resolvents
            if (clause(x.var())) {
                bool freeId = (cnt && cnt--);
                bceVeRemove(x.var(), freeId, v, false);
            }
        }
        // add non trivial resolvents
        assert(resCands_.size() % 2 == 0);
        auto it = cls.begin();
        for (auto i = 0u; i != size32(resCands_); i += 2, ++it) {
            if (not addResolvent(it->var(), *resCands_[i], *resCands_[i + 1])) {
                return false;
            }
        }
        assert(occurs_[v].numOcc() == 0);
        // release memory
        occurs_[v].clear();
    }
    else if ((blocked + markMax) > 0) {
        // remove blocked clauses
        for (auto id : std::span(occT_[occ_pos].data(), blocked)) { bceVeRemove(id, false, v, true); }
        for (auto it = occT_[occ_neg].data(); markMax; ++it) {
            if (clause(*it)->marked()) {
                bceVeRemove(*it, false, v, true);
                --markMax;
            }
        }
    }
    return opts_.limIters != 0 || backwardSubsume();
}

bool SatElite::bce() {
    uint32_t ops = 0;
#if SAT_ALGO < SAT_ALGO_OCC_1
    for (ClWList& bce = occurs_[0].refs; bce.right_size() != 0; ++ops) {
        Var_t v = *(bce.right_end() - 1);
        bce.pop_right();
#else
    for (auto& bce = bce_; not bce.empty();) {
        auto v = bce.back();
        bce.pop_back();
#endif
        occurs_[v].bce = 0;
        if ((ops & 1023) == 0) {
            if (timeout()) {
                bce.clear();
                return true;
            }
            if ((ops & 8191) == 0) {
                reportProgress(Progress::event_bce, ops, 1 + bce.size());
            }
        }
        if (not cutoff(v) && not bceVe(v, 0)) {
            return false;
        }
    }
    return true;
}

bool SatElite::eliminateVars() {
    if (not bce()) {
        return false;
    }
    const auto bceOnly = opts_.veLimit(numClauses());
    if (bceOnly && opts_.bce() != 1) {
        elimHeap_.clear();
        return true;
    }
    for (uint32_t ops = 0; not elimHeap_.empty(); ++ops) {
        auto v = elimHeap_.top();
        elimHeap_.pop();
        auto occ = not bceOnly ? occurs_[v].numOcc() : 0;
        if ((ops & 1023) == 0) {
            if (timeout()) {
                elimHeap_.clear();
                return true;
            }
            if ((ops & 8191) == 0) {
                reportProgress(Progress::event_var_elim, ops, 1 + size32(elimHeap_));
            }
        }
        if (not cutoff(v) && not bceVe(v, occ)) {
            return false;
        }
    }
#if SAT_ALGO == SAT_ALGO_NO_FWD
    for (auto v : touched_) {
        for (auto id : occurs_[v].refs) {
            if (auto clId = id.var(); clause(clId)) {
                addToSubQueue(clId);
            }
        }
        occurs_[v].touched = false;
    }
    touched_.clear();
#endif
    return opts_.limIters != 0 || bce();
}

// returns true if the result of resolving c1 (implicitly given) and c2 on v yields a tautologous clause
bool SatElite::trivialResolvent(const Clause& c2, Var_t v) const {
    return std::ranges::any_of(c2.lits(),
                               [&](Literal x) { return occurs_[x.var()].marked(not x.sign()) && x.var() != v; });
}

// Pre: lhs and rhs can be resolved on lhs[0].var()
// Pre: trivialResolvent(lhs, rhs, lhs[0].var()) == false
bool SatElite::addResolvent(uint32_t id, const Clause& lhs, const Clause& rhs) {
    resolvent_.clear();
    Solver* s = ctx().master();
    assert(lhs[0] == ~rhs[0]);
    uint32_t i, end;
    Literal  l;
    for (i = 1, end = lhs.size(); i != end; ++i) {
        l = lhs[i];
        if (not s->isFalse(l)) {
            if (s->isTrue(l)) {
                goto unmark;
            }
            occurs_[l.var()].mark(l.sign());
            resolvent_.push_back(l);
        }
    }
    for (i = 1, end = rhs.size(); i != end; ++i) {
        l = rhs[i];
        if (not s->isFalse(l) && not occurs_[l.var()].marked(l.sign())) {
            if (s->isTrue(l)) {
                goto unmark;
            }
            occurs_[l.var()].mark(l.sign());
            resolvent_.push_back(l);
        }
    }
    if (not subsumed(resolvent_)) {
        if (resolvent_.empty()) {
            return s->force(negLit(0));
        }
        if (resolvent_.size() == 1) {
            occurs_[resolvent_[0].var()].unmark();
            return s->force(resolvent_[0]) && s->propagate() && propagateFacts();
        }
        setClause(id, resolvent_);
        attach(id, false);
        return true;
    }
unmark:
    if (not resolvent_.empty()) {
        unmarkAll(resolvent_);
    }
    return true;
}

// extends the model given in assign by the vars that were eliminated
void SatElite::doExtendModel(Clause* top, ValueVec& m, LitVec& unconstr) {
    if (not top) {
        return;
    }
    constexpr auto value_eliminated = static_cast<Val_t>(4u);
    // compute values of eliminated vars / blocked literals by "unit propagating"
    // eliminated/blocked clauses in reverse order
    uint32_t uv = 0;
    uint32_t us = size32(unconstr);
    Clause*  r  = top;
    do {
        Literal x     = (*r)[0];
        auto    last  = x.var();
        bool    check = true;
        if (not r->marked()) {
            // eliminated var - compute the implied value
            m[last] = value_eliminated;
        }
        if (uv != us && unconstr[uv].var() == last) {
            // last is unconstrained w.r.t the current model -
            // set remembered value
            check   = false;
            m[last] = trueValue(unconstr[uv]);
            ++uv;
        }
        do {
            Clause& c = *r;
            if (m[x.var()] != trueValue(x) && check) {
                for (uint32_t i = 1, end = c.size(); i != end; ++i) {
                    auto vi = static_cast<Val_t>(m[c[i].var()] & 3u);
                    if (vi != falseValue(c[i])) {
                        x = c[i];
                        break;
                    }
                }
                if (x == c[0]) {
                    // all lits != x are false
                    // clause is unit or conflicting
                    assert(c.marked() || m[x.var()] != falseValue(x));
                    m[x.var()] = trueValue(x);
                    check      = false;
                }
            }
            r = r->next();
        } while (r && (x = (*r)[0]).var() == last);
        if (m[last] == value_eliminated) {
            // last seems unconstrained w.r.t the model
            m[last] |= value_true;
            unconstr.push_back(posLit(last));
        }
    } while (r);
    // check whether newly added unconstrained vars are really unconstrained w.r.t the model
    // or if they are implied by some blocked clause.
    auto j = unconstr.begin() + us;
    for (auto x : drop(unconstr, us)) {
        if (Potassco::test_any(m[x.var()], value_eliminated)) {
            // var is unconstrained - assign to true and remember it
            // so that we can later enumerate the model containing ~var
            m[x.var()] = value_true;
            *j++       = x;
        }
    }
    unconstr.erase(j, unconstr.end());
}
SatPreprocessor* SatPreParams::create(const SatPreParams& opts) {
    if (opts.type != 0) {
        return new SatElite();
    }
    return nullptr;
}
bool SatPreParams::frozenLimit(const SharedContext& ctx) const {
    if (double limit = limFrozen; limit != 0 && ctx.stats().vars.frozen) {
        auto assignedFrozen = static_cast<uint32_t>(std::ranges::count_if(
            ctx.master()->trailView(), [&](Literal lit) { return ctx.varInfo(lit.var()).frozen(); }));
        return percent(ctx.stats().vars.frozen - assignedFrozen, ctx.master()->numFreeVars()) > limit;
    }
    return false;
}

} // namespace Clasp
