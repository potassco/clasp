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
//! \file
//! \brief Types and functions for SAT-based preprocessing.
#pragma once

#include <clasp/solver.h>
#include <clasp/util/indexed_priority_queue.h>
#include <ctime>

namespace Clasp {
//! SatElite preprocessor for clauses.
/*!
 * \ingroup shared
 * The preprocessor implements subsumption, self-subsumption, variable elimination,
 * and (optionally) blocked clause elimination.
 * \see
 *   - Niklas Eén, Armin Biere: "Effective Preprocessing in SAT through Variable and Clause Elimination"
 *   - Matti Järvisalo, Armin Biere, Marijn Heule: "Blocked Clause Elimination"
 *   - Parts of the SatElite preprocessor are adapted from MiniSAT 2.0 beta
 *     available under the MIT licence from http://minisat.se/MiniSat.html
 *
 */
class SatElite : public SatPreprocessor {
public:
    SatElite();
    ~SatElite() override;
    SatElite(SatElite&&) = delete;
    auto clone() -> SatPreprocessor* override;

    static constexpr auto event_bce         = static_cast<Progress::EventOp>('B');
    static constexpr auto event_var_elim    = static_cast<Progress::EventOp>('E');
    static constexpr auto event_subsumption = static_cast<Progress::EventOp>('S');

protected:
    bool initPreprocess(Options& opts) override;
    bool doPreprocess() override;
    bool doAttachClauses(Range32 clauseRange, bool propagate) override;
    void doExtendModel(Clause* top, ValueVec& m, LitVec& open) override;
    void doCleanUp() override;

private:
    using ClWList = bk_lib::left_right_sequence<Literal, Var_t, 0>;
    using ClIter  = ClWList::left_iterator;
    using WIter   = ClWList::right_iterator;
    using ClRange = std::span<Literal>;
    using IdQueue = VecQueue<uint32_t>;
    // For each var v
    struct OccurList {
        [[nodiscard]] auto numOcc() const -> uint32_t { return pos + neg; }
        [[nodiscard]] auto cost() const -> uint32_t { return saturating_mul<uint32_t>(pos, neg); }
        [[nodiscard]] auto clauseRange() const -> ClRange {
            return {const_cast<ClWList&>(refs).left_begin(), refs.left_size()};
        }
        void clear() {
            this->~OccurList();
            new (this) OccurList();
        }
        void addWatch(uint32_t clId) { refs.push_right(clId); }
        void removeWatch(uint32_t clId) { refs.erase_right(std::find(refs.right_begin(), refs.right_end(), clId)); }
        void add(uint32_t id, bool sign) {
            pos += static_cast<uint32_t>(not sign);
            neg += static_cast<uint32_t>(sign);
            refs.push_left(Literal(id, sign));
        }
        void remove(uint32_t id, bool sign, bool updateClauseList) {
            pos -= static_cast<uint32_t>(not sign);
            neg -= static_cast<uint32_t>(sign);
            if (updateClauseList) {
                refs.erase_left(std::find(refs.left_begin(), refs.left_end(), Literal(id, sign)));
            }
            else {
                dirty = 1;
            }
        }
        // note: only one literal of v shall be marked at a time
        static constexpr auto mask(bool s) -> uint32_t { return 1u + s; }
        [[nodiscard]] bool    marked(bool sign) const { return Potassco::test_any(litMark, mask(sign)); }
        void                  mark(bool sign) { litMark = mask(sign); }
        void                  unmark() { litMark = 0; }

        ClWList refs;              // left : ids of clauses containing v or ~v  (var() == id, sign() == v or ~v)
                                   // right: ids of clauses watching v or ~v (literal 0 is the watched literal)
        uint32_t pos     : 30 = 0; // number of *relevant* clauses containing v
        uint32_t bce     : 1  = 0; // in BCE queue?
        uint32_t dirty   : 1  = 0; // does clauses contain removed clauses?
        uint32_t neg     : 30 = 0; // number of *relevant* clauses containing v
        uint32_t litMark : 2  = 0; // 00: no literal of v marked, 01: v marked, 10: ~v marked
    };
    using OccurLists = std::unique_ptr<OccurList[]>;
    struct LessOccCost {
        explicit LessOccCost(OccurLists& occ) : occ_(occ) {}
        bool operator()(Var_t v1, Var_t v2) const { return occ_[v1].cost() < occ_[v2].cost(); }

    private:
        OccurLists& occ_;
    };
    using ElimHeap = bk_lib::indexed_priority_queue<Var_t, LessOccCost, Potassco::DynamicArray>;
    [[nodiscard]] auto allowElim(Var_t v) const -> bool {
        return not ctx().varInfo(v).frozen() && not ctx().eliminated(v);
    }
    [[nodiscard]] auto findUnmarkedLit(const Clause& c, uint32_t x) const -> uint32_t;
    [[nodiscard]] auto subsumes(const Clause& c, const Clause& other, Literal res) const -> Literal;
    [[nodiscard]] bool trivialResolvent(const Clause& c2, Var_t v) const;
    [[nodiscard]] bool timeout() const { return time(nullptr) > timeout_; }
    [[nodiscard]] bool cutoff(Var_t v) const {
        return opts_->occLimit(occurs_[v].pos, occurs_[v].neg) || (occurs_[v].cost() == 0 && ctx().preserveModels());
    }
    void updateHeap(Var_t v) {
        if (allowElim(v)) {
            elimHeap_.update(v);
            if (occurs_[v].bce == 0 && occurs_[0].bce != 0) {
                occurs_[0].addWatch(v);
                occurs_[v].bce = 1;
            }
        }
    }
    auto popSubQueue() -> Clause*;
    void addToSubQueue(uint32_t clauseId);
    void attach(uint32_t cId, bool initialClause);
    void detach(uint32_t cId);
    void bceVeRemove(uint32_t cId, bool freeId, Var_t v, bool blocked);
    bool propagateFacts();
    bool backwardSubsume();
    bool strengthenClause(uint32_t clauseId, Literal p);
    bool subsumed(LitVec& cl);
    bool eliminateVars();
    bool bce();
    bool bceVe(Var_t v, uint32_t maxCnt);
    void resizeOcc(uint32_t ns);
    auto splitOcc(Var_t v, bool mark) -> ClRange;
    void markAll(LitView lits) const;
    void unmarkAll(LitView lits) const;
    bool addResolvent(uint32_t newId, const Clause& c1, const Clause& c2);

    enum OccSign { occ_pos = 0, occ_neg = 1 };
    OccurLists     occurs_;    // occur list for each variable
    ElimHeap       elimHeap_;  // candidates for variable elimination; ordered by increasing occurrence-cost
    VarVec         occT_[2];   // temporary clause lists used in eliminateVar
    ClauseVec      resCands_;  // pairs of clauses to be resolved
    LitVec         resolvent_; // temporary, used in addResolvent
    IdQueue        queue_;     // indices of clauses waiting for subsumption-check
    const Options* opts_;      // active options
    uint32_t       facts_{0};  // [facts_, solver.trail.size()): new top-level facts
    uint32_t       nOcc_{0};   // size of occurs_ (number of variables)
    std::time_t    timeout_{}; // stop once time > timeout_
};
} // namespace Clasp
