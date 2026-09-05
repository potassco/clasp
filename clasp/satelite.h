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
    struct TimeoutError : std::exception {};
    static constexpr auto pos_bit     = 0u;
    static constexpr auto neg_bit     = 1u;
    static constexpr auto bce_bit     = 2u;
    static constexpr auto marked_mask = 3u;
    enum OccSign { occ_pos = 0, occ_neg = 1 };
    using ClRange     = std::span<Literal>;
    using IdQueue     = VecQueue<uint32_t>;
    using OccCount    = std::array<uint32_t, 2u>;
    using OccurLists  = std::unique_ptr<LitVec[]>;
    using WatchLists  = std::unique_ptr<VarVec[]>;
    using OccurCounts = std::unique_ptr<OccCount[]>;
    using VarStates   = std::unique_ptr<uint8_t[]>;

    [[nodiscard]] static constexpr auto numOcc(const OccCount& occ) -> uint32_t { return occ[occ_pos] + occ[occ_neg]; }
    [[nodiscard]] static constexpr auto cost(const OccCount& occ) -> uint32_t {
        return saturating_mul<uint32_t>(occ[occ_pos], occ[occ_neg]);
    }
    [[nodiscard]] static constexpr uint8_t mask(Literal l) { return 1u + l.sign(); }
    struct LessOccCost {
        explicit LessOccCost(OccurCounts& st) : counts_(st) {}
        bool operator()(Var_t v1, Var_t v2) const { return cost(counts_[v1]) < cost(counts_[v2]); }

    private:
        OccurCounts& counts_;
    };
    using ElimHeap = bk_lib::indexed_priority_queue<Var_t, LessOccCost, Vector_t>;
    [[nodiscard]] auto numOcc(Var_t v) const -> uint32_t { return numOcc(counts_[v]); }
    [[nodiscard]] auto allowElim(Var_t v) const -> bool {
        return not ctx().varInfo(v).frozen() && not ctx().eliminated(v);
    }
    [[nodiscard]] auto findUnmarkedLit(const Clause& c, uint32_t x) const -> uint32_t;
    [[nodiscard]] auto subsumes(const Clause& c, const Clause& other, Literal res, bool& markedC) const -> Literal;
    [[nodiscard]] bool trivialResolvent(const Clause& c2, Var_t v) const;
    [[nodiscard]] bool cutoff(Var_t v) const {
        return opts_->occLimit(counts_[v][occ_pos], counts_[v][occ_neg]) ||
               (cost(counts_[v]) == 0 && ctx().preserveModels());
    }

    [[nodiscard]] auto marked(Var_t v) const -> uint8_t { return flags_[v] & marked_mask; }
    [[nodiscard]] bool marked(Literal p) const { return Potassco::test_any(marked(p.var()), mask(p)); }

    void unmarkVar(Var_t v) const { Potassco::store_clear_mask(flags_[v], marked_mask); }
    void mark(Literal p) const { Potassco::store_set_mask(flags_[p.var()], mask(p)); }

    void addOcc(Literal p, uint32_t id) {
        auto v = p.var();
        occurs_[v].push_back(Literal(id, p.sign()));
        ++counts_[v][p.sign()];
    }
    void removeOcc(Literal p, uint32_t id, bool updateClauseList) {
        auto v = p.var();
        --counts_[v][p.sign()];
        if (updateClauseList) {
            auto& occ = occurs_[v];
            if (auto it = std::ranges::find(occ, Literal(id, p.sign())); it != occ.end()) {
                occ.erase(it);
            }
        }
    }
    void addWatch(const Clause& c, uint32_t clId) { watches_[c[0].var()].push_back(clId); }
    void removeWatch(const Clause& c, uint32_t clId) {
        auto& watches = watches_[c[0].var()];
        if (auto it = std::ranges::find(watches, clId); it != watches.end()) {
            watches.erase(it);
        }
    }
    void updateHeap(Var_t v) {
        if (allowElim(v)) {
            elimHeap_.update(v);
            if (Potassco::test_bit(flags_[0], bce_bit) && not Potassco::test_bit(flags_[v], bce_bit)) {
                watches_[0].push_back(v);
                Potassco::store_toggle_bit(flags_[v], bce_bit);
            }
        }
    }
    void clearVar(Var_t v) {
        discardVec(occurs_[v]);
        discardVec(watches_[v]);
        counts_[v] = OccCount{};
        flags_[v]  = {};
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
    void checkTimeout() const;

    OccurLists     occurs_;     // occur list for each variable
    WatchLists     watches_;    // watch list for each variable
    OccurCounts    counts_;     // occur counters for each variable
    VarStates      flags_;      // state for each variable
    ElimHeap       elimHeap_;   // candidates for variable elimination; ordered by increasing occurrence-cost
    VarVec         occT_[2];    // temporary clause lists used in eliminateVar
    ClauseVec      resCands_;   // pairs of clauses to be resolved
    LitVec         resolvent_;  // temporary, used in addResolvent
    IdQueue        queue_;      // indices of clauses waiting for subsumption-check
    const Options* opts_;       // active options
    double         timeout_{0}; // stop once time > timeout_
    uint32_t       facts_{0};   // [facts_, solver.trail.size()): new top-level facts
    uint32_t       nOcc_{0};    // size of occurs_ (number of variables)
};
} // namespace Clasp
