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
    using ClRange  = std::span<Literal>;
    using IdQueue  = VecQueue<uint32_t>;
    using OccCount = std::array<uint32_t, 2u>;

    using OccurLists  = std::unique_ptr<LitVec[]>;
    using WatchLists  = std::unique_ptr<VarVec[]>;
    using OccurCounts = std::unique_ptr<OccCount[]>;
    static constexpr auto sum(const OccCount& c) -> uint32_t { return c[0] + c[1]; }
    static constexpr auto costs(const OccCount& c) -> uint32_t { return saturating_mul<uint32_t>(c[0], c[1]); }
    struct LessOccCost {
        explicit LessOccCost(OccurCounts& st) : counts_(st) {}
        bool operator()(Var_t v1, Var_t v2) const { return costs(counts_[v1]) < costs(counts_[v2]); }

    private:
        OccurCounts& counts_;
    };
    using ElimHeap = bk_lib::indexed_priority_queue<Var_t, LessOccCost, Vector_t>;
    [[nodiscard]] auto numOcc(Var_t v) const -> uint32_t { return sum(counts_[v]); }
    [[nodiscard]] auto allowElim(Var_t v) const -> bool {
        return not ctx().varInfo(v).frozen() && not ctx().eliminated(v);
    }
    [[nodiscard]] auto findUnmarkedLit(const Clause& c, uint32_t x) const -> uint32_t;
    [[nodiscard]] auto subsumes(const Clause& c, const Clause& other, Literal res) -> Literal;
    [[nodiscard]] bool trivialResolvent(const Clause& c2, Var_t v) const;
    [[nodiscard]] bool timeout() const { return time(nullptr) > timeout_; }
    [[nodiscard]] bool cutoff(Var_t v) const {
        return opts_.occLimit(counts_[v][0], counts_[v][1]) || (costs(counts_[v]) == 0 && ctx().preserveModels());
    }

    [[nodiscard]] bool marked(Var_t v) const { return ctx().varInfo(v).has(VarInfo::flag_pos | VarInfo::flag_neg); }
    [[nodiscard]] bool marked(Literal p) const { return ctx().marked(p); }

    void unmarkVar(Var_t v) const { ctx().unmark(v); }
    void mark(Literal p) const { ctx().mark(p); }

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
            if (opts_.type == Options::sat_pre_full && not ctx().master()->seen(v)) {
                assert(ctx().master()->value(v) == value_free);
                watches_[0].push_back(v);
                ctx().master()->markSeen(v);
            }
        }
    }
    void clearVar(Var_t v) {
        discardVec(occurs_[v]);
        discardVec(watches_[v]);
        counts_[v] = OccCount{};
    }
    auto        popSubQueue() -> Clause*;
    void        addToSubQueue(uint32_t clauseId);
    void        attach(uint32_t cId, bool initialClause);
    void        detach(uint32_t cId);
    void        bceVeRemove(uint32_t cId, bool freeId, Var_t v, bool blocked);
    bool        propagateFacts();
    bool        backwardSubsume();
    bool        strengthenClause(uint32_t clauseId, Literal p);
    bool        subsumed(LitVec& cl);
    bool        eliminateVars();
    bool        bce();
    bool        bceVe(Var_t v, uint32_t maxCnt);
    void        resizeOcc(uint32_t ns);
    auto        splitOcc(Var_t v, bool mark) -> ClRange;
    void        markAll(LitView lits) const;
    void        unmarkAll(LitView lits) const;
    bool        addResolvent(uint32_t newId, const Clause& c1, const Clause& c2);
    static auto cacheLines(uint32_t nLits) -> uint32_t { return toU32(((nLits * sizeof(Literal)) + 63u) / 64u); }
    void        addTicks(const Clause& c) {
        auto sz = c.size();
        ++stats.baseTicks;
        stats.cacheTicks += cacheLines(sz);
    }

    enum OccSign { occ_pos = 0, occ_neg = 1 };
    OccurLists  occurs_;    // occur list for each variable
    WatchLists  watches_;   // watch list for each variable
    OccurCounts counts_;    // occur counts for each variable
    ElimHeap    elimHeap_;  // candidates for variable elimination; ordered by increasing occurrence-cost
    VarVec      occT_[2];   // temporary clause lists used in eliminateVar
    ClauseVec   resCands_;  // pairs of clauses to be resolved
    LitVec      resolvent_; // temporary, used in addResolvent
    IdQueue     queue_;     // indices of clauses waiting for subsumption-check
    Options     opts_{};    // active options
    uint32_t    facts_{0};  // [facts_, solver.trail.size()): new top-level facts
    uint32_t    nOcc_{0};   // size of occurs_ (number of variables)
    uint32_t    wTick_{1};
    std::time_t timeout_{}; // stop once time > timeout_
};
} // namespace Clasp
