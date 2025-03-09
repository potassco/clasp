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
#pragma once

#include <clasp/constraint.h>
#include <clasp/literal.h>
#include <clasp/util/left_right_sequence.h>
#include <clasp/util/misc_types.h>

#include <numeric>
/*!
 * \file
 * \brief Types and functions used by a Solver
 */
namespace Clasp {
class SharedLiterals;

/*!
 * \addtogroup solver
 */
//@{
///////////////////////////////////////////////////////////////////////////////
// Statistics
///////////////////////////////////////////////////////////////////////////////
class StatisticObject;
class StatsMap;
#if !defined(DOXY)
#define DOXY(X)
#endif
#define CLASP_STAT_DEFINE(m, k, a, accu) m
#define NO_ARG
#define CLASP_DECLARE_ISTATS(T)                                                                                        \
    void               accu(const T& o);                                                                               \
    static uint32_t    size();                                                                                         \
    static const char* key(uint32_t i);                                                                                \
    StatisticObject    at(const char* key) const

//! A struct for holding core statistics used by a solver.
/*!
 * Core statistics are always present in a solver and hence
 * can be used by heuristics.
 */
struct CoreStats {
#define CLASP_CORE_STATS(STAT, LHS, RHS)                                                                               \
    STAT(uint64_t choices{}; DOXY(number of choices), "choices", VALUE(choices), (LHS).choices += (RHS).choices)       \
    STAT(uint64_t conflicts{};                                                                                         \
         DOXY(number of conflicts), "conflicts", VALUE(conflicts), (LHS).conflicts += (RHS).conflicts)                 \
    STAT(uint64_t analyzed{};                                                                                          \
         DOXY(number of conflicts analyzed), "conflicts_analyzed", VALUE(analyzed), (LHS).analyzed += (RHS).analyzed)  \
    STAT(uint64_t restarts{}; DOXY(number of restarts), "restarts", VALUE(restarts), (LHS).restarts += (RHS).restarts) \
    STAT(uint64_t lastRestart{}; DOXY(length of last restart), "restarts_last", VALUE(lastRestart),                    \
                                 (LHS).lastRestart = std::max((LHS).lastRestart, (RHS).lastRestart))                   \
    STAT(uint64_t blRestarts{}; DOXY(number of blocked restarts), "restarts_blocked", VALUE(blRestarts),               \
                                (LHS).blRestarts = std::max((LHS).blRestarts, (RHS).blRestarts))

    constexpr CoreStats() = default;
    [[nodiscard]] constexpr uint64_t backtracks() const { return conflicts - analyzed; }
    [[nodiscard]] constexpr uint64_t backjumps() const { return analyzed; }
    [[nodiscard]] constexpr double   avgRestart() const { return ratio(analyzed, restarts); }
    CLASP_DECLARE_ISTATS(CoreStats);
    CLASP_CORE_STATS(CLASP_STAT_DEFINE, NO_ARG, NO_ARG)
};
//! A struct for holding (optional) jump statistics.
struct JumpStats {
#define CLASP_JUMP_STATS(STAT, LHS, RHS)                                                                               \
    STAT(uint64_t jumps{}; DOXY(number of backjumps), "jumps", VALUE(jumps), (LHS).jumps += (RHS).jumps)               \
    STAT(uint64_t bounded{};                                                                                           \
         DOXY(backjumps bounded by root level), "jumps_bounded", VALUE(bounded), (LHS).bounded += (RHS).bounded)       \
    STAT(uint64_t jumpSum{}; DOXY(levels removed by jumps), "levels", VALUE(jumpSum), (LHS).jumpSum += (RHS).jumpSum)  \
    STAT(uint64_t boundSum{};                                                                                          \
         DOXY(levels kept because of root level), "levels_bounded", VALUE(boundSum), (LHS).boundSum += (RHS).boundSum) \
    STAT(uint32_t maxJump{}; DOXY(longest backjump), "max", VALUE(maxJump), MAX_MEM((LHS).maxJump, (RHS).maxJump))     \
    STAT(uint32_t maxJumpEx{}; DOXY(longest unbounded backjump), "max_executed", VALUE(maxJumpEx),                     \
                               MAX_MEM((LHS).maxJumpEx, (RHS).maxJumpEx))                                              \
    STAT(uint32_t maxBound{}; DOXY(max levels kept because of root level), "max_bounded", VALUE(maxBound),             \
                              MAX_MEM((LHS).maxBound, (RHS).maxBound))

    constexpr JumpStats() = default;
    void update(uint32_t dl, uint32_t uipLevel, uint32_t bLevel) {
        ++jumps;
        jumpSum += dl - uipLevel;
        maxJump  = std::max(maxJump, dl - uipLevel);
        if (uipLevel < bLevel) {
            ++bounded;
            boundSum  += bLevel - uipLevel;
            maxJumpEx  = std::max(maxJumpEx, dl - bLevel);
            maxBound   = std::max(maxBound, bLevel - uipLevel);
        }
        else {
            maxJumpEx = maxJump;
        }
    }
    [[nodiscard]] constexpr uint64_t jumped() const { return jumpSum - boundSum; }
    [[nodiscard]] constexpr double   jumpedRatio() const { return ratio(jumped(), jumpSum); }
    [[nodiscard]] constexpr double   avgBound() const { return ratio(boundSum, bounded); }
    [[nodiscard]] constexpr double   avgJump() const { return ratio(jumpSum, jumps); }
    [[nodiscard]] constexpr double   avgJumpEx() const { return ratio(jumped(), jumps); }
    CLASP_DECLARE_ISTATS(JumpStats);
    CLASP_JUMP_STATS(CLASP_STAT_DEFINE, NO_ARG, NO_ARG)
};

//! A struct for holding (optional) extended statistics.
struct ExtendedStats {
    //! An array for storing a value[t-1] for each learnt ConstraintType t.
    using Array = uint64_t[Potassco::enum_max<ConstraintType>()];
    static constexpr uint32_t index(ConstraintType t) { return +t - 1; }
#define CLASP_EXTENDED_STATS(STAT, LHS, RHS)                                                                           \
    STAT(uint64_t domChoices{};                                                                                        \
         DOXY(number of domain choices), "domain_choices", VALUE(domChoices), (LHS).domChoices += (RHS).domChoices)    \
    STAT(uint64_t models{}; DOXY(number of models), "models", VALUE(models), (LHS).models += (RHS).models)             \
    STAT(uint64_t modelLits{};                                                                                         \
         DOXY(decision levels in models), "models_level", VALUE(modelLits), (LHS).modelLits += (RHS).modelLits)        \
    STAT(uint64_t hccTests{};                                                                                          \
         DOXY(number of stability tests), "hcc_tests", VALUE(hccTests), (LHS).hccTests += (RHS).hccTests)              \
    STAT(uint64_t hccPartial{};                                                                                        \
         DOXY(number of partial tests), "hcc_partial", VALUE(hccPartial), (LHS).hccPartial += (RHS).hccPartial)        \
    STAT(uint64_t deleted{}; DOXY(lemmas deleted), "lemmas_deleted", VALUE(deleted), (LHS).deleted += (RHS).deleted)   \
    STAT(uint64_t distributed{};                                                                                       \
         DOXY(lemmas distributed), "distributed", VALUE(distributed), (LHS).distributed += (RHS).distributed)          \
    STAT(uint64_t sumDistLbd{}; DOXY(lbds of distributed lemmas), "distributed_sum_lbd", VALUE(sumDistLbd),            \
                                (LHS).sumDistLbd += (RHS).sumDistLbd)                                                  \
    STAT(uint64_t integrated{};                                                                                        \
         DOXY(lemmas integrated), "integrated", VALUE(integrated), (LHS).integrated += (RHS).integrated)               \
    STAT(Array learnts{}; DOXY(lemmas of each learnt type), "lemmas", MEM_FUN(lemmas), NO_ARG)                         \
    STAT(Array lits{}; DOXY(lits of each learnt type), "lits_learnt", MEM_FUN(learntLits), NO_ARG)                     \
    STAT(uint32_t binary{};                                                                                            \
         DOXY(number of binary lemmas), "lemmas_binary", VALUE(binary), (LHS).binary += (RHS).binary)                  \
    STAT(uint32_t ternary{};                                                                                           \
         DOXY(number of ternary lemmas), "lemmas_ternary", VALUE(ternary), (LHS).ternary += (RHS).ternary)             \
    STAT(double cpuTime{}; DOXY(cpu time used), "cpu_time", VALUE(cpuTime), (LHS).cpuTime += (RHS).cpuTime)            \
    STAT(uint64_t intImps{};                                                                                           \
         DOXY(implications on integrating), "integrated_imps", VALUE(intImps), (LHS).intImps += (RHS).intImps)         \
    STAT(uint64_t intJumps{};                                                                                          \
         DOXY(backjumps on integrating), "integrated_jumps", VALUE(intJumps), (LHS).intJumps += (RHS).intJumps)        \
    STAT(uint64_t gpLits{};                                                                                            \
         DOXY(lits in received gps), "guiding_paths_lits", VALUE(gpLits), (LHS).gpLits += (RHS).gpLits)                \
    STAT(uint32_t gps{}; DOXY(guiding paths received), "guiding_paths", VALUE(gps), (LHS).gps += (RHS).gps)            \
    STAT(uint32_t splits{}; DOXY(split requests handled), "splits", VALUE(splits), (LHS).splits += (RHS).splits)       \
    STAT(NO_ARG, "lemmas_conflict", VALUE(learnts[0]), (LHS).learnts[0] += (RHS).learnts[0])                           \
    STAT(NO_ARG, "lemmas_loop", VALUE(learnts[1]), (LHS).learnts[1] += (RHS).learnts[1])                               \
    STAT(NO_ARG, "lemmas_other", VALUE(learnts[2]), (LHS).learnts[2] += (RHS).learnts[2])                              \
    STAT(NO_ARG, "lits_conflict", VALUE(lits[0]), (LHS).lits[0] += (RHS).lits[0])                                      \
    STAT(NO_ARG, "lits_loop", VALUE(lits[1]), (LHS).lits[1] += (RHS).lits[1])                                          \
    STAT(NO_ARG, "lits_other", VALUE(lits[2]), (LHS).lits[2] += (RHS).lits[2])                                         \
    STAT(JumpStats jumps; DOXY(backjump statistics), "jumps", MAP(jumps), (LHS).jumps.accu((RHS).jumps))

    constexpr ExtendedStats() = default;
    constexpr void addLearnt(uint32_t size, ConstraintType t) {
        if (t == ConstraintType::static_) {
            return;
        }
        auto idx      = index(t);
        learnts[idx] += 1;
        lits[idx]    += size;
        binary       += (size == 2);
        ternary      += (size == 3);
    }
    //! Total number of lemmas learnt.
    [[nodiscard]] constexpr uint64_t lemmas() const {
        return std::accumulate(std::begin(learnts), std::end(learnts), static_cast<uint64_t>(0));
    }
    //! Total number of literals in all learnt lemmas.
    [[nodiscard]] constexpr uint64_t learntLits() const {
        return std::accumulate(std::begin(lits), std::end(lits), static_cast<uint64_t>(0));
    }
    //! Number of lemmas of learnt type t.
    [[nodiscard]] constexpr uint64_t lemmas(ConstraintType t) const { return learnts[index(t)]; }
    //! Average length of lemmas of learnt type t.
    [[nodiscard]] constexpr double avgLen(ConstraintType t) const { return ratio(lits[index(t)], lemmas(t)); }
    //! Average decision level on which models were found.
    [[nodiscard]] constexpr double avgModel() const { return ratio(modelLits, models); }
    //! Ratio of lemmas that were distributed to other threads.
    [[nodiscard]] constexpr double distRatio() const { return ratio(distributed, learnts[0] + learnts[1]); }
    //! Average lbd of lemmas that were distributed to other threads.
    [[nodiscard]] constexpr double avgDistLbd() const { return ratio(sumDistLbd, distributed); }
    [[nodiscard]] constexpr double avgIntJump() const { return ratio(intJumps, intImps); }
    //! Average length (i.e. number of literals) of guiding paths.
    [[nodiscard]] constexpr double avgGp() const { return ratio(gpLits, gps); }
    //! Ratio of lemmas integrated.
    [[nodiscard]] constexpr double intRatio() const { return ratio(integrated, distributed); }
    CLASP_DECLARE_ISTATS(ExtendedStats);
    CLASP_EXTENDED_STATS(CLASP_STAT_DEFINE, NO_ARG, NO_ARG)
};

//! A struct for aggregating statistics maintained in a solver object.
struct SolverStats : CoreStats {
    SolverStats() = default;
    SolverStats(const SolverStats& o);
    SolverStats& operator=(const SolverStats&) = delete;
    ~SolverStats();
    bool                      enableExtended();
    bool                      enable(const SolverStats& o) { return not o.extra || enableExtended(); }
    void                      reset();
    void                      accu(const SolverStats& o);
    void                      accu(const SolverStats& o, bool enableRhs);
    void                      swapStats(SolverStats& o);
    void                      flush() const;
    [[nodiscard]] uint32_t    size() const;
    [[nodiscard]] const char* key(uint32_t i) const;
    StatisticObject           at(const char* key) const;
    void                      addTo(const char* key, StatsMap& solving, StatsMap* accu) const;
    inline void               addLearnt(uint32_t size, ConstraintType t);
    inline void               addConflict(uint32_t dl, uint32_t uipLevel, uint32_t bLevel, uint32_t lbd);
    inline void               addDeleted(uint32_t num);
    inline void               addDistributed(uint32_t lbd, ConstraintType t);
    inline void               addTest(bool partial);
    inline void               addModel(uint32_t dl);
    inline void               addCpuTime(double t);
    inline void               addSplit(uint32_t n = 1);
    inline void               addDomChoice(uint32_t n = 1);
    inline void               addIntegratedAsserting(uint32_t startLevel, uint32_t jumpLevel);
    inline void               addIntegrated(uint32_t n = 1);
    inline void               removeIntegrated(uint32_t n = 1);
    inline void               addPath(LitView::size_type sz);
    ExtendedStats*            extra = nullptr; /**< Optional extended statistics. */
    SolverStats*              multi = nullptr; /**< Not owned: set to accu stats in multishot solving. */
};
// NOLINTBEGIN(readability-make-member-function-const)
inline void SolverStats::addLearnt(uint32_t size, ConstraintType t) {
    if (extra) {
        extra->addLearnt(size, t);
    }
}
inline void SolverStats::addDeleted(uint32_t num) {
    if (extra) {
        extra->deleted += num;
    }
}
inline void SolverStats::addDistributed(uint32_t lbd, ConstraintType) {
    if (extra) {
        ++extra->distributed;
        extra->sumDistLbd += lbd;
    }
}
inline void SolverStats::addIntegrated(uint32_t n) {
    if (extra) {
        extra->integrated += n;
    }
}
inline void SolverStats::removeIntegrated(uint32_t n) {
    if (extra) {
        extra->integrated -= n;
    }
}
inline void SolverStats::addCpuTime(double t) {
    if (extra) {
        extra->cpuTime += t;
    }
}
inline void SolverStats::addSplit(uint32_t n) {
    if (extra) {
        extra->splits += n;
    }
}
inline void SolverStats::addPath(LitView::size_type sz) {
    if (extra) {
        ++extra->gps;
        extra->gpLits += sz;
    }
}
inline void SolverStats::addTest(bool partial) {
    if (extra) {
        ++extra->hccTests;
        extra->hccPartial += static_cast<uint32_t>(partial);
    }
}
inline void SolverStats::addModel(uint32_t dl) {
    if (extra) {
        ++extra->models;
        extra->modelLits += dl;
    }
}
inline void SolverStats::addDomChoice(uint32_t n) {
    if (extra) {
        extra->domChoices += n;
    }
}
inline void SolverStats::addIntegratedAsserting(uint32_t startLevel, uint32_t jumpLevel) {
    if (extra) {
        ++extra->intImps;
        extra->intJumps += (startLevel - jumpLevel);
    }
}
// NOLINTEND(readability-make-member-function-const)
inline void SolverStats::addConflict(uint32_t dl, uint32_t uipLevel, uint32_t bLevel, uint32_t) {
    ++analyzed;
    if (extra) {
        extra->jumps.update(dl, uipLevel, bLevel);
    }
}
#undef CLASP_STAT_DEFINE
#undef NO_ARG
#undef DOXY
#undef CLASP_DECLARE_ISTATS
///////////////////////////////////////////////////////////////////////////////
// Clauses
///////////////////////////////////////////////////////////////////////////////
//! Primitive representation of a clause.
struct ClauseRep {
    using Info = ConstraintInfo;
    static constexpr ClauseRep create(std::span<Literal> lits, const Info& i = Info()) {
        return {i, size32(lits), false, lits.data()};
    }
    static constexpr ClauseRep prepared(std::span<Literal> lits, const Info& i = Info()) {
        return {i, size32(lits), true, lits.data()};
    }

    [[nodiscard]] constexpr bool    isImp() const { return size > 1 && size < 4; }
    [[nodiscard]] constexpr LitView literals() const { return {lits, size}; }

    Info     info;                /*!< Additional clause info.    */
    uint32_t size : 31 = 0;       /*!< Size of array of literals. */
    uint32_t prep : 1  = 0;       /*!< Whether lits is already prepared. */
    Literal* lits      = nullptr; /*!< Pointer to array of literals (not owned!). */
};

//! (Abstract) base class for clause types.
/*!
 * ClauseHead is used to enforce a common memory-layout for all clauses.
 * It contains the two watched literals and a cache literal to improve
 * propagation performance. A virtual call to Constraint::propagate()
 * is only needed if the other watch is not true and the cache literal
 * is false.
 */
class ClauseHead : public Constraint {
public:
    static constexpr auto head_lits     = 3u;
    static constexpr auto max_short_len = 5u;

    explicit ClauseHead(const InfoType& init);
    // base interface
    //! Propagates the head and calls updateWatch() if necessary.
    PropResult propagate(Solver& s, Literal, uint32_t& data) override;
    //! Type of clause.
    [[nodiscard]] Type type() const override { return info_.type(); }
    //! Returns the activity of this clause.
    [[nodiscard]] ScoreType activity() const override { return info_.score(); }
    //! True if this clause currently is the antecedent of an assignment.
    [[nodiscard]] bool locked(const Solver& s) const override;
    //! Halves the activity of this clause.
    void decreaseActivity() override { info_.score().reduce(); }
    void resetActivity() override { info_.score().reset(); }
    //! Downcast from LearntConstraint.
    ClauseHead* clause() override { return this; }

    // clause interface
    //! Adds watches for first two literals in head to solver.
    void attach(Solver& s);
    void resetScore(ScoreType sc);
    //! Returns true if head is satisfied w.r.t current assignment in s.
    [[nodiscard]] bool satisfied(const Solver& s) const;
    //! Conditional clause?
    [[nodiscard]] bool tagged() const { return info_.tagged(); }
    //! Contains aux vars?
    [[nodiscard]] bool     aux() const { return info_.aux(); }
    [[nodiscard]] bool     learnt() const { return info_.learnt(); }
    [[nodiscard]] uint32_t lbd() const { return info_.lbd(); }
    //! Removes watches from s.
    virtual void detach(Solver& s);
    //! Returns the size of this clause.
    [[nodiscard]] virtual uint32_t size() const = 0;
    //! Returns the literals of this clause in out.
    virtual void toLits(LitVec& out) const = 0;
    //! Returns true if this clause is a valid "reverse antecedent" for p.
    virtual bool isReverseReason(const Solver& s, Literal p, uint32_t maxL, uint32_t maxN) = 0;
    struct StrengthenResult {
        bool litRemoved   = false;
        bool removeClause = false;
    };
    //! Removes p from clause if possible.
    /*!
     * \return A StrengthenResult object @c r, with:
     *   - @c r.litRemoved if p was removed from the clause.
     *   - @c r.removeClause if the clause should be removed.
     */
    virtual StrengthenResult strengthen(Solver& s, Literal p, bool allowToShort = true) = 0;

protected:
    struct Local {
        void                   init(uint32_t sz);
        [[nodiscard]] bool     isSmall() const { return (mem[0] & 1u) == 0u; }
        [[nodiscard]] bool     contracted() const { return (mem[0] & 3u) == 3u; }
        [[nodiscard]] bool     strengthened() const { return (mem[0] & 5u) == 5u; }
        [[nodiscard]] uint32_t size() const { return mem[0] >> 3; }
        void                   setSize(uint32_t size) { mem[0] = (size << 3) | (mem[0] & 7u); }
        void                   markContracted() { mem[0] |= 2u; }
        void                   markStrengthened() { mem[0] |= 4u; }
        void                   clearContracted() { mem[0] &= ~2u; }
        void                   clearIdx() { mem[1] = 0; }
        uint32_t               mem[2];
    };
    bool toImplication(Solver& s);
    void clearTagged() { info_.setTagged(false); }
    void setLbd(uint32_t x) { info_.setLbd(x); }
    //! Shall replace the watched literal at position pos with a non-false literal.
    /*!
     * \pre pos in [0,1]
     * \pre s.isFalse(head_[pos]) && s.isFalse(head_[2])
     * \pre head_[pos^1] is the other watched literal
     */
    virtual bool updateWatch(Solver& s, uint32_t pos) = 0;
    union {
        Local           local_;
        SharedLiterals* shared_;
    };
    InfoType info_;
    Literal  head_[head_lits]; // two watched literals and one cache literal
};
//! Allocator for small (at most 32-byte) clauses.
class SmallClauseAlloc {
public:
    SmallClauseAlloc();
    ~SmallClauseAlloc();
    SmallClauseAlloc(SmallClauseAlloc&&) = delete;

    void* allocate() {
        if (freeList_ == nullptr) {
            allocBlock();
        }
        Chunk* r  = freeList_;
        freeList_ = r->next;
        return r;
    }
    void free(void* mem) {
        auto* b   = static_cast<Chunk*>(mem);
        b->next   = freeList_;
        freeList_ = b;
    }

private:
    struct Chunk {
        Chunk*        next; // enforce ptr alignment
        unsigned char mem[32 - sizeof(Chunk*)];
    };
    struct Block {
        static constexpr auto num_chunks = 1023u;

        Block*        next;
        unsigned char pad[32 - sizeof(Block*)];
        Chunk         chunk[num_chunks];
    };
    void   allocBlock();
    Block* blocks_;
    Chunk* freeList_;
};
///////////////////////////////////////////////////////////////////////////////
// Watches
///////////////////////////////////////////////////////////////////////////////
//! Represents a clause watch in a Solver.
struct ClauseWatch {
    //! Clause watch: clause head
    explicit ClauseWatch(ClauseHead* a_head) : head(a_head) {}
    ClauseHead* head;
    struct EqHead {
        constexpr explicit EqHead(ClauseHead* h) : head(h) {}
        constexpr bool operator()(const ClauseWatch& w) const { return head == w.head; }
        ClauseHead*    head;
    };
};

//! Represents a generic watch in a Solver.
struct GenericWatch {
    //! A constraint and some associated data.
    explicit GenericWatch(Constraint* a_con, uint32_t a_data = 0) : con(a_con), data(a_data) {}
    //! Calls propagate on the stored constraint and passes the stored data to that constraint.
    Constraint::PropResult propagate(Solver& s, Literal p) { return con->propagate(s, p, data); }

    Constraint* con;  /**< The constraint watching a certain literal. */
    uint32_t    data; /**< Additional data associated with this watch - passed to constraint on update. */

    struct EqConstraint {
        constexpr explicit EqConstraint(Constraint* c) : con(c) {}
        constexpr bool operator()(const GenericWatch& w) const { return con == w.con; }
        Constraint*    con;
    };
};

//! Watch list type.
using WatchList = bk_lib::left_right_sequence<ClauseWatch, GenericWatch, 0>;
inline void releaseVec(WatchList& w) { w.reset(); }

///////////////////////////////////////////////////////////////////////////////
// Assignment
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
//! Type for storing reasons for variable assignments together with additional data.
/*!
 * \note On 32-bit systems additional data is stored in the high-word of antecedents.
 */
struct ReasonStore32 : PodVector_t<Antecedent> {
    [[nodiscard]] uint32_t data(uint32_t v) const { return decode((*this)[v]); }
    void                   setData(uint32_t v, uint32_t data) { encode((*this)[v], data); }
    static void            encode(Antecedent& a, uint32_t data) {
        a.asUint() = (static_cast<uint64_t>(data) << 32) | static_cast<uint32_t>(a.asUint());
    }
    static uint32_t decode(const Antecedent& a) { return static_cast<uint32_t>(a.asUint() >> 32); }
    struct value_type { // NOLINT
        value_type(const Antecedent& ante, uint32_t d) : a(ante) {
            if (d != UINT32_MAX) {
                encode(a, d);
                assert(data() == d && a.type() == Antecedent::generic);
            }
        }
        [[nodiscard]] const Antecedent& ante() const { return a; }
        [[nodiscard]] uint32_t data() const { return a.type() == Antecedent::generic ? decode(a) : UINT32_MAX; }
        Antecedent             a;
    };
};

//! Type for storing reasons for variable assignments together with additional data.
/*
 * \note On 64-bit systems additional data is stored in a separate container.
 */
struct ReasonStore64 : PodVector_t<Antecedent> {
    [[nodiscard]] uint32_t dataSize() const { return size32(dv); }
    void                   dataResize(uint32_t nv) {
        if (nv > dataSize()) {
            dv.resize(nv, UINT32_MAX);
        }
    }
    [[nodiscard]] uint32_t data(uint32_t v) const { return v < dataSize() ? dv[v] : UINT32_MAX; }
    void                   setData(uint32_t v, uint32_t data) {
        dataResize(v + 1);
        dv[v] = data;
    }
    VarVec dv;
    struct value_type { // NOLINT
        constexpr value_type(const Antecedent& ante, uint32_t data) : a(ante), d(data) {}
        [[nodiscard]] const Antecedent& ante() const { return a; }
        [[nodiscard]] uint32_t          data() const { return d; }
        Antecedent                      a;
        uint32_t                        d;
    };
};

//! A set of configurable values for a variable.
/*!
 * Beside its currently assigned value, a variable
 * can also have a user, saved, preferred, and default value.
 * These values are used in sign selection to determine the signed literal
 * of a variable to be assign first.
 * During sign selection, the values form a hierarchy:
 * user > saved > preferred > current sign score of heuristic > default value
 */
struct ValueSet {
    enum Value : uint32_t { user_value = 0x03u, saved_value = 0x0Cu, pref_value = 0x30u, def_value = 0xC0u };
    constexpr ValueSet() = default;
    [[nodiscard]] constexpr bool  sign() const { return Potassco::test_any(Potassco::right_most_bit(rep), 0xAAu); }
    [[nodiscard]] constexpr bool  empty() const { return rep == 0; }
    [[nodiscard]] constexpr bool  has(Value v) const { return Potassco::test_any(rep, v); }
    [[nodiscard]] constexpr bool  has(uint32_t f) const { return Potassco::test_any(rep, f); }
    [[nodiscard]] constexpr Val_t get(Value v) const {
        return static_cast<Val_t>((rep & v) / Potassco::right_most_bit<uint8_t>(v));
    }
    constexpr void set(Value which, Val_t to) {
        Potassco::store_clear_mask(rep, which);
        Potassco::store_set_mask(rep, to * Potassco::right_most_bit<uint8_t>(which));
    }
    constexpr void save(Val_t x) {
        Potassco::store_clear_mask(rep, saved_value);
        Potassco::store_set_mask(rep, x << 2);
    }
    uint8_t rep{0};
};

//! Stores assignment related information.
/*!
 * For each variable v, the class stores
 *  - v's current value (value_free if unassigned)
 *  - the decision level on which v was assign (only valid if value(v) != value_free)
 *  - the reason why v is in the assignment (only valid if value(v) != value_free)
 *  - (optionally) some additional data associated with the reason
 *  .
 * Furthermore, the class stores the sequences of assignments as a set of
 * true literals in its trail-member.
 */
class Assignment {
public:
    using AssignVec      = PodVector_t<uint32_t>;
    using PrefVec        = PodVector_t<ValueSet>;
    using ReasonVec      = std::conditional_t<sizeof(Constraint*) == sizeof(uint64_t), ReasonStore64, ReasonStore32>;
    using ReasonWithData = ReasonVec::value_type;
    Assignment()         = default;
    Assignment(const Assignment&)            = delete;
    Assignment& operator=(const Assignment&) = delete;

    LitVec                 trail;    // assignment sequence
    uint32_t               front{0}; // and "propagation queue"
    [[nodiscard]] bool     qEmpty() const { return front == size32(trail); }
    [[nodiscard]] uint32_t qSize() const { return size32(trail) - front; }
    Literal                qPop() { return trail[front++]; }
    void                   qReset() { front = size32(trail); }

    //! Number of variables in the three-valued assignment.
    [[nodiscard]] uint32_t numVars() const { return size32(assign_); }
    //! Number of assigned variables.
    [[nodiscard]] uint32_t assigned() const { return size32(trail); }
    //! Number of free variables.
    [[nodiscard]] uint32_t free() const { return numVars() - (assigned() + elims_); }
    //! Returns the largest possible decision level.
    [[nodiscard]] uint32_t maxLevel() const { return (1u << 28) - 2; }
    //! Returns v's value in the three-valued assignment.
    [[nodiscard]] Val_t value(Var_t v) const { return static_cast<Val_t>(assign_[v] & value_mask); }
    //! Returns the decision level on which v was assigned if value(v) != value_free.
    [[nodiscard]] uint32_t level(Var_t v) const { return assign_[v] >> level_shift; }
    //! Returns true if v was not eliminated from the assignment.
    [[nodiscard]] bool valid(Var_t v) const { return not Potassco::test_mask(assign_[v], elim_mask); }
    //! Returns the set of preferred values of v.
    [[nodiscard]] ValueSet pref(Var_t v) const { return v < pref_.size() ? pref_[v] : ValueSet(); }
    //! Returns the reason for v being assigned if value(v) != value_free.
    [[nodiscard]] const Antecedent& reason(Var_t v) const { return reason_[v]; }
    //! Returns the reason data associated with v.
    [[nodiscard]] uint32_t data(Var_t v) const { return reason_.data(v); }

    void reserve(uint32_t n) {
        assign_.reserve(n);
        reason_.reserve(n);
    }
    //! Resize to nv variables.
    void resize(uint32_t nv) {
        assign_.resize(nv);
        reason_.resize(nv);
    }
    //! Adds a var to assignment - initially the new var is unassigned.
    Var_t addVar() {
        assign_.push_back(0);
        reason_.push_back(nullptr);
        return numVars() - 1;
    }
    //! Allocates space for storing preferred values for all variables.
    void requestPrefs() {
        if (pref_.size() != assign_.size()) {
            pref_.resize(assign_.size());
        }
    }
    //! Eliminates v from the assignment.
    void eliminate(Var_t v) {
        assert(value(v) == value_free && "Can not eliminate assigned var!\n");
        if (valid(v)) {
            assign_[v] = elim_mask | value_true;
            ++elims_;
        }
    }
    //! Assigns p.var() on level lev to the value that makes p true and stores x as reason for the assignment.
    /*!
     * \return true if the assignment is consistent. False, otherwise.
     * \post If true is returned, p is in trail. Otherwise, ~p is.
     */
    template <std::integral... DataT>
    bool assign(Literal p, uint32_t lev, const Antecedent& x, DataT... data) {
        static_assert(sizeof...(DataT) <= 1);
        const auto v   = p.var();
        const auto val = value(v);
        if (val == value_free) {
            assert(valid(v));
            assign_[v] = (lev << level_shift) + trueValue(p);
            reason_[v] = x;
            if constexpr (sizeof...(DataT) > 0) {
                reason_.setData(v, data...);
            }
            trail.push_back(p);
            return true;
        }
        return val == trueValue(p);
    }
    //! Undos all assignments in the range trail[first, last).
    /*!
     * \param first First assignment to be undone.
     * \param save  If true, previous assignment of a var is saved before it is undone.
     */
    void undoTrail(LitVec::size_type first, bool save) {
        if (auto stop = trail[first]; not save) {
            popUntil<false>(stop);
        }
        else {
            requestPrefs();
            popUntil<true>(stop);
        }
        qReset();
    }
    //! Undos the last assignment.
    void undoLast() {
        clear(trail.back().var());
        trail.pop_back();
    }
    //! Returns the last assignment as a true literal.
    [[nodiscard]] Literal last() const { return trail.back(); }
    Literal&              last() { return trail.back(); }
    /*!
     * \name Implementation functions
     * Low-level implementation functions. Use with care and only if you
     * know what you are doing!
     */
    //@{
    [[nodiscard]] uint32_t units() const { return units_; }
    [[nodiscard]] bool     seen(Var_t v) const { return Potassco::test_any(assign_[v], seen_mask_v); }
    [[nodiscard]] bool     seen(Literal p) const { return Potassco::test_any(assign_[p.var()], seen_mask(p)); }
    void                   values(ValueVec& out) const {
        out.clear();
        out.reserve(assign_.size());
        for (auto x : assign_) { out.push_back(static_cast<Val_t>(x & value_mask)); }
    }
    void setSeen(Var_t v) { Potassco::store_set_mask(assign_[v], seen_mask_v); }
    void setSeen(Literal p) { Potassco::store_set_mask(assign_[p.var()], seen_mask(p)); }
    void clearSeen(Var_t v) { Potassco::store_clear_mask(assign_[v], seen_mask_v); }
    void clearValue(Var_t v) { Potassco::store_clear_mask(assign_[v], value_mask); }
    void setValue(Var_t v, Val_t val) {
        assert(value(v) == val || value(v) == value_free);
        assign_[v] |= val;
    }
    void setReason(Var_t v, const Antecedent& a) { reason_[v] = a; }
    void setData(Var_t v, uint32_t data) { reason_.setData(v, data); }
    void setPref(Var_t v, ValueSet::Value which, Val_t to) { pref_[v].set(which, to); }
    bool markUnits() {
        while (units_ != front) { setSeen(trail[units_++].var()); }
        return true;
    }
    void setUnits(uint32_t ts) { units_ = ts; }
    void resetPrefs() { pref_.assign(pref_.size(), ValueSet()); }
    void clear(Var_t v) { assign_[v] = 0; }
    //@}
private:
    static constexpr uint32_t elim_mask   = 0xFFFFFFF0u;
    static constexpr uint32_t seen_mask_v = 0b1100u;
    static constexpr uint32_t value_mask  = 0b0011u;
    static constexpr uint32_t level_shift = 4u;
    static constexpr uint32_t seen_mask(Literal p) { return static_cast<uint32_t>(trueValue(p)) << 2u; }

    template <bool SaveVal>
    void popUntil(Literal stop) {
        Literal p;
        do {
            p = trail.back();
            trail.pop_back();
            auto v = p.var();
            if constexpr (SaveVal) {
                pref_[v].save(value(v));
            }
            clear(v);
        } while (p != stop);
    }
    AssignVec assign_;   // for each var: three-valued assignment (28-bit decision level, 2-bit seen, 2-bit value)
    ReasonVec reason_;   // for each var: reason for being assigned (+ optional data)
    PrefVec   pref_;     // for each var: set of preferred values
    uint32_t  elims_{0}; // number of variables that were eliminated from the assignment
    uint32_t  units_{0}; // number of marked top-level assignments
};

//! Stores information about a literal that is implied on an earlier level than the current decision level.
struct ImpliedLiteral {
    using AnteInfo = Assignment::ReasonWithData;
    ImpliedLiteral(Literal a_lit, uint32_t a_level, const Antecedent& a_ante, uint32_t a_data = UINT32_MAX)
        : lit(a_lit)
        , level(a_level)
        , ante(a_ante, a_data) {}
    Literal  lit;   /**< The implied literal */
    uint32_t level; /**< The earliest decision level on which lit is implied */
    AnteInfo ante;  /**< The reason why lit is implied on decision-level level */
};
//! A type for storing ImpliedLiteral objects.
struct ImpliedList {
    using VecType  = PodVector_t<ImpliedLiteral>;
    using iterator = VecType::const_iterator; // NOLINT
    ImpliedList()  = default;
    //! Searches for an entry <p> in list. Returns nullptr if none is found.
    ImpliedLiteral* find(Literal p) {
        for (auto& x : lits) {
            if (x.lit == p) {
                return &x;
            }
        }
        return nullptr;
    }
    //! Adds a new object to the list.
    void add(uint32_t dl, const ImpliedLiteral& n) {
        if (dl > level) {
            level = dl;
        }
        lits.push_back(n);
    }
    //! Returns true if list contains entries that must be reassigned on current dl.
    [[nodiscard]] bool active(uint32_t dl) const { return dl < level && front != lits.size(); }
    //! Reassigns all literals that are still implied.
    bool                   assign(Solver& s);
    [[nodiscard]] iterator begin() const { return lits.begin(); }
    [[nodiscard]] iterator end() const { return lits.end(); }
    VecType                lits;     // current set of (out-of-order) implied literals
    uint32_t               level{0}; // highest dl on which lits must be reassigned
    uint32_t               front{0}; // current starting position in lits
};

using SolverSet = Potassco::Bitset<uint64_t>;

//@}
} // namespace Clasp
