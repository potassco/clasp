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
#include <clasp/util/misc_types.h>

#include <functional>
#include <memory>

#if !defined(CLASP_ALIGN_BITFIELD)
#if defined(EMSCRIPTEN)
// Force alignment of bitfield to T in order to prevent
// code-generation bug in emcc
// see: https://github.com/kripken/emscripten/issues/4540
#define CLASP_ALIGN_BITFIELD(T) T : 0;
#else
#define CLASP_ALIGN_BITFIELD(T)
#endif
#endif

/*!
 * \file
 * \brief Contains strategies and options used to configure solvers and search.
 */
namespace Clasp {
//! Implements clasp's configurable schedule-strategies.
/*!
 * clasp currently supports the following basic strategies:
 *  - geometric sequence  : X = n1 * n2^k   (k >= 0)
 *  - arithmetic sequence : X = n1 + (n2*k) (k >= 0)
 *  - fixed sequence      : X = n1 + (0*k)  (k >= 0)
 *  - luby's sequence     : X = n1 * luby(k)(k >= 0)
 *  .
 * Furthermore, an inner-outer scheme can be applied to the selected sequence.
 * In that case, the sequence is repeated every \<limit\>+j restarts, where
 * \<limit\> is the initial outer-limit and j is the number of times the
 * sequence was already repeated.
 *
 * \note For luby's sequence, j is not a repetition counter
 * but the index where the sequence grows to the next power of two.
 *
 * \see Luby et al. "Optimal speedup of las vegas algorithms."
 *
 */
struct ScheduleStrategy {
    //! Supported strategies.
    enum Type { sched_geom = 0, sched_arith = 1, sched_luby = 2 };

    ScheduleStrategy(Type t = sched_geom, uint32_t b = 100, double g = 1.5, uint32_t o = 0);
    //! Creates luby's sequence with unit-length unit and optional outer limit.
    static ScheduleStrategy luby(uint32_t unit, uint32_t limit = 0) { return {sched_luby, unit, 0, limit}; }
    //! Creates geometric sequence base * (grow^k) with optional outer limit.
    static ScheduleStrategy geom(uint32_t base, double grow, uint32_t limit = 0) {
        return {sched_geom, base, grow, limit};
    }
    //! Creates arithmetic sequence base + (add*k) with optional outer limit.
    static ScheduleStrategy arith(uint32_t base, double add, uint32_t limit = 0) {
        return {sched_arith, base, add, limit};
    }
    //! Creates fixed sequence with length base.
    static ScheduleStrategy fixed(uint32_t base) { return {sched_arith, base, 0, 0}; }
    static ScheduleStrategy none() { return {sched_geom, 0}; }
    static ScheduleStrategy def() { return {sched_arith, 0}; }
    [[nodiscard]] uint64_t  current() const;
    [[nodiscard]] bool      disabled() const { return base == 0; }
    [[nodiscard]] bool      defaulted() const { return base == 0 && type == sched_arith; }
    void                    reset() { idx = 0; }
    uint64_t                next();
    void                    advanceTo(uint32_t idx);
    uint32_t                base : 30; // base of sequence (n1)
    uint32_t                type : 2;  // type of basic sequence
    uint32_t                idx;       // current index into sequence
    uint32_t len;  // length of sequence (0 if infinite) (once reached, sequence is repeated and len increased)
    float    grow; // update parameter n2
};
//! Returns the idx-th value of the luby sequence.
uint32_t lubyR(uint32_t idx);
//! Returns the idx-th value of the geometric sequence with the given growth factor.
double growR(uint32_t idx, double g);
//! Returns the idx-th value of the arithmetic sequence with the given addend.
double addR(uint32_t idx, double a);

class DecisionHeuristic;
//! Supported decision heuristics.
enum class HeuristicType : uint32_t {
    def     = 0,
    berkmin = 1,
    vsids   = 2,
    vmtf    = 3,
    domain  = 4,
    unit    = 5,
    none    = 6,
    user    = 7
};
POTASSCO_SET_DEFAULT_ENUM_MAX(HeuristicType::user);
POTASSCO_ENABLE_CMP_OPS(HeuristicType);

//! Parameter-Object for grouping solver strategies.
struct SolverStrategies {
    //! Clasp's two general search strategies.
    enum SearchStrategy {
        use_learning = 0, //!< Analyze conflicts and learn First-1-UIP-clause.
        no_learning  = 1  //!< Don't analyze conflicts - chronological backtracking.
    };
    //! Default sign heuristic.
    enum SignHeu {
        sign_atom = 0, //!< Prefer negative literal for atoms.
        sign_pos  = 1, //!< Prefer positive literal.
        sign_neg  = 2, //!< Prefer negative literal.
        sign_rnd  = 3, //!< Prefer random literal.
    };
    //! Conflict clause minimization strategy.
    enum CCMinType {
        cc_local     = 0, //!< Basic algorithm.
        cc_recursive = 1, //!< Extended algorithm.
    };
    //! Antecedents to consider during conflict clause minimization.
    enum CCMinAntes {
        all_antes    = 0, //!< Consider all antecedents.
        short_antes  = 1, //!< Consider only short antecedents.
        binary_antes = 2, //!< Consider only binary antecedents.
        no_antes     = 3, //!< Don't minimize conflict clauses.
    };
    //! Simplifications for long conflict clauses.
    enum CCRepMode {
        cc_no_replace   = 0, //!< Don't replace literals in conflict clauses.
        cc_rep_decision = 1, //!< Replace conflict clause with decision sequence.
        cc_rep_uip      = 2, //!< Replace conflict clause with all uip clause.
        cc_rep_dynamic  = 3, //!< Dynamically select between cc_rep_decision and cc_rep_uip.
    };
    //! Strategy for initializing watched literals in clauses.
    enum WatchInit { watch_rand = 0, watch_first = 1, watch_least = 2 };
    //! Strategy for integrating new information in parallel solving.
    enum UpdateMode { update_on_propagate = 0, update_on_conflict = 1 };
    enum LbdMode { lbd_fixed = 0, lbd_updated_less = 1, lbd_update_glucose = 2, lbd_update_pseudo = 3 };

    void prepare();
    //----- 32 bit ------------
    uint32_t compress     : 16 = 0; /*!< If > 0, enable compression for learnt clauses of size > compress. */
    uint32_t saveProgress : 16 = 0; /*!< Enable progress saving if > 0. */
    //----- 32 bit ------------
    uint32_t heuId          : 3 = 0; /*!< Type of decision heuristic.   */
    uint32_t reverseArcs    : 2 = 0; /*!< Use "reverse-arcs" during learning if > 0. */
    uint32_t otfs           : 2 = 0; /*!< Enable "on-the-fly" subsumption if > 0. */
    uint32_t updateLbd      : 2 = 0; /*!< Update lbds of antecedents during conflict analysis (one of LbdMode). */
    uint32_t ccMinAntes     : 2 = 0; /*!< Antecedents to look at during conflict clause minimization. */
    uint32_t ccRepMode      : 2 = 0; /*!< One of CCRepMode. */
    uint32_t ccMinRec       : 1 = 0; /*!< If 1, use more expensive recursive nogood minimization.  */
    uint32_t ccMinKeepAct   : 1 = 0; /*!< Do not increase nogood activities during nogood minimization? */
    uint32_t initWatches    : 2 = 0; /*!< Initialize watches randomly in clauses. */
    uint32_t upMode         : 1 = 0; /*!< One of UpdateMode. */
    uint32_t bumpVarAct     : 1 = 0; /*!< Bump activities of vars implied by learnt clauses with small lbd. */
    uint32_t search         : 1 = 0; /*!< Current search strategy. */
    uint32_t restartOnModel : 1 = 0; /*!< Do a restart after each model. */
    uint32_t resetOnModel   : 1 = 0; /*!< Reset solving state like e.g. restarts on model? */
    uint32_t signDef        : 2 = 0; /*!< Default sign heuristic.        */
    uint32_t signFix        : 1 = 0; /*!< Disable all sign heuristics and always use default sign. */
    uint32_t hasConfig      : 1 = 0; /*!< Config applied to solver? */
    uint32_t id             : 6 = 0; /*!< Solver id - SHALL ONLY BE SET BY Shared Context! */
};
//! Parameter-Object for grouping additional heuristic options.
struct HeuParams {
    //! Strategy for scoring clauses not learnt by conflict analysis.
    enum ScoreOther { other_auto = 0u, other_no = 1u, other_loop = 2u, other_all = 3u };
    //! Strategy for scoring during conflict analysis.
    enum Score { score_auto = 0u, score_min = 1u, score_set = 2u, score_multi_set = 3u };
    //! Global preference for domain heuristic.
    enum DomPref { pref_atom = 0u, pref_scc = 1u, pref_hcc = 2u, pref_disj = 4u, pref_min = 8u, pref_show = 16u };
    //! Global modification for domain heuristic.
    enum DomMod {
        mod_none   = 0u,
        mod_level  = 1u,
        mod_spos   = 2u,
        mod_true   = 3u,
        mod_sneg   = 4u,
        mod_false  = 5u,
        mod_init   = 6u,
        mod_factor = 7u
    };
    //! Values for dynamic decaying scheme.
    struct VsidsDecay {
        uint32_t init : 10; /*!< Starting decay factor: 1/0.\<init\>. */
        uint32_t bump : 7;  /*!< Decay decrease value : \<bump\>/100. */
        uint32_t freq : 15; /*!< Update decay factor every \<freq\> conflicts. */
    };
    uint32_t param   : 16 = 0; /*!< Extra parameter for heuristic with meaning depending on type. */
    uint32_t score   : 2  = 0; /*!< Type of scoring during resolution. */
    uint32_t other   : 2  = 0; /*!< Consider other learnt nogoods in heuristic. */
    uint32_t moms    : 1  = 1; /*!< Use MOMS-score as top-level heuristic. */
    uint32_t nant    : 1  = 0; /*!< Prefer elements in NegAnte(P).      */
    uint32_t huang   : 1  = 0; /*!< Only for Berkmin.   */
    uint32_t acids   : 1  = 0; /*!< Only for Vsids/Dom. */
    uint32_t domPref : 5  = 0; /*!< Default pref for domain heuristic (set of DomPref). */
    uint32_t domMod  : 3  = 0; /*!< Default mod for domain heuristic (one of DomMod). */
    union {
        uint32_t   extra = 0;
        VsidsDecay decay; /*!< Only for Vsids/Dom. */
    };
};
constexpr bool isLookbackHeuristic(HeuristicType type) {
    return type >= HeuristicType::berkmin && type < HeuristicType::unit;
}
constexpr bool isLookbackHeuristic(uint32_t type) { return isLookbackHeuristic(static_cast<HeuristicType>(type)); }
using HeuristicFactory = std::function<std::unique_ptr<DecisionHeuristic>(HeuristicType, const HeuParams&)>;
//! Default factory for decision heuristics.
auto createHeuristic(HeuristicType type, const HeuParams& p) -> std::unique_ptr<DecisionHeuristic>;

struct OptParams {
    //! Strategy to use for optimization.
    enum Type {
        type_bb  = 0, //!< Branch and bound based (model-guided) optimization.
        type_usc = 1, //!< Unsatisfiable-core based (core-guided) optimization.
    };
    //! Algorithm for model-guided optimization.
    enum BBAlgo {
        bb_lin  = 0u, //!< Linear branch and bound with fixed step of size 1.
        bb_hier = 1u, //!< Hierarchical branch and bound with fixed step of size 1.
        bb_inc  = 2u, //!< Hierarchical branch and bound with increasing steps.
        bb_dec  = 3u, //!< Hierarchical branch and bound with decreasing steps.
    };
    //! Algorithm for core-guided optimization.
    enum UscAlgo {
        usc_oll = 0u, //!< OLL with possibly multiple cardinality constraints per core.
        usc_one = 1u, //!< ONE with one cardinality constraints per core.
        usc_k   = 2u, //!< K with bounded cardinality constraints of size 2 * (K+1).
        usc_pmr = 3u, //!< PMRES with clauses.
    };
    //! Additional tactics for core-guided optimization.
    enum UscOption {
        usc_disjoint = 1u, //!< Enable (disjoint) preprocessing.
        usc_succinct = 2u, //!< Do not add redundant constraints.
        usc_stratify = 4u, //!< Enable stratification for weighted optimization.
    };
    //! Strategy for unsatisfiable-core shrinking.
    enum UscTrim {
        usc_trim_lin = 1u, //!< Shrinking with linear search SAT->UNSAT.
        usc_trim_inv = 2u, //!< Shrinking with inverse linear search UNSAT->SAT.
        usc_trim_bin = 3u, //!< Shrinking with binary search SAT->UNSAT.
        usc_trim_rgs = 4u, //!< Shrinking with repeated geometric sequence until UNSAT.
        usc_trim_exp = 5u, //!< Shrinking with exponential search until UNSAT.
        usc_trim_min = 6u, //!< Shrinking with linear search for subset minimal core.
    };
    //! Heuristic options common to all optimization strategies.
    enum Heuristic {
        heu_sign  = 1, //!< Use optimize statements in sign heuristic.
        heu_model = 2, //!< Apply model heuristic when optimizing.
    };
    constexpr OptParams(Type st = type_bb) : type(st) {}
    [[nodiscard]] bool supportsSplitting() const { return type != type_usc; }
    [[nodiscard]] bool hasOption(UscOption o) const { return (opts & static_cast<uint32_t>(o)) != 0u; }
    [[nodiscard]] bool hasOption(Heuristic h) const { return (heus & static_cast<uint32_t>(h)) != 0u; }
    uint32_t           type : 1  = type_bb; /*!< Optimization strategy (see Type).*/
    uint32_t           heus : 2  = 0;       /*!< Set of Heuristic values. */
    uint32_t           algo : 2  = 0;       /*!< Optimization algorithm (see BBAlgo/UscAlgo). */
    uint32_t           trim : 3  = 0;       /*!< Unsatisfiable-core shrinking (0=no shrinking). */
    uint32_t           opts : 4  = 0;       /*!< Set of usc options. */
    uint32_t           tLim : 5  = 0;       /*!< Limit core shrinking to 2^tLim conflicts (0=no limit). */
    uint32_t           kLim : 15 = 0;       /*!< Limit for algorithm K (0=dynamic limit). */
};

//! Parameter-Object for configuring a solver.
struct SolverParams : SolverStrategies {
    //! Supported forget options.
    enum Forget { forget_heuristic = 1u, forget_signs = 2u, forget_activities = 4u, forget_learnts = 8u };
    uint32_t prepare();
    //! Adds a lookahead post propagator to the given solver if requested.
    [[nodiscard]] bool addPropagator(Solver& s) const;
    //! Extended factor for decision heuristics.
    [[nodiscard]] auto createHeuristic(const HeuristicFactory& creator) const -> std::unique_ptr<DecisionHeuristic>;
    [[nodiscard]] bool forgetHeuristic() const { return Potassco::test_mask(forgetSet, forget_heuristic); }
    [[nodiscard]] bool forgetSigns() const { return Potassco::test_mask(forgetSet, forget_signs); }
    [[nodiscard]] bool forgetActivities() const { return Potassco::test_mask(forgetSet, forget_activities); }
    [[nodiscard]] bool forgetLearnts() const { return Potassco::test_mask(forgetSet, forget_learnts); }
    SolverParams&      setId(uint32_t sId) {
        id = sId;
        return *this;
    }
    HeuParams heuristic; /*!< Parameters for decision heuristic. */
    OptParams opt;       /*!< Parameters for optimization.       */
    // 64-bit
    uint32_t seed           = 1; /*!< Seed for the random number generator.  */
    uint32_t lookOps   : 16 = 0; /*!< Max. number of lookahead operations (0: no limit). */
    uint32_t lookType  : 2  = 0; /*!< Type of lookahead operations. */
    uint32_t loopRep   : 2  = 0; /*!< How to represent loops? */
    uint32_t acycFwd   : 1  = 0; /*!< Disable backward propagation in acyclicity checker. */
    uint32_t forgetSet : 4  = 0; /*!< What to forget on (incremental step). */
    uint32_t reserved  : 7  = 0;
};

struct RestartSchedule : ScheduleStrategy {
    using AvgType = MovingAvg::Type;
    enum Keep : uint32_t { keep_never = 0, keep_restart = 1, keep_block = 2, keep_always = 3 };
    //! Creates dynamic sequence.
    static RestartSchedule dynamic(uint32_t base, float k, uint32_t lim, AvgType fast, Keep keep, AvgType slow,
                                   uint32_t slowW);

    [[nodiscard]] bool isDynamic() const { return type == 3u; }
    // only valid if isDynamic() is true.
    [[nodiscard]] float    k() const { return grow; }
    [[nodiscard]] uint32_t lbdLim() const { return len; }
    [[nodiscard]] uint32_t adjustLim() const { return lbdLim() != UINT32_MAX ? 16000 : UINT32_MAX; }
    [[nodiscard]] AvgType  fastAvg() const;
    [[nodiscard]] AvgType  slowAvg() const;
    [[nodiscard]] uint32_t slowWin() const;
    [[nodiscard]] Keep     keepAvg() const;
};

//! Aggregates restart-parameters to configure restarts during search.
/*!
 * \see ScheduleStrategy
 */
struct RestartParams {
    enum SeqUpdate { seq_continue = 0, seq_repeat = 1, seq_disable = 2 };
    using Schedule = RestartSchedule;
    RestartParams();
    uint32_t                prepare(bool withLookback);
    void                    disable();
    [[nodiscard]] bool      disabled() const { return base() == 0; }
    [[nodiscard]] bool      local() const { return cntLocal != 0; }
    [[nodiscard]] SeqUpdate update() const { return static_cast<SeqUpdate>(upRestart); }
    [[nodiscard]] uint32_t  base() const { return rsSched.base; }
    Schedule                rsSched;
    struct Block {
        [[nodiscard]] double scale() const { return static_cast<double>(fscale) / 100.0; }
        uint32_t             window : 23; /**< Size of moving assignment average for blocking restarts (0: disable). */
        uint32_t             fscale : 9;  /**< Scaling factor for blocking restarts. */
        CLASP_ALIGN_BITFIELD(uint32_t)
        uint32_t first : 29;      /**< Disable blocking restarts for first conflicts. */
        uint32_t avg   : 3;       /**< Use avg strategy (see MovingAvg::Type) */
    } block;                      /**< Blocking restarts options. */
    uint32_t counterRestart : 16; /**< Apply counter implication bump every counterRestart restarts (0: disable). */
    uint32_t counterBump    : 16; /**< Bump factor for counter implication restarts. */
    CLASP_ALIGN_BITFIELD(uint32_t)
    uint32_t shuffle     : 14; /**< Shuffle program after shuffle restarts (0: disable). */
    uint32_t shuffleNext : 14; /**< Re-Shuffle program every shuffleNext restarts (0: disable). */
    uint32_t upRestart   : 2;  /**< How to update restart sequence after a model was found (one of SeqUpdate). */
    uint32_t cntLocal    : 1;  /**< Count conflicts globally or relative to current branch? */
};

//! Type for implementing Glucose-style dynamic restarts.
/*!
 * \see  G. Audemard, L. Simon. "Refining Restarts Strategies for SAT and UNSAT"
 * \note In contrast to Glucose's dynamic restarts, this class also implements a heuristic for
 *       dynamically adjusting the margin ratio K.
 */
struct DynamicLimit {
    using Keep = RestartSchedule::Keep;
    enum Type { lbd_limit, level_limit };
    //! Creates new limit with moving average of the given window size.
    DynamicLimit(float k, uint32_t window, MovingAvg::Type fast, Keep keep, MovingAvg::Type slow, uint32_t slowWin = 0,
                 uint32_t adjustLimit = 16000);
    DynamicLimit(const DynamicLimit&)            = delete;
    DynamicLimit& operator=(const DynamicLimit&) = delete;

    //! Resets adjust strategy and optionally the moving (fast) average.
    void resetAdjust(float k, Type type, uint32_t lim, bool resetAvg = false);
    //! Resets current run - depending on the Keep strategy this also clears the moving average.
    void block();
    //! Resets moving and global average.
    void reset();
    //! Adds an observation and updates the moving average. Typically called on conflict.
    void update(uint32_t conflictLevel, uint32_t lbd);
    //! Notifies this object about a restart.
    /*!
     * The function checks whether to adjust the active margin ratio and/or
     * whether to switch from LBD based to conflict level based restarts.
     *
     * \param maxLbd Threshold for switching between lbd and conflict level queue.
     * \param k Lower bound for margin ratio.
     */
    uint32_t restart(uint32_t maxLbd, float k);
    //! Returns the number of updates since last restart.
    [[nodiscard]] uint32_t runLen() const { return num_; }
    //! Returns whether it is time to restart.
    [[nodiscard]] bool reached() const {
        return runLen() >= avg_.win() && (movingAverage() * adjust.rk) > globalAverage();
    }
    struct {
        //! Returns the average restart length, i.e. number of conflicts between restarts.
        [[nodiscard]] double avgRestart() const { return ratio(samples, restarts); }

        uint32_t limit;    //!< Number of conflicts before an update is forced.
        uint32_t restarts; //!< Number of restarts since last update.
        uint32_t samples;  //!< Number of samples since last update.
        float    rk;       //!< LBD/CFL dynamic limit factor (typically < 1.0).
        Type     type;     //!< Dynamic limit based on lbd or conflict level.
    } adjust{};            //!< Data for dynamically adjusting margin ratio (rk).

    [[nodiscard]] double globalAverage() const { return global_.avg(adjust.type); }
    [[nodiscard]] double movingAverage() const { return avg_.get(); }

private:
    void resetRun(Keep k);
    struct Global {
        explicit Global(MovingAvg::Type type, uint32_t size = 0);
        //! Returns the global lbd or conflict level average.
        [[nodiscard]] double avg(Type t) const { return (t == lbd_limit ? lbd : cfl).get(); }
        void                 reset() {
            lbd.clear();
            cfl.clear();
        }
        MovingAvg lbd; //!< Moving average of lbds
        MovingAvg cfl; //!< Moving average of conflict levels
    } global_;         //!< Global lbd/conflict level data.
    MovingAvg avg_;    //!< (Fast) moving average.
    uint32_t  num_;    //!< Number of samples in this run.
    Keep      keep_;   //!< Strategy for keeping fast moving average.
};

//! Type for implementing Glucose-style blocking of restarts.
/*!
 * \see G. Audemard, L. Simon "Refining Restarts Strategies for SAT and UNSAT"
 * \see A. Biere, A. Froehlich "Evaluating CDCL Restart Schemes"
 */
struct BlockLimit {
    explicit BlockLimit(uint32_t windowSize, double rf = 1.4, MovingAvg::Type t = MovingAvg::Type::avg_ema);
    bool push(uint32_t nAssign) {
        avg.push(nAssign);
        return ++n >= next;
    }
    //! Returns the exponential moving average scaled by r.
    [[nodiscard]] double scaled() const { return avg.get() * r; }
    MovingAvg            avg;  //!< Moving average.
    uint64_t             next; //!< Enable once n >= next.
    uint64_t             n;    //!< Number of data points seen so far.
    uint32_t             inc;  //!< Block restart for next inc conflicts.
    float                r;    //!< Scale factor for moving average.
};

//! Reduce strategy used during solving.
/*!
 * A reduce strategy mainly consists of an algorithm and a scoring scheme
 * for measuring "activity" of learnt constraints.
 */
struct ReduceStrategy {
    //! Reduction algorithm to use during solving.
    enum Algorithm {
        reduce_linear = 0, //!< Linear algorithm from clasp-1.3.x.
        reduce_stable = 1, //!< Sort constraints by score but keep order in learnt db.
        reduce_sort   = 2, //!< Sort learnt db by score and remove fraction with the lowest score.
        reduce_heap   = 3  //!< Similar to reduce_sort but only partially sorts learnt db.
    };
    //! Score to measure "activity" of learnt constraints.
    enum Score {
        score_act  = 0, //!< Activity only: how often constraint is used during conflict analysis.
        score_lbd  = 1, //!< Use literal block distance as activity.
        score_both = 2  //!< Use activity and lbd together.
    };
    //! Strategy for estimating size of problem.
    enum EstimateSize {
        est_dynamic         = 0, //!< Dynamically decide whether to use number of variables or constraints.
        est_con_complexity  = 1, //!< Measure size in terms of constraint complexities.
        est_num_constraints = 2, //!< Measure size in terms of number constraints.
        est_num_vars        = 3  //!< Measure size in terms of number variable.
    };
    static uint32_t scoreAct(const ConstraintScore& sc) { return sc.activity(); }
    static uint32_t scoreLbd(const ConstraintScore& sc) { return (lbd_max + 1) - sc.lbd(); }
    static uint32_t scoreBoth(const ConstraintScore& sc) { return (sc.activity() + 1) * scoreLbd(sc); }
    static int      compare(Score sc, const ConstraintScore& lhs, const ConstraintScore& rhs) {
        int fs = 0;
        if (sc == score_act) {
            fs = static_cast<int>(scoreAct(lhs)) - static_cast<int>(scoreAct(rhs));
        }
        else if (sc == score_lbd) {
            fs = static_cast<int>(scoreLbd(lhs)) - static_cast<int>(scoreLbd(rhs));
        }
        return fs != 0 ? fs : static_cast<int>(scoreBoth(lhs)) - static_cast<int>(scoreBoth(rhs));
    }
    static uint32_t asScore(Score sc, const ConstraintScore& act) {
        if (sc == score_act) {
            return scoreAct(act);
        }
        if (sc == score_lbd) {
            return scoreLbd(act);
        }
        /*  sc == score_both*/ { return scoreBoth(act); }
    }
    constexpr ReduceStrategy() = default;

    uint32_t protect  : 7 = 0;  /*!< Protect nogoods whose lbd was reduced and is now <= freeze. */
    uint32_t glue     : 4 = 0;  /*!< Don't remove nogoods with lbd <= glue.    */
    uint32_t fReduce  : 7 = 75; /*!< Fraction of nogoods to remove in percent. */
    uint32_t fRestart : 7 = 0;  /*!< Fraction of nogoods to remove on restart. */
    uint32_t score    : 2 = 0;  /*!< One of Score.                             */
    uint32_t algo     : 2 = 0;  /*!< One of Algorithm.                         */
    uint32_t estimate : 2 = 0;  /*!< How to estimate problem size in init.     */
    uint32_t noGlue   : 1 = 0;  /*!< Do not count glue clauses in limit.       */
};

//! Aggregates parameters for the nogood deletion heuristic used during search.
/*!
 * - S:delCond {yes,no}
 * - no:del {0}[0]
 * - no:del | delCond in {no}
 * - deletion | delCond in {yes}
 * - del-* | delCond in {yes}
 * - {delCond=yes, del-grow=no, del-cfl=no}
 * .
 */
struct ReduceParams {
    ReduceParams()
        : cflSched(ScheduleStrategy::none())
        , growSched(ScheduleStrategy::def())
        , fInit(1.0f / 3.0f)
        , initRange(10, UINT32_MAX) {}
    void                   disable();
    uint32_t               prepare(bool withLookback);
    [[nodiscard]] Range32  sizeInit(const SharedContext& ctx) const;
    [[nodiscard]] uint32_t cflInit(const SharedContext& ctx) const;
    [[nodiscard]] uint32_t getBase(const SharedContext& ctx) const;
    [[nodiscard]] float    fReduce() const { return static_cast<float>(strategy.fReduce) / 100.0f; }
    [[nodiscard]] float    fRestart() const { return static_cast<float>(strategy.fRestart) / 100.0f; }
    static uint32_t        getLimit(uint32_t base, double f, const Range32& r);
    ScheduleStrategy       cflSched;             /**< Conflict-based deletion schedule.               */
    ScheduleStrategy       growSched;            /**< Growth-based deletion schedule.                 */
    ReduceStrategy         strategy;             /**< Strategy to apply during nogood deletion.       */
    float                  fInit;                /**< Initial limit. X = P*fInit clamped to initRange.*/
    float                  fMax{3.0f};           /**< Maximal limit. X = P*fMax  clamped to maxRange. */
    float                  fGrow{1.1f};          /**< Growth factor for db.                           */
    Range32                initRange;            /**< Allowed range for initial limit.                */
    uint32_t               maxRange{UINT32_MAX}; /**< Allowed range for maximal limit: [initRange.lo,maxRange]*/
    uint32_t               memMax{0};            /**< Memory limit in MB (0 = no limit).              */
};

//! Parameter-Object for grouping solve-related options.
/*!
 * \ingroup enumerator
 */
struct SolveParams {
    //! Creates a default-initialized object.
    /*!
     * The following parameters are used:
     * - restart      : quadratic: 100*1.5^k / no restarts after first solution
     * - deletion     : initial size: vars()/3, grow factor: 1.1, max factor: 3.0, do not reduce on restart
     * - randomization: disabled
     * - randomProp   : 0.0 (disabled)
     * .
     */
    SolveParams();
    uint32_t      prepare(bool withLookback);
    bool          randomize(Solver& s) const;
    RestartParams restart;
    ReduceParams  reduce;
    uint32_t      randRuns : 16;    /*!< Number of initial randomized-runs. */
    uint32_t      randConf : 16;    /*!< Number of conflicts comprising one randomized-run. */
    float         randProb;         /*!< Use random heuristic with given probability ([0,1]) */
    struct FwdCheck {               /*!< Options for (partial checks in) DLP-solving; */
        uint32_t highStep : 24 = 0; /*!< Init/inc high level when reached. */
        uint32_t highPct  : 7  = 0; /*!< Check on low + (high - low) * highPct/100  */
        uint32_t signDef  : 2  = 0; /*!< Default sign heuristic for atoms in disjunctions. */
    } fwdCheck;
};

class SharedContext;
class SatPreprocessor;

//! Parameters for (optional) Sat-preprocessing.
struct SatPreParams {
    enum Algo {
        sat_pre_no     = 0, /**< Disable sat-preprocessing.                            */
        sat_pre_ve     = 1, /**< Run variable elimination.                             */
        sat_pre_ve_bce = 2, /**< Run variable- and limited blocked clause elimination. */
        sat_pre_full   = 3, /**< Run variable- and full blocked clause elimination.    */
    };
    static SatPreprocessor*      create(const SatPreParams&);
    [[nodiscard]] constexpr bool clauseLimit(uint32_t nc) const { return limClause && nc > (limClause * 1000u); }
    [[nodiscard]] constexpr bool occLimit(uint32_t pos, uint32_t neg) const {
        return limOcc && pos > (limOcc - 1u) && neg > (limOcc - 1u);
    }
    [[nodiscard]] constexpr uint32_t bce() const { return type != sat_pre_no ? type - 1 : 0; }
    constexpr void                   disableBce() { type = std::min(type, static_cast<uint32_t>(sat_pre_ve)); }

    uint32_t type      : 2  = 0u;    /**< One of algo. */
    uint32_t limIters  : 11 = 0u;    /**< Max. number of iterations.                         (0=no limit)*/
    uint32_t limTime   : 12 = 0u;    /**< Max. runtime in sec, checked after each iteration. (0=no limit)*/
    uint32_t limFrozen : 7  = 0u;    /**< Run only if percent of frozen vars < maxFrozen.    (0=no limit)*/
    uint32_t limClause : 16 = 4000u; /**< Run only if \#clauses \< (limClause*1000)          (0=no limit)*/
    uint32_t limOcc    : 16 = 0u;    /**< Skip v, if \#occ(v) \>= limOcc && \#occ(~v) \>= limOcc.(0=no limit) */
};

//! Parameters for a SharedContext object.
struct ContextParams {
    //! How to handle short learnt clauses.
    enum ShortMode {
        short_implicit = 0, /*!< Share short learnt clauses via short implication graph. */
        short_explicit = 1, /*!< Do not use short implication graph. */
    };
    //! How to simplify short (learnt) clauses.
    enum ShortSimpMode {
        simp_no     = 0, /*!< No additional simplifications. */
        simp_learnt = 1, /*!< Drop duplicate learnt short clauses. */
        simp_all    = 2, /*!< Drop all duplicate short clauses. */
    };
    //! How to handle physical sharing of (explicit) constraints.
    enum ShareMode {
        share_no      = 0, /*!< Do not physically share constraints (use copies instead). */
        share_problem = 1, /*!< Share problem constraints but copy learnt constraints.    */
        share_learnt  = 2, /*!< Copy problem constraints but share learnt constraints.    */
        share_all     = 3, /*!< Share all constraints.                                    */
        share_auto    = 4, /*!< Use share_no or share_all depending on number of solvers. */
    };
    SatPreParams satPre;                         /*!< Preprocessing options.                    */
    uint8_t      shareMode : 3 = share_auto;     /*!< Physical sharing mode (one of ShareMode). */
    uint8_t      shortMode : 1 = short_implicit; /*!< One of ShortMode.                         */
    uint8_t      shortSimp : 2 = 0;              /*!< One of ShortSimpMode. */
    uint8_t      seed      : 1 = 1;              /*!< Apply new seed when adding solvers.       */
    uint8_t      hasConfig : 1 = 0;              /*!< Reserved for command-line interface.      */
    uint8_t      cliConfig     = 0;              /*!< Reserved for command-line interface.      */
    uint8_t      stats         = 0;              /*!< See SharedContext::enableStats().         */
};

//! Interface for configuring a SharedContext object and its associated solvers.
class Configuration {
public:
    using SolverOpts = SolverParams;
    using SearchOpts = SolveParams;
    using CtxOpts    = ContextParams;
    virtual ~Configuration();
    //! Prepares this configuration for the usage in the given context.
    virtual void prepare(SharedContext&) = 0;
    //! Returns the options for the shared context.
    [[nodiscard]] virtual const CtxOpts& context() const = 0;
    //! Returns the number of solver options in this config.
    [[nodiscard]] virtual uint32_t numSolver() const = 0;
    //! Returns the number of search options in this config.
    [[nodiscard]] virtual uint32_t numSearch() const = 0;
    //! Returns the solver options for the i-th solver to be attached to the SharedContext.
    [[nodiscard]] virtual const SolverOpts& solver(uint32_t i) const = 0;
    //! Returns the search options for the i-th solver of the SharedContext.
    [[nodiscard]] virtual const SearchOpts& search(uint32_t i) const = 0;

    //! Creates and sets the heuristic to be used in the given solver.
    virtual void setHeuristic(Solver& s) const = 0;
    //! Adds post propagators to the given solver.
    virtual bool addPost(Solver& s) const = 0;
    //! Returns the configuration with the given name or nullptr if no such config exists.
    /*!
     * The default implementation returns `this` if `n` is empty or one of "." or "/".
     * Otherwise, nullptr is returned.
     */
    virtual Configuration* config(const char* n);
};

//! Base class for user-provided configurations.
class UserConfiguration : public Configuration {
public:
    //! Adds a lookahead post propagator to the given solver if requested.
    /*!
     * The function adds a lookahead post propagator if indicated by
     * the solver's SolverParams.
     */
    bool addPost(Solver& s) const override;
    //! Returns the (modifiable) solver options for the i-th solver.
    virtual SolverOpts& addSolver(uint32_t i) = 0;
    //! Returns the (modifiable) search options for the i-th solver.
    virtual SearchOpts& addSearch(uint32_t i) = 0;
};

enum class ProjectMode { implicit = 0u, output = 1u, project = 2u };

//! Basic configuration for one or more SAT solvers.
class BasicSatConfig
    : public UserConfiguration
    , public ContextParams {
public:
    BasicSatConfig();
    void               prepare(SharedContext&) override;
    [[nodiscard]] auto context() const -> const CtxOpts& override { return *this; }
    [[nodiscard]] auto numSolver() const -> uint32_t override { return size32(solver_); }
    [[nodiscard]] auto numSearch() const -> uint32_t override { return size32(search_); }
    [[nodiscard]] auto solver(uint32_t i) const -> const SolverOpts& override { return solver_[i % solver_.size()]; }
    [[nodiscard]] auto search(uint32_t i) const -> const SearchOpts& override { return search_[i % search_.size()]; }
    void               setHeuristic(Solver& s) const override;
    SolverOpts&        addSolver(uint32_t i) override;
    SearchOpts&        addSearch(uint32_t i) override;

    virtual void reset();
    virtual void resize(uint32_t numSolver, uint32_t numSearch);

private:
    using SolverVec = PodVector_t<SolverOpts>;
    using SearchVec = PodVector_t<SearchOpts>;
    SolverVec solver_;
    SearchVec search_;
};
///////////////////////////////////////////////////////////////////////////////
// SearchLimits
///////////////////////////////////////////////////////////////////////////////
//! Parameter-Object for managing search limits.
struct SearchLimits {
    using LimitPtr = DynamicLimit*;
    using BlockPtr = BlockLimit*;
    uint64_t used  = 0;
    struct {
        uint64_t conflicts = UINT64_MAX; //!< Soft limit on number of conflicts for restart.
        LimitPtr dynamic   = nullptr;    //!< Use dynamic restarts based on lbd or conflict level.
        BlockPtr block     = nullptr;    //!< Optional strategy to increase restart limit.
        bool     local     = false;      //!< Apply conflict limit against active branch.
    } restart;                           //!< Restart limits.
    uint64_t conflicts = UINT64_MAX;     //!< Soft limit on number of conflicts.
    uint64_t memory    = UINT64_MAX;     //!< Soft memory limit for learnt lemmas (in bytes).
    uint32_t learnts   = UINT32_MAX;     //!< Limit on number of learnt lemmas.
};

//! Base class for solving related events.
struct SolveEvent : Event {
    template <typename DerivedT>
    SolveEvent(DerivedT* self, const Solver& s, Verbosity v) : Event(self, subsystem_solve, v)
                                                             , solver(&s) {}
    const Solver* solver;
};
struct Model;
//! Base class for handling results of a solve operation.
class ModelHandler {
public:
    virtual ~ModelHandler();
    virtual bool onModel(const Solver&, const Model&) = 0;
    virtual bool onUnsat(const Solver&, const Model&);
};
//! Type for storing the lower bound of a minimize statement.
struct LowerBound {
    [[nodiscard]] constexpr bool active() const { return bound != weight_sum_min; }
    uint32_t                     level = 0;
    Wsum_t                       bound = weight_sum_min;
};

} // namespace Clasp
