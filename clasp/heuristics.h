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

/*!
 * \file
 * \brief Defines various decision heuristics to be used in clasp.
 */

#include <clasp/pod_vector.h>
#include <clasp/solver.h>
#include <clasp/util/indexed_priority_queue.h>
namespace Clasp {

//! Computes a moms-like score for var v.
uint32_t momsScore(const Solver& s, Var_t v);

//! A variant of the BerkMin decision heuristic from the BerkMin Sat-Solver.
/*!
 * \ingroup heuristic
 * \see E. Goldberg, Y. Navikov: "BerkMin: a Fast and Robust Sat-Solver"
 *
 * \note
 * This version of the BerkMin heuristic varies mostly in the following points from the original BerkMin:
 *  -# it considers loop-nogoods if requested (this is the default)
 *  -# it uses a MOMS-like heuristic as long as there are no conflicts (and therefore no activities)
 *  -# it uses a MOMS-like score to break ties whenever multiple variables from an unsatisfied learnt constraint have
 * equal activities
 *  -# it uses a lazy decaying scheme that only touches active variables
 */
class ClaspBerkmin : public DecisionHeuristic {
public:
    /*!
     * \note Checks at most params.param candidates when searching for not yet
     * satisfied learnt constraints. If param is 0, all candidates are checked.
     */
    explicit ClaspBerkmin(const HeuParams& params = HeuParams());
    void    setConfig(const HeuParams& params) override;
    void    startInit(const Solver& s) override;
    void    endInit(Solver& s) override;
    void    newConstraint(const Solver& s, LitView lits, ConstraintType t) override;
    void    updateReason(const Solver& s, LitView lits, Literal resolveLit) override;
    bool    bump(const Solver& s, WeightLitView lits, double adj) override;
    void    undo(const Solver&, LitView undo) override;
    void    updateVar(const Solver& s, Var_t v, uint32_t n) override;
    Literal doSelect(Solver& s) override;
    Literal selectRange(Solver& s, LitView range) override;

private:
    [[nodiscard]] Literal selectLiteral(const Solver& s, Var_t v, bool vsids) const;
    [[nodiscard]] bool    initHuang() const { return order_.score[0].occ == 1; }
    [[nodiscard]] bool    hasActivities() const { return order_.score[0].act != 0; }

    void  initHuang(bool b) { order_.score[0].occ = b; }
    void  hasActivities(bool b) { order_.score[0].act = b; }
    Var_t getMostActiveFreeVar(const Solver& s);
    Var_t getTopMoms(const Solver& s);
    bool  hasTopUnsat(const Solver& s);
    // Gathers heuristic information for one variable v.
    struct HScore {
        explicit HScore(uint32_t d = 0) : dec(static_cast<uint16_t>(d)) {}
        void incAct(uint32_t gd, bool h, bool sign) {
            occ += static_cast<int>(h) * (1 - (2 * static_cast<int>(sign)));
            decay(gd, h);
            ++act;
        }
        void     incOcc(bool sign) { occ += 1 - (2 * static_cast<int>(sign)); }
        uint32_t decay(uint32_t gd, bool h) {
            if (uint32_t x = (gd - dec)) {
                // NOTE: shifts might overflow, i.e.
                // activity is actually shifted by x%32.
                // We deliberately ignore this "logical inaccuracy"
                // and treat it as random noise ;)
                act >>= x;
                dec   = static_cast<uint16_t>(gd);
                occ  /= (1 << (x * static_cast<unsigned>(h)));
            }
            return act;
        }
        int32_t  occ{0};
        uint16_t act{0};
        uint16_t dec;
    };
    using Scores = PodVector_t<HScore>;
    using Pos    = VarVec::iterator;

    struct Order {
        Order()                        = default;
        Order(const Order&)            = delete;
        Order& operator=(const Order&) = delete;
        struct Compare {
            explicit Compare(Order* o) : self(o) {}
            bool operator()(Var_t v1, Var_t v2) const {
                return self->decayedScore(v1) > self->decayedScore(v2) ||
                       (self->score[v1].act == self->score[v2].act && v1 < v2);
            }
            Order* self;
        };
        uint32_t              decayedScore(Var_t v) { return score[v].decay(decay, huang); }
        [[nodiscard]] int32_t occ(Var_t v) const { return score[v].occ; }
        void                  inc(Literal p, bool inNant) {
            if (not this->nant || inNant) {
                score[p.var()].incAct(decay, huang, p.sign());
            }
        }
        void incOcc(Literal p) { score[p.var()].incOcc(p.sign()); }
        int  compare(Var_t v1, Var_t v2) {
            return static_cast<int>(decayedScore(v1)) - static_cast<int>(decayedScore(v2));
        }
        void     resetDecay();
        Scores   score;        // For each var v score_[v] stores heuristic score of v
        uint32_t decay{0};     // "global" decay counter. Increased every decP_ decisions
        bool     huang{false}; // Use Huang's scoring scheme (see: Jinbo Huang: "A Case for Simple SAT Solvers")
        bool     nant{false};  // only score vars v with varInfo(v).nant()?
        uint8_t  resScore{3u};
    } order_;
    VarVec   cache_;         // Caches the most active variables
    LitVec   freeLits_;      // Stores free variables of the last learnt conflict clause that is not sat
    LitVec   freeOtherLits_; // Stores free variables of the last other learnt nogood that is not sat
    uint32_t topConflict_;   // Index into learnt db used when searching for conflict clauses that are not sat
    uint32_t topOther_;      // Index into learnt db used when searching for other learnt nogoods that are not sat
    Var_t    front_;         // First variable whose truth-value is not already known - reset on backtracking
    Pos      cacheFront_;    // First unprocessed cache position - reset on backtracking
    uint32_t cacheSize_;     // Cache at most cacheSize_ variables
    uint32_t numVsids_;      // Number of consecutive vsids-based decisions
    uint32_t maxBerkmin_;    // When searching for an open learnt constraint, check at most maxBerkmin_ candidates.
    TypeSet  types_;         // When searching for an open learnt constraint, consider these types of nogoods.
    Rng      rng_;
};

//! Variable Move To Front decision strategies inspired by Siege.
/*!
 * \ingroup heuristic
 * \see Lawrence Ryan: "Efficient Algorithms for Clause Learning SAT-Solvers"
 *
 * \note This implementation of VMTF differs from the original implementation in three points:
 *  - it optionally moves to the front a selection of variables from learnt loop nogoods
 *  - it measures variable activity by using a BerkMin-like score scheme
 *  - the initial order of the var list is determined using a MOMs-like score scheme
 */
class ClaspVmtf : public DecisionHeuristic {
public:
    /*!
     * \note Moves at most params.param literals from constraints used during
     *  conflict resolution to the front. If params.param is 0, the default is
     *  to move up to 8 literals.
     */
    explicit ClaspVmtf(const HeuParams& params = HeuParams());
    void    setConfig(const HeuParams& params) override;
    void    startInit(const Solver& s) override;
    void    endInit(Solver&) override;
    void    newConstraint(const Solver& s, LitView lits, ConstraintType t) override;
    void    updateReason(const Solver& s, LitView lits, Literal resolveLit) override;
    bool    bump(const Solver& s, WeightLitView lits, double adj) override;
    void    simplify(const Solver&, LitView) override;
    void    undo(const Solver&, LitView undo) override;
    void    updateVar(const Solver& s, Var_t v, uint32_t n) override;
    Literal doSelect(Solver& s) override;
    Literal selectRange(Solver& s, LitView range) override;

private:
    [[nodiscard]] Var_t getNext(Var_t v) const { return score_[v].next; }
    [[nodiscard]] Var_t getFront() const { return score_[0].next; }

    void addToList(Var_t v);
    void removeFromList(Var_t v);
    void moveToFront(Var_t v);

    struct VarInfo {
        [[nodiscard]] bool inList() const { return prev != next; }
        uint32_t&          activity(uint32_t globalDecay) {
            if (uint32_t x = globalDecay - decay; x) {
                act   >>= (x << 1);
                decay   = globalDecay;
            }
            return act;
        }
        Var_t    prev{0};  // link to prev node in intrusive linked list
        Var_t    next{0};  // link to next node in intrusive linked list
        uint32_t act{0};   // activity of var - initially 0
        int32_t  occ{0};   // which literal of var occurred more often in learnt constraints?
        uint32_t decay{0}; // counter for lazy decaying activity
    };
    using Score = PodVector_t<VarInfo>;

    struct LessLevel {
        LessLevel(const Solver& s, const Score& sc) : s_(s), sc_(sc) {}
        bool operator()(Var_t v1, Var_t v2) const {
            return s_.level(v1) < s_.level(v2) || (s_.level(v1) == s_.level(v2) && sc_[v1].act > sc_[v2].act);
        }
        bool operator()(Literal l1, Literal l2) const { return (*this)(l1.var(), l2.var()); }

    private:
        const Solver& s_;
        const Score&  sc_;
    };
    Score    score_;       // For each var v score_[v] stores heuristic score of v
    VarVec   mtf_;         // Vars to be moved to the front of vars_
    Var_t    front_{0};    // Current front in var list - reset on backtracking
    uint32_t decay_{0};    // "Global" decay counter. Increased every 512 decisions
    uint32_t nMove_{8};    // Limit on number of vars to move
    TypeSet  types_;       // Type of nogoods to score during resolution
    uint32_t scType_{0};   // Type of scoring
    uint32_t nList_{0};    // Num vars in vmtf-list
    bool     nant_{false}; // only move vars v with varInfo(v).nant()?
};

//! Score type for VSIDS heuristic.
/*!
 * \see ClaspVsids
 */
struct VsidsScore {
    using Score = VsidsScore;
    explicit VsidsScore(double sc = 0.0) : value(sc) {}
    [[nodiscard]] double get() const { return value; }
    bool                 operator>(const Score& o) const { return value > o.value; }
    void                 set(double f) { value = f; }
    template <typename C>
    static double applyFactor(C&, Var_t, double f) {
        return f;
    }
    double value; // activity
};

//! A variable state independent decision heuristic favoring variables that were active in recent conflicts.
/*!
 * \ingroup heuristic
 * \see M. W. Moskewicz, C. F. Madigan, Y. Zhao, L. Zhang, and S. Malik:
 * "Chaff: Engineering an Efficient SAT Solver"
 *
 * \note By default, the implementation uses the exponential VSIDS scheme from MiniSAT and
 * applies a MOMs-like score scheme to get an initial var order.
 */
template <typename ScoreType>
class ClaspVsidsBase : public DecisionHeuristic {
public:
    /*!
     * \note Uses params.param to init the decay value d and inc factor 1.0/d.
     * If params.param is 0, d is set 0.95. Otherwise, d is set to 0.x, where x is params.param.
     */
    explicit ClaspVsidsBase(const HeuParams& params = HeuParams());
    void setConfig(const HeuParams& params) override;
    void startInit(const Solver& s) override;
    void endInit(Solver&) override;
    void newConstraint(const Solver& s, LitView lits, ConstraintType t) override;
    void updateReason(const Solver& s, LitView lits, Literal resolveLit) override;
    bool bump(const Solver& s, WeightLitView lits, double adj) override;
    void undo(const Solver&, LitView undo) override;
    void simplify(const Solver&, LitView) override;
    void updateVar(const Solver& s, Var_t v, uint32_t n) override;

    Literal doSelect(Solver& s) override;
    Literal selectRange(Solver& s, LitView range) override;

protected:
    using ScoreVec = PodVector_t<ScoreType>;
    using OccVec   = PodVector_t<int32_t>;
    virtual void initScores(Solver& s, bool moms);

    [[nodiscard]] int occ(Var_t v) const { return occ_[v]; }

    void updateVarActivity(const Solver& s, Var_t v, double f = 1.0);
    void incOcc(Literal p) { occ_[p.var()] += 1 - (static_cast<int>(p.sign()) << 1); }
    void normalize();
    struct CmpScore {
        explicit CmpScore(const ScoreVec& s) : sc_(s) {}
        bool operator()(Var_t v1, Var_t v2) const { return sc_[v1] > sc_[v2]; }

    private:
        const ScoreVec& sc_;
    };
    using VarOrder = bk_lib::indexed_priority_queue<Var_t, CmpScore>;
    struct DynDecay {
        double   curr{0.0};
        double   stop{0.0};
        uint32_t bump{0};
        uint16_t freq{0};
        uint16_t next{0};
    };
    ScoreVec score_;        // vsids score for each variable
    OccVec   occ_;          // occurrence balance of each variable
    VarOrder vars_;         // priority heap of variables
    DynDecay dyn_;          // dynamic decaying strategy
    double   decay_{1.25};  // active decay factor for evsids (>= 1.0)
    double   inc_{1.0};     // var bump for evsids or conflict index for acids (increased on conflict)
    TypeSet  types_;        // set of constraints to score
    uint32_t scType_{0};    // score type (one of HeuParams::Score)
    bool     acids_{false}; // whether to use acids instead if evsids scoring
    bool     nant_{false};  // whether bumps are restricted to vars v with varInfo(v).nant()
};
using ClaspVsids = ClaspVsidsBase<VsidsScore>;

//! Score type for DomainHeuristic.
/*!
 * \see DomainHeuristic
 */
struct DomScore : VsidsScore {
    static constexpr uint32_t dom_max = (1u << 30) - 1;
    using Score                       = DomScore;
    explicit DomScore(double v = 0.0) : VsidsScore(v) {}
    bool operator>(const Score& o) const { return (level > o.level) || (level == o.level && value > o.value); }
    [[nodiscard]] bool isDom() const { return domP != dom_max; }
    void               setDom(uint32_t key) { domP = key; }
    template <typename C>
    static double applyFactor(C& sc, Var_t v, double f) {
        int16_t df = sc[v].factor;
        return df == 1 ? f : static_cast<double>(df) * f;
    }
    int16_t  level{0};            // priority level
    int16_t  factor{1};           // factor used when bumping activity
    uint32_t domP : 30 {dom_max}; // index into dom-table if dom var
    uint32_t sign : 1 {0};        // whether v has a sign modification
    uint32_t init : 1 {0};        // whether value is from init modification
};

//! A VSIDS heuristic supporting additional domain knowledge.
/*!
 * \ingroup heuristic
 *
 * \see M. Gebser, B. Kaufmann, R. Otero, J. Romero, T. Schaub, P. Wanko:
 *      "Domain-specific Heuristics in Answer Set Programming",
 *      https://www.cs.uni-potsdam.de/wv/publications/DBLP_conf/aaai/GebserKROSW13.pdf
 */
class DomainHeuristic
    : public ClaspVsidsBase<DomScore>
    , private Constraint {
public:
    using BaseType = ClaspVsidsBase<DomScore>;
    explicit DomainHeuristic(const HeuParams& params = HeuParams());
    ~DomainHeuristic() override;
    void                          setDefaultMod(HeuParams::DomMod mod, uint32_t prefSet);
    void                          setConfig(const HeuParams& params) override;
    void                          startInit(const Solver& s) override;
    [[nodiscard]] const DomScore& score(Var_t v) const { return score_[v]; }

protected:
    // base interface
    Literal doSelect(Solver& s) override;
    void    initScores(Solver& s, bool moms) override;
    void    detach(Solver& s) override;
    // Constraint interface
    Constraint* cloneAttach(Solver&) override { return nullptr; }
    void        reason(Solver&, Literal, LitVec&) override {}
    PropResult  propagate(Solver&, Literal, uint32_t&) override;
    void        undoLevel(Solver& s) override;

private:
    struct DomAction {
        static constexpr uint32_t undo_nil = (1u << 31) - 1;
        uint32_t                  var  : 30; // dom var to be modified
        uint32_t                  mod  : 2;  // modification to apply
        uint32_t                  undo : 31; // next action in undo list
        uint32_t                  next : 1;  // next action belongs to same condition?
        int16_t                   bias;      // value to apply
        uint16_t                  prio;      // prio of modification
    };
    struct DomPrio {
        void      clear() { prio[0] = prio[1] = prio[2] = prio[3] = 0; }
        uint16_t  operator[](unsigned i) const { return prio[i]; }
        uint16_t& operator[](unsigned i) { return prio[i]; }
        uint16_t  prio[4];
    };
    struct Frame {
        Frame(uint32_t lev, uint32_t h) : dl(lev), head(h) {}
        uint32_t dl;
        uint32_t head;
    };
    struct VarScore {
        Var_t  var{};
        double score{};
    };
    using ActionVec   = PodVector_t<DomAction>;
    using PrioVec     = PodVector_t<DomPrio>;
    using FrameVec    = PodVector_t<Frame>;
    using DomMod      = DomainTable::ValueType;
    using VarScoreVec = PodVector_t<VarScore>;

    uint32_t  addDomAction(const DomMod& e, Solver& s, VarScoreVec& outInit, Literal& lastW);
    void      addDefAction(Solver& s, Literal x, int16_t lev, uint32_t domKey);
    void      pushUndo(uint32_t& head, uint32_t actionId);
    void      applyAction(Solver& s, DomAction& act, uint16_t& oldPrio);
    uint16_t& prio(Var_t v, uint32_t mod) { return prios_[score_[v].domP][mod]; }
    PrioVec   prios_;   // priorities for domain vars
    ActionVec actions_; // dynamic modifications
    FrameVec  frames_;  // dynamic undo information
    uint32_t  domSeen_; // offset into domain table
    uint32_t  defMax_;  // max var with default modification
    uint16_t  defMod_;  // default modifier
    uint16_t  defPref_; // default preferences
};
} // namespace Clasp
