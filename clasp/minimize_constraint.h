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
#pragma once

/*!
 * \file
 * \brief Types and functions for implementing minimization constraints.
 */
#include <cassert>
#include <clasp/constraint.h>
#include <clasp/solver_strategies.h>

namespace Clasp {
class MinimizeConstraint;
class WeightConstraint;

//! Supported minimization modes.
/*!
 * \ingroup constraint
 * Defines the possible minimization modes used during solving.
 * If optimize is used, a valid candidate model is a solution that is
 * strictly smaller than all previous solutions. Otherwise,
 * solutions with costs no greater than a fixed bound are considered valid.
 */
enum class MinimizeMode {
    ignore    = 0, //!< Ignore optimize statements during solving.
    optimize  = 1, //!< Optimize via a decreasing bound.
    enumerate = 2, //!< Enumerate models with cost less or equal to a fixed bound.
    enum_opt  = 3, //!< Enumerate models with cost equal to optimum.
};

//! A type holding data (possibly) shared between a set of minimize constraints.
/*!
 * \ingroup shared_con
 */
class SharedMinimizeData {
public:
    using ThisType = SharedMinimizeData;
    //! A type to represent a weight at a certain level.
    /*!
     * Objects of this type are used to create sparse vectors of weights. E.g.
     * a weight vector (w1\@L1, w2\@L3, w3\@L5) is represented as \[\<L1,1,w1\>\<L3,1,w2\>\<L5,0,w3\>\],
     * where each \<level, next, weight\>-tuple is an object of type LevelWeight.
     */
    struct LevelWeight {
        LevelWeight(uint32_t l, Weight_t w) : level(l), next(0), weight(w) {}
        uint32_t level : 31; //!< The level of this weight.
        uint32_t next  : 1;  //!< Does this weight belong to a sparse vector of weights?
        Weight_t weight;     //!< The weight at this level.
    };
    //! A type for holding sparse vectors of level weights of a multi-level constraint.
    using WeightVec = PodVector_t<LevelWeight>;
    using PrioVec   = PodVector_t<Weight_t>;
    explicit SharedMinimizeData(SumView lhsAdjust, MinimizeMode m = MinimizeMode::optimize);
    //! Increases the reference count of this object.
    auto share() -> ThisType* {
        count_.add();
        return this;
    }
    //! Decreases the object's reference count and destroys it if reference count drops to 0.
    void release() {
        if (count_.release()) {
            destroy();
        }
    }
    //! Number of minimize statements contained in this constraint.
    [[nodiscard]] auto numRules() const -> uint32_t { return size32(adjust_); }
    [[nodiscard]] auto maxLevel() const -> uint32_t { return numRules() - 1; }
    static constexpr auto maxBound() -> Wsum_t { return weight_sum_max; }
    //! Returns the active minimization mode.
    [[nodiscard]] auto mode() const -> MinimizeMode { return mode_; }
    //! Returns true if optimization is active.
    [[nodiscard]] bool optimize() const { return optGen_ ? checkNext() : mode_ != MinimizeMode::enumerate; }
    //! Returns the lower bound of level x.
    [[nodiscard]] auto lower(uint32_t x) const -> Wsum_t;
    //! Returns the upper bound of level x.
    [[nodiscard]] auto upper(uint32_t x) const -> Wsum_t { return upper()[x]; }
    [[nodiscard]] auto upper() const -> const Wsum_t* { return &(up_ + (gCount_.load() & 1u))->front(); }
    //! Returns the sum of level x in the most recent model.
    [[nodiscard]] auto sum(uint32_t x) const -> Wsum_t { return sum()[x]; }
    [[nodiscard]] auto sum() const -> const Wsum_t* { return (mode_ != MinimizeMode::enumerate) ? upper() : up_[1].data(); }
    //! Returns the adjustment for level x.
    [[nodiscard]] auto adjust(uint32_t x) const -> Wsum_t { return adjust_[x]; }
    [[nodiscard]] auto adjust() const -> const Wsum_t* { return adjust_.data(); }
    //! Returns the current (adjusted and possibly tentative) optimum for level x.
    [[nodiscard]] auto optimum(uint32_t x) const -> Wsum_t;
    //! Returns the current (adjusted and possibly tentative) most relevant lower bound.
    [[nodiscard]] auto lowerBound() const -> LowerBound;
    //! Returns the highest level of the literal with the given index i.
    [[nodiscard]] auto level(uint32_t i) const -> uint32_t { return numRules() == 1 ? 0 : lw(lits[i])->level; }
    //! Returns the most important weight of the literal with the given index i.
    [[nodiscard]] auto weight(uint32_t i) const -> Weight_t { return numRules() == 1 ? lits[i].weight : lw(lits[i])->weight; }
    [[nodiscard]] auto generation() const -> uint32_t { return gCount_.load(); }
    //! Returns whether minimization should search for solutions with current or next smaller upper bound.
    [[nodiscard]] bool checkNext() const { return mode() != MinimizeMode::enumerate && generation() != optGen_; }
    /*!
     * \name interface for optimization
     * If not otherwise specified, the following functions shall not be called concurrently.
     */
    //@{

    //! Sets the enumeration mode and (optionally) an initial bound.
    /*!
     * \note If m is MinimizeMode::enumerate, the caller should always
     * set a bound. Otherwise, *all* solutions are considered valid.
     */
    bool setMode(MinimizeMode m, SumView bound = {});
    void resetBounds();

    //! Attaches a new minimize constraint to this data object.
    /*!
     * \param s      Solver in which the new minimize constraint should apply.
     * \param params Parameters to pass to the optimization strategy.
     * \param addRef If true, the ref count of the shared object is increased.
     *               Otherwise, the new minimize constraint inherits the reference to the shared object.
     */
    MinimizeConstraint* attach(Solver& s, const OptParams& params, bool addRef = true);

    //! Makes opt the new (tentative) optimum.
    /*!
     * \pre opt is a pointer to an array of size numRules()
     */
    auto setOptimum(const Wsum_t* opt) -> SumView;
    //! Marks the current tentative optimum as the final optimum.
    /*!
     * \note Once a final optimum is set, further calls to setOptimum()
     * are ignored until resetBounds() is called.
     */
    void markOptimal();
    //! Sets the lower bound of level lev to low.
    void setLower(uint32_t lev, Wsum_t low);
    //! Sets the lower bound of level lev to the maximum of low and the existing value lower(lev).
    /*!
     * \note This function is thread-safe, i.e., can be called safely from multiple threads.
     */
    auto incLower(uint32_t lev, Wsum_t low) -> Wsum_t;
    //@}

    /*!
     * \name Arithmetic functions on weights.
     */
    //@{
    //! Computes lhs += weight(lit).
    void add(Wsum_t* lhs, const WeightLiteral& lit) const {
        if (weights.empty()) {
            *lhs += lit.weight;
        }
        else {
            add(lhs, lw(lit));
        }
    }
    static void add(Wsum_t* lhs, const LevelWeight* w) {
        do { lhs[w->level] += w->weight; } while (w++->next);
    }
    //! Computes lhs -= weight(lit).
    void sub(Wsum_t* lhs, const WeightLiteral& lit, uint32_t& aLev) const {
        if (weights.empty()) {
            *lhs -= lit.weight;
        }
        else {
            sub(lhs, lw(lit), aLev);
        }
    }
    static void sub(Wsum_t* lhs, const LevelWeight* w, uint32_t& aLev);
    //! Returns (lhs + weight(lit)) > rhs
    bool imp(Wsum_t* lhs, const WeightLiteral& lit, const Wsum_t* rhs, uint32_t& lev) const {
        return weights.empty() ? (*lhs + lit.weight) > *rhs : imp(lhs, lw(lit), rhs, lev);
    }
    bool imp(Wsum_t* lhs, const LevelWeight* w, const Wsum_t* rhs, uint32_t& lev) const;
    //! Returns the weight of lit at level lev.
    [[nodiscard]] auto weight(const WeightLiteral& lit, uint32_t lev) const -> Weight_t {
        if (numRules() == 1) {
            return lit.weight * (lev == 0);
        }
        const auto* w = lw(lit);
        do {
            if (w->level == lev) {
                return w->weight;
            }
        } while (w++->next);
        return 0;
    }
    // NOLINTBEGIN(readability-convert-member-functions-to-static)
    struct IterSent {};
    [[nodiscard]] constexpr auto begin() const noexcept -> const WeightLiteral* { return lits; }
    [[nodiscard]] constexpr auto end() const noexcept -> IterSent { return {}; }
    friend bool operator==(const WeightLiteral* lhs, IterSent) { return isSentinel(lhs->lit); }
    // NOLINTEND(readability-convert-member-functions-to-static)

    //@}
private:
    using CounterType = mt::ThreadSafe<uint32_t>;
    using LowerType   = mt::ThreadSafe<Wsum_t>;
    using LowerPtr    = std::unique_ptr<LowerType[]>;
    SumVec       adjust_; // initial bound adjustments
    SumVec       up_[2];  // buffers for update via "double buffering"
    LowerPtr     lower_;  // (unadjusted) lower bound of constraint
    CounterType  lowPos_; // active lower bound idx
    MinimizeMode mode_;   // how to compare assignments?
    RefCount     count_;  // number of refs to this object
    CounterType  gCount_; // generation count - used when updating optimum
    uint32_t     optGen_; // generation of optimal bound
public:
    WeightVec weights; // sparse vectors of weights - only used for multi-level constraints
    PrioVec   prios;   // (optional): maps levels to original priorities
    POTASSCO_WARNING_BEGIN_RELAXED
    WeightLiteral lits[0]; // (shared) literals - terminated with lit_true()
    POTASSCO_WARNING_END_RELAXED
private:
    [[nodiscard]] auto lw(const WeightLiteral& wl) const -> const LevelWeight* {
        return &weights[static_cast<uint32_t>(wl.weight)];
    }
    ~SharedMinimizeData();
    void destroy() const;
};
//! Helper class for creating minimize constraints.
/*!
 * \ingroup constraint
 */
class MinimizeBuilder {
public:
    using SharedData = SharedMinimizeData;
    MinimizeBuilder();

    auto add(Weight_t prio, WeightLitView lits) -> MinimizeBuilder&;
    auto add(Weight_t prio, WeightLiteral lit) -> MinimizeBuilder&;
    auto add(Weight_t prio, Weight_t adjust) -> MinimizeBuilder&;
    auto add(const SharedData& minCon) -> MinimizeBuilder&;

    [[nodiscard]] bool empty() const;

    //! Creates a new data object from previously added minimize literals.
    /*!
     * The function creates a new minimize data object from
     * the previously added literals to minimize. The returned
     * object can be used to attach one or more MinimizeConstraints.
     * \param ctx A ctx object to be associated with the new minimize constraint.
     * \return A data object representing previously added minimize statements or nullptr if empty().
     * \pre !ctx.frozen()
     * \post empty()
     */
    auto build(SharedContext& ctx) -> SharedData*;

    //! Discards any previously added minimize literals.
    void clear();

private:
    struct MLit {
        MLit(const WeightLiteral& wl, Weight_t at) : lit(wl.lit), prio(at), weight(wl.weight) {}
        Literal  lit;
        Weight_t prio;
        Weight_t weight;
    };
    using LitVec = PodVector_t<MLit>;
    void        prepareLevels(const Solver& s, SumVec& adjustOut, WeightVec& priosOut);
    void        mergeLevels(SumVec& adjust, SharedData::WeightVec& weightsOut);
    auto createShared(SharedContext& ctx, SumView adjust, const SharedData::WeightVec* weights) -> SharedData*;
    LitVec      lits_;
};

//! Base class for implementing (multi-level) minimize statements.
/*!
 * \ingroup constraint
 * A solver contains at most one minimize constraint, but a minimize constraint
 * may represent several minimize statements. In that case, each minimize statement
 * has a unique level (starting at 0) and minimize statements with a lower level
 * have higher priority. Priorities are handled like in smodels, i.e. statements
 * with lower priority become relevant only if all statements with higher priority
 * currently have an optimal assignment.
 *
 * MinimizeConstraint supports two modes of operation: if mode is set to
 * optimize, solutions are considered optimal only if they are strictly smaller
 * than previous solutions. Otherwise, if mode is set to enumerate a
 * solution is valid if it is not greater than the initially set optimum.
 * Example:
 *  m0: {a, b}
 *  m1: {c, d}
 *  All models: {a, c,...}, {a, d,...} {b, c,...}, {b, d,...} {a, b,...}
 *  Mode = optimize: {a, c, ...} (m0 = 1, m1 = 1)
 *  Mode = enumerate and initial opt=1,1: {a, c, ...}, {a, d,...}, {b, c,...}, {b, d,...}
 *
 */
class MinimizeConstraint : public Constraint {
public:
    using SharedData  = SharedMinimizeData;
    using SharedDataP = const SharedData*;
    //! Returns a pointer to the shared representation of this constraint.
    [[nodiscard]] auto shared() const -> SharedDataP { return shared_; }
    //! Attaches this object to the given solver.
    virtual bool attach(Solver& s) = 0;
    //! Shall activate the minimize constraint by integrating bounds stored in the shared data object.
    virtual bool integrate(Solver& s) = 0;
    //! Shall relax this constraint (i.e. remove any bounds).
    /*!
     * If reset is true, shall also remove search-path related state.
     */
    virtual bool relax(Solver& s, bool reset) = 0;
    //! Shall commit the model in s to the shared data object.
    /*!
     * The return value indicates whether the model is valid w.r.t the
     * costs stored in the shared data object.
     */
    virtual bool handleModel(Solver& s) = 0;
    //! Shall handle the unsatisfiable path in s.
    virtual bool               handleUnsat(Solver& s, bool upShared, LitVec& restore) = 0;
    [[nodiscard]] virtual bool supportsSplitting() const { return true; }
    // base interface
    void        destroy(Solver*, bool) override;
    auto cloneAttach(Solver&) -> Constraint* override { return nullptr; }

protected:
    MinimizeConstraint(SharedData* s);
    ~MinimizeConstraint() override;
    bool        prepare(Solver& s, bool useTag);
    SharedData* shared_; // common shared data
    Literal     tag_;    // (optional) literal for tagging reasons
};

//! Minimization via branch and bound.
/*!
 * \ingroup constraint
 * The class supports both basic branch and bound as well as
 * hierarchical branch and bound (with or without varying step sizes).
 */
class DefaultMinimize : public MinimizeConstraint {
public:
    explicit DefaultMinimize(SharedData* d, const OptParams& params);
    // base interface
    //! Attaches the constraint to the given solver.
    /*!
     * \pre s.decisionLevel() == 0
     * \note If either MinimizeMode::enumOpt or hierarchical optimization
     * is active, s.sharedContext()->tagLiteral() shall be an unassigned literal.
     */
    bool attach(Solver& s) override;
    bool integrate(Solver& s) override { return integrateBound(s); }
    bool relax(Solver&, bool reset) override { return relaxBound(reset); }
    bool handleModel(Solver& s) override {
        commitUpperBound(s);
        return true;
    }
    bool handleUnsat(Solver& s, bool up, LitVec& out) override;
    // constraint interface
    auto propagate(Solver& s, Literal p, uint32_t& data) -> PropResult override;
    void       undoLevel(Solver& s) override;
    void       reason(Solver& s, Literal p, LitVec& lits) override;
    bool       minimize(Solver& s, Literal p, CCMinRecursive* r) override;
    void       destroy(Solver*, bool) override;
    // own interface
    [[nodiscard]] bool active() const { return *opt() != SharedData::maxBound(); }
    //! Number of minimize statements contained in this constraint.
    [[nodiscard]] auto numRules() const -> uint32_t { return size_; }
    //! Tries to integrate the next tentative bound into this constraint.
    /*!
     * Starting from the current optimum stored in the shared data object,
     * the function tries to integrate the next candidate bound into
     * this constraint.
     *
     * \return The function returns true if integration succeeded. Otherwise,
     * false is returned and s.hasConflict() is true.
     *
     * \note If integrateBound() failed, the bound of this constraint
     *       is relaxed. The caller has to resolve the conflict first
     *       and then integrateBound() shall be called again.
     *
     * \note The caller has to call s.propagate() to propagate any new information
     *       from the new bound.
     *
     * \note If the tag literal (if any) is not true, the minimize constraint first assumes it.
     */
    bool integrateBound(Solver& s);

    //! Sets the current local sum as the global optimum (upper bound).
    /*!
     * commitUpperBound() shall be called whenever the solver finds a model.
     * The current local sum is recorded as new optimum in the shared data object.
     * Once the local bound is committed, the function integrateBound() has to be
     * called in order to continue optimization.
     */
    void commitUpperBound(const Solver& s);
    //! Sets the current local upper bound as the lower bound of this constraint.
    /*!
     * commitLowerBound() shall be called on unsat. The function stores
     * the local upper bound as new lower bound in this constraint. If upShared is true,
     * the lower bound is also copied to the shared data object.
     *
     * Once the local bound is committed, the function integrateBound() has to be
     * called in order to continue optimization.
     * \return false if search-space is exceeded w.r.t this constraint.
     */
    bool commitLowerBound(Solver& s, bool upShared);

    //! Removes the local upper bound of this constraint and therefore disables it.
    /*!
     * If full is true, also removes search-path related state.
     */
    bool relaxBound(bool full = false);

    [[nodiscard]] bool more() const { return step_.lev != size_; }

    // FOR TESTING ONLY!
    [[nodiscard]] auto sum(uint32_t i, bool adjust) const -> Wsum_t { return sum()[i] + (adjust ? shared_->adjust(i) : 0); }

private:
    enum PropMode { propagate_new_sum, propagate_new_opt };
    struct UndoInfo;
    using Iter     = const WeightLiteral*;
    using BoundPtr = std::unique_ptr<Wsum_t[]>;
    using UndoPtr  = std::unique_ptr<UndoInfo[]>;
    ~DefaultMinimize() override;
    // bound operations
    [[nodiscard]] auto opt() const -> Wsum_t* { return bounds_.get(); }
    [[nodiscard]] auto sum() const -> Wsum_t* { return opt() + size_; }
    [[nodiscard]] auto temp() const -> Wsum_t* { return sum() + size_; }
    [[nodiscard]] auto end() const -> Wsum_t* { return temp() + size_; }
    void                  assign(Wsum_t* lhs, const Wsum_t* rhs) const;
    static bool           greater(Wsum_t* lhs, Wsum_t* rhs, uint32_t len, uint32_t& aLev);
    // propagation & undo
    [[nodiscard]] auto lastUndoLevel(const Solver& s) const -> uint32_t;
    [[nodiscard]] bool     litSeen(uint32_t i) const;
    bool                   propagateImpl(Solver& s, PropMode m);
    auto computeImplicationSet(const Solver& s, const WeightLiteral& it, uint32_t& undoPos) -> uint32_t;
    void                   pushUndo(Solver& s, uint32_t litIdx);
    [[nodiscard]] auto     viewUndo(const Solver& s, Literal p) const -> SpanView<UndoInfo>;
    bool                   updateBounds(bool applyStep);
    // step
    [[nodiscard]] auto stepLow() const -> Wsum_t& { return *(end() + step_.lev); }
    void                  stepInit(uint32_t n);
    BoundPtr              bounds_;  // [upper,sum,temp[,lower]]
    Iter                  pos_;     // position of literal to look at next
    UndoPtr               undo_;    // one "seen" flag for each literal +
    uint32_t              undoTop_; // undo stack holding assigned literals
    uint32_t              posTop_;  // stack of saved "look at" positions
    const uint32_t        size_;    // number of rules
    uint32_t              actLev_;  // first level to look at when comparing bounds
    struct Step {                   // how to reduce next tentative bound
        uint32_t size;              //   size of step
        uint32_t lev  : 30;         //   level on which step is applied
        uint32_t type : 2;          //   type of step (one of OptParams::BBAlgo)
    } step_{};
};

//! Minimization via unsat cores.
/*!
 * \ingroup constraint
 */
class UncoreMinimize : public MinimizeConstraint {
public:
    // constraint interface
    auto propagate(Solver& s, Literal p, uint32_t& data) -> PropResult override;
    void       reason(Solver& s, Literal p, LitVec& lits) override;
    void       destroy(Solver*, bool) override;
    bool       simplify(Solver& s, bool reinit = false) override;
    // base interface
    bool               attach(Solver& s) override;
    bool               integrate(Solver& s) override;
    bool               relax(Solver&, bool reset) override;
    bool               valid(Solver& s) override;
    bool               handleModel(Solver& s) override;
    bool               handleUnsat(Solver& s, bool up, LitVec& out) override;
    [[nodiscard]] bool supportsSplitting() const override { return false; }

private:
    friend class SharedMinimizeData;
    explicit UncoreMinimize(SharedData* d, const OptParams& params);
    using EnumPtr  = DefaultMinimize*;
    using BoundPtr = std::unique_ptr<Wsum_t[]>;
    struct LitData {
        LitData(Weight_t w, bool as, uint32_t c) : weight(w), coreId(c), assume(static_cast<uint32_t>(as)), flag(0u) {}
        Weight_t weight;
        uint32_t coreId : 30;
        uint32_t assume : 1;
        uint32_t flag   : 1;
    };
    struct LitPair {
        LitPair(Literal p, uint32_t dataId) : lit(p), id(dataId) {}
        Literal  lit;
        uint32_t id;
    };
    struct Core {
        Core(WeightConstraint* c, Weight_t b, Weight_t w) : con(c), bound(b), weight(w) {}
        [[nodiscard]] auto size() const -> uint32_t;
        [[nodiscard]] auto at(uint32_t i) const -> Literal;
        [[nodiscard]] auto tag() const -> Literal;
        WeightConstraint*      con;
        Weight_t               bound;
        Weight_t               weight;
    };
    struct WCTemp {
        using WLitVec = WeightLitVec;
        using Ptr     = WeightLiteral*;
        void start(Weight_t b) {
            lits.clear();
            bound = b;
        }
        void                   add(const Solver& s, Literal p);
        [[nodiscard]] bool     unsat() const { return bound > 0 && static_cast<uint32_t>(bound) > size32(lits); }
        [[nodiscard]] auto size() const -> uint32_t { return size32(lits); }
        Ptr                    data() { return lits.data(); }
        Weight_t               bound;
        WLitVec                lits;
    };
    using LitTable  = PodVector_t<LitData>;
    using CoreTable = PodVector_t<Core>;
    using ConTable  = PodVector_t<Constraint*>;
    using LitSet    = PodVector_t<LitPair>;
    using LitView   = SpanView<LitPair>;
    class Todo {
    public:
        Todo() = default;
        [[nodiscard]] auto size() const -> uint32_t { return size32(lits_); }
        [[nodiscard]] auto view() const -> LitView { return lits_; }
        [[nodiscard]] auto last(uint32_t n) const -> LitView { return {lits_.data() + (lits_.size() - n), n}; }
        [[nodiscard]] auto weight() const -> Weight_t { return minW_; }
        [[nodiscard]] bool     shrink() const { return next_ != 0u; }
        void                   clear(bool resetShrink = true);
        void                   add(const LitPair& x, Weight_t w);
        void                   terminate();
        bool                   shrinkNext(UncoreMinimize& self, Val_t result);
        void                   shrinkPush(UncoreMinimize& self, Solver& s);
        void                   shrinkReset();

    private:
        bool     subsetNext(UncoreMinimize& self, Val_t result);
        LitSet   lits_;
        Weight_t minW_ = weight_min;
        // shrinking
        uint32_t last_ = 0;
        uint32_t next_ = 0;
        uint32_t step_ = 0;
        LitSet   core_;
    };
    // literal and core management
    [[nodiscard]] static bool hasCore(const LitData& x) { return x.coreId != 0; }
    [[nodiscard]] bool        flagged(uint32_t id) const { return litData_[id - 1].flag != 0u; }
    void                      setFlag(uint32_t id, bool f) { litData_[id - 1].flag = static_cast<uint32_t>(f); }
    auto getData(uint32_t id) -> LitData& { return litData_[id - 1]; }

    auto getCore(const LitData& x) -> Core& { return open_[x.coreId - 1]; }
    auto newAssumption(Literal p, Weight_t w) -> LitPair;
    auto newLit(Solver& s) -> Literal;
    void     releaseLits();
    bool     addCore(Solver& s, LitView lits, Weight_t w, bool updateLower);
    auto allocCore(WeightConstraint* con, Weight_t bound, Weight_t weight, bool open) -> uint32_t;
    bool     closeCore(Solver& s, LitData& x, bool sat);
    bool     addOll(Solver& s, LitView lits, Weight_t w);
    bool     addOllCon(Solver& s, WCTemp& wc, Weight_t w);
    bool     addK(Solver& s, uint32_t k, LitView lits, Weight_t w);
    enum CompType { comp_disj = 0, comp_conj = 1 };
    bool addPmr(Solver& s, LitView lits, Weight_t w);
    bool addPmrCon(CompType t, Solver& s, Literal head, Literal body1, Literal body2);
    bool addConstraint(Solver& s, WeightLiteral* lits, uint32_t size, Weight_t bound);
    bool addImplication(Solver& s, Literal a, Literal b, bool concise);
    // algorithm
    void               init();
    auto initRoot(const Solver& s) -> uint32_t;
    bool               initLevel(Solver& s);
    auto analyze(Solver& s) -> uint32_t;
    bool               addNext(Solver& s, bool allowInit = true);
    bool               pushPath(Solver& s);
    bool               popPath(Solver& s, uint32_t dl);
    bool               fixLit(Solver& s, Literal p);
    bool               fixLevel(Solver& s);
    void               detach(Solver* s, bool b);
    bool               pushTrim(Solver& s);
    void               resetTrim(Solver& s);
    bool               push(Solver& s, Literal p, uint32_t id);
    auto computeSum(const Solver& s) const -> Wsum_t*; // NOLINT(modernize-use-nodiscard)
    [[nodiscard]] bool validLowerBound() const {
        Wsum_t cmp = lower_ - upper_;
        return cmp < 0 || (cmp == 0 && level_ == shared_->maxLevel() && not shared_->checkNext());
    }
    // data
    EnumPtr   enum_;       // for supporting (optimal) model enumeration in parallel mode
    BoundPtr  sum_;        // costs of active model
    LitTable  litData_;    // data for active literals (tag lits for cores + lits from active minimize)
    CoreTable open_;       // open cores, i.e. relaxable and referenced by an assumption
    ConTable  closed_;     // closed cores represented as weight constraints
    LitSet    assume_;     // current set of assumptions
    Todo      todo_;       // core(s) not yet represented as constraint
    LitVec    fix_;        // set of fixed literals
    LitVec    conflict_;   // temporary: conflicting set of assumptions
    WCTemp    temp_;       // temporary: used for creating weight constraints
    Wsum_t    lower_;      // lower bound of active level
    Wsum_t    upper_;      // upper bound of active level
    uint32_t  auxInit_;    // number of solver aux vars on attach
    uint32_t  auxAdd_;     // number of aux vars added for cores
    uint32_t  gen_;        // active generation
    uint32_t  level_ : 28; // active level
    uint32_t  next_  : 1;  // update because of model
    uint32_t  disj_  : 1;  // preprocessing active?
    uint32_t  path_  : 1;  // push path?
    uint32_t  init_  : 1;  // init constraint?
    Weight_t  actW_;       // active weight limit (only weighted minimization with stratification)
    Weight_t  nextW_;      // next weight limit   (only weighted minimization with stratification)
    uint32_t  eRoot_;      // saved root level of solver (initial gp)
    uint32_t  aTop_;       // saved assumption level (added by us)
    uint32_t  freeOpen_;   // head of open core free list
    OptParams options_;    // active options
};

} // end namespace Clasp
