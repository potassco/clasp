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
#include <clasp/minimize_constraint.h>

namespace Clasp {
class Solver;
class SharedContext;
class OutputTable;
class Enumerator;
class EnumerationConstraint;

//! Type for storing a model.
struct Model {
    enum Type { sat = 0u, brave = 1u, cautious = 2u, user = 4u };
    enum : uint32_t { cons_mask = 3u, est_mask = 4u };
    static constexpr auto        estMask(Literal p) -> uint8_t { return est_mask << static_cast<int>(p.sign()); }
    [[nodiscard]] constexpr bool hasVar(Var_t v) const { return v < values.size(); }
    [[nodiscard]] constexpr bool hasCosts() const { return not costs.empty(); }
    //! True if this model stores current (cautious/brave) consequences.
    [[nodiscard]] constexpr bool consequences() const { return Potassco::test_any(type, cons_mask); }
    //! For sat models, value of v in model. Otherwise, undefined.
    [[nodiscard]] constexpr auto value(Var_t v) const -> Val_t {
        assert(hasVar(v));
        return values[v] & 3u;
    }
    //! True if p is true in model or part of current consequences.
    [[nodiscard]] constexpr bool isTrue(Literal p) const { return Potassco::test_any(value(p.var()), trueValue(p)); }
    //! True if p is part of a definite answer.
    [[nodiscard]] constexpr bool isDef(Literal p) const {
        return isTrue(p) && (def || not Potassco::test_any(type, cautious) || not isEst(p));
    }
    //! True if p is part of the current estimate of consequences.
    [[nodiscard]] constexpr bool isEst(Literal p) const {
        assert(hasVar(p.var()));
        return not def && Potassco::test_any(values[p.var()], estMask(p));
    }
    //! State of p wrt current consequences or undefined if `consequences()` is false.
    /*!
     * \return `value_true` if `p` is a definite consequence, `value_false` if it is not a consequence, and
     *         `value_free` if the state is still unknown.
     */
    [[nodiscard]] constexpr auto isCons(Literal p) const -> Val_t {
        return isEst(p) ? value_free : isTrue(p) ? value_true : value_false;
    }

    //! Number of consequences and estimates in the current model.
    /*!
     * If consequences() is true, returns a pair `ret`, such that
     * - `ret.first`  is the number of definite consequences, and
     * - `ret.second` is the number of remaining possible consequences.
     */
    [[nodiscard]] auto numConsequences(const SharedContext& problem) const -> std::pair<uint32_t, uint32_t>;
    [[nodiscard]] auto numConsequences(const OutputTable& problem) const -> std::pair<uint32_t, uint32_t>;

    //! Visits shown symbols that are true in this model.
    /*!
     * For model of type `sat`, the function invokes the given `visitor` for all true literals in the model.
     * For a `brave`/`cautious` model, the function invokes the given `visitor` for:
     * - true literals that are definite, followed by
     * - true literals in the current estimate.
     */
    template <typename OutputT, std::invocable<typename OutputT::Type, Literal, const char*> VisitorT>
    void visitWitness(const OutputT& out, VisitorT&& visitor,
                      typename OutputT::TypeSet types = OutputT::all_types) const {
        const bool onlyD = type != cautious || def;
        for (bool definite = true;; definite = not definite) {
            if (auto wt = OutputT::type_pred; types.contains(wt)) {
                for (const auto& pred : out.pred_range()) {
                    if (isTrue(pred.cond) && (onlyD || isDef(pred.cond) == definite)) {
                        visitor(wt, lit_true, pred.name.c_str());
                    }
                }
            }
            if (auto wt = OutputT::type_var; not out.vars_range().empty() && types.contains(wt)) {
                const bool showNeg = not consequences();
                if (out.projectMode() == ProjectMode::output || not out.filter("_")) {
                    for (auto v : out.vars_range()) {
                        if (auto p = posLit(v); (showNeg || isTrue(p)) && (onlyD || isDef(p) == definite)) {
                            visitor(wt, isTrue(p) ? p : ~p, nullptr);
                        }
                    }
                }
                else {
                    for (auto lit : out.proj_range()) {
                        if ((showNeg || isTrue(lit)) && (onlyD || isDef(lit) == definite)) {
                            visitor(wt, isTrue(lit) ? lit : ~lit, nullptr);
                        }
                    }
                }
            }
            if (definite == onlyD) {
                for (const auto& theory : out.theory_range()) {
                    if (auto wt = theory->type(); types.contains(wt)) {
                        for (const char* x = theory->first(*this); x; x = theory->next()) { visitor(wt, lit_true, x); }
                    }
                }
                return;
            }
        }
    }

    uint64_t          num = 0;       // running number of this model
    const Enumerator* ctx = nullptr; // ctx in which model was found
    ValueView         values;        // variable assignment or consequences
    SumView           costs;         // associated costs (or empty if not applicable)
    LowerBound        lower;         // associated lower bound (only active if applicable)
    uint32_t          sId  : 16 = 0; // id of solver that found the model
    uint32_t          type : 10 = 0; // type of model
    uint32_t          opt  : 1  = 0; // whether the model is optimal w.r.t costs (0: unknown)
    uint32_t          def  : 1  = 0; // whether the model is definite w.r.t consequences (0: unknown)
    uint32_t          sym  : 1  = 0; // whether symmetric models are possible
    uint32_t          up   : 1  = 0; // whether the model was updated on last unsat
    uint32_t          fin  : 1  = 0; // final model of the active reasoning step
    uint32_t          lb   : 1  = 0; // whether the lower bound was updated on last unsat
};

/**
 * \defgroup enumerator Solving
 * \brief Enumerators and solve algorithms.
 */
//@{

//! Options for configuring enumeration.
struct EnumOptions {
    using OptMode  = MinimizeMode;
    using ProjMode = ProjectMode;
    using EnumPtr  = std::unique_ptr<Enumerator>;
    enum EnumType {
        enum_auto         = 0,
        enum_bt           = 1,
        enum_record       = 2,
        enum_dom_record   = 3,
        enum_consequences = 4,
        enum_brave        = 5,
        enum_cautious     = 6,
        enum_query        = 7,
        enum_user         = 8
    };
    EnumOptions() = default;
    static auto        createModelEnumerator(const EnumOptions& opts) -> EnumPtr;
    static auto        createConsEnumerator(const EnumOptions& opts) -> EnumPtr;
    static auto        nullEnumerator() -> EnumPtr;
    static auto        createEnumerator(const EnumOptions& opts) -> EnumPtr;
    [[nodiscard]] bool consequences() const { return (enumMode & enum_consequences) != 0; }
    [[nodiscard]] bool models() const { return (enumMode < enum_consequences); }
    [[nodiscard]] bool optimize() const { return Potassco::test(optMode, MinimizeMode::optimize); }
    int64_t            numModels{-1};                   /*!< Number of models to compute. */
    EnumType           enumMode{enum_auto};             /*!< Enumeration type to use.     */
    OptMode            optMode{MinimizeMode::optimize}; /*!< Optimization mode to use.    */
    ProjMode           proMode{ProjectMode::implicit};  /*!< Projection mode to use.      */
    uint32_t           project{0};                      /*!< Options for projection.      */
    SumVec             optBound;                        /*!< Initial bound for optimize statements. */
    SumVec             optStop;                         /*!< Optional stop bound for optimization. */
};
auto modelType(const Model& m) -> const char*;

//! Interface for supporting enumeration of models.
/*!
 * Enumerators are global w.r.t a solve algorithm. That is,
 * even if the solve algorithm itself uses a parallel search, there
 * shall be only one enumerator, and it is the user's responsibility
 * to protect the enumerator with appropriate locking.
 *
 * Concrete enumerators must implement a function for preparing a problem for enumeration
 * and an EnumerationConstraint to be added to each solver attached to the problem.
 * It is then the job of the actual solve algorithm to commit models to the enumerator
 * and to integrate new information into attached solvers via appropriate calls to
 * Enumerator::update().
 */
class Enumerator {
public:
    using ConPtr    = EnumerationConstraint*;
    using ConRef    = EnumerationConstraint&;
    using Minimizer = const SharedMinimizeData*;
    using OptMode   = EnumOptions::OptMode;
    class SharedQueue;
    explicit Enumerator();
    virtual ~Enumerator();
    Enumerator(Enumerator&&) = delete;

    void reset();

    //! Prepares the problem for enumeration.
    /*!
     * The function shall be called once before search is started and before SharedContext::endInit()
     * was called. It freezes enumeration-related variables and adds a suitable enumeration constraint
     * to the master solver.
     *
     * \pre The problem is not yet frozen, i.e. SharedContext::endInit() was not yet called.
     * \param problem The problem on which this enumerator should work.
     * \param opt     Minimization mode to apply during enumeration.
     * \param limit   Optional hint on max number of models to compute.
     *
     * \note In the incremental setting, init() must be called once for each incremental step.
     */
    int init(SharedContext& problem, OptMode opt = MinimizeMode::optimize, int limit = 0);

    //! Prepares the given solver for enumeration under the given path.
    /*!
     * The function shall be called once before solving is started. It pushes the
     * given path to the solver by calling Solver::pushRoot() and prepares s for
     * enumeration/optimization.
     * \return true if path was added.
     */
    bool start(Solver& s, LitView path = {}, bool disjointPath = false) const;

    //! Updates the given solver with enumeration-related information.
    /*!
     * The function is used to integrate enumeration-related information,
     * like minimization bounds or previously committed models, into the search space of s.
     * It shall be called after each commit.
     *
     * \param s The solver to update.
     * \note The function is concurrency-safe, i.e. can be called
     *       concurrently by different solvers.
     */
    bool update(Solver& s) const;

    /*!
     * \name Commit functions.
     * Functions for committing enumeration-related information to the enumerator.
     * \note The functions in this group are *not* concurrency-safe, i.e. in a parallel search
     *       at most one solver shall call a commit function at any one time.
     */
    //@{

    //! Commits the model stored in the given solver.
    /*!
     * If the model is valid and unique, the function returns true and the
     * model can be accessed via a call to Enumerator::lastModel().
     * Otherwise, the function returns false.
     * In either case, Enumerator::update(s) shall be called
     * in order to continue search for further models.
     *
     * \pre The solver's assignment is total.
     */
    bool commitModel(Solver& s);
    //! Expands the next symmetric model if any.
    bool commitSymmetric(Solver& s);
    //! Returns whether there is a next symmetric model not yet committed.
    [[nodiscard]] bool hasSymmetric(const Solver& s) const;
    //! Commits an unsatisfiable path stored in the given solver.
    /*!
     * The return value determines how search should proceed.
     * If true is returned, the enumerator has relaxed an enumeration constraint
     * and search may continue after a call to Enumerator::update(s).
     * Otherwise, the search shall be stopped.
     */
    bool commitUnsat(Solver& s);
    //! Commits the given clause to this enumerator.
    bool commitClause(LitView clause) const; // NOLINT(modernize-use-nodiscard)
    //! Marks current enumeration phase as completed.
    /*!
     * If the enumerator was initialized with a minimization constraint and
     * optimization mode MinimizeMode::enumOpt, the optimal bound is committed,
     * the enumerator is prepared for enumerating optimal models, and the function
     * returns false. Otherwise, the function returns true and search shall be stopped.
     */
    bool commitComplete();
    //! Commits the state stored in the given solver.
    /*!
     * Calls commitModel() or commitUnsat() depending on the state of `s`.
     * The function returns `value_true`, to signal that `s` stores a valid and
     * unique model, `value_false` to signal that search shall be stopped, and
     * `value_free` otherwise.
     * \see commitModel()
     * \see commitUnsat()
     */
    auto commit(Solver& s) -> Val_t;
    //@}

    //! Removes from s the path that was passed to start() and any active (minimization) bound.
    void end(Solver& s) const;
    //! Returns the number of models enumerated so far.
    [[nodiscard]] auto enumerated() const -> uint64_t { return model_.num; }
    //! Returns the last model enumerated.
    /*!
     * \note If enumerated() is equal to 0, the returned object is in an indeterminate state.
     */
    [[nodiscard]] auto lastModel() const -> const Model& { return model_; }
    //! Returns the most recently updated lower bound (if any).
    /*!
     * \note If optimize() is false, the returned bound is always inactive.
     */
    [[nodiscard]] auto lowerBound() const -> LowerBound;
    //! Returns whether optimization is active.
    [[nodiscard]] bool optimize() const { return mini_ && mini_->mode() != MinimizeMode::enumerate && model_.opt == 0; }
    //! Returns whether computed models are still tentative.
    [[nodiscard]] bool tentative() const { return mini_ && mini_->mode() == MinimizeMode::enum_opt && model_.opt == 0; }
    //! Returns the active minimization constraint if any.
    [[nodiscard]] auto minimizer() const -> Minimizer { return mini_; }
    //! Returns the type of models this enumerator computes.
    [[nodiscard]] virtual int modelType() const { return Model::sat; }
    enum UnsatType {
        unsat_stop = 0u, /*!< First unsat stops search - commitUnsat() always return false.     */
        unsat_cont = 1u, /*!< Unsat may be tentative - commitUnsat() may return true.           */
    };
    //! Returns whether unsat may be tentative and requires synchronization.
    [[nodiscard]] virtual int unsatType() const;
    //! Returns whether this enumerator supports full restarts once a model was found.
    [[nodiscard]] virtual bool supportsRestarts() const { return true; }
    //! Returns whether this enumerator supports parallel search.
    [[nodiscard]] virtual bool supportsParallel() const { return true; }
    //! Returns whether this enumerator supports splitting-based search.
    [[nodiscard]] virtual bool supportsSplitting(const SharedContext& problem) const;
    //! Returns whether this enumerator requires exhaustive search to produce a definite answer.
    [[nodiscard]] virtual bool exhaustive() const { return mini_ && mini_->mode() != MinimizeMode::enumerate; }
    //! Sets whether the search path stored in s is disjoint from all others.
    void setDisjoint(Solver& s, bool b) const;
    //! Sets whether symmetric models should be ignored.
    void setIgnoreSymmetric(bool b);
    //! Clears the update state of the last model.
    void clearUpdate();

protected:
    //! Shall prepare the enumerator and freeze any enumeration-related variable.
    /*!
     * \return A prototypical enumeration constraint to be used in a solver.
     */
    virtual auto doInit(SharedContext& ctx, SharedMinimizeData* min, int numModels) -> ConPtr = 0;
    virtual void doReset();

private:
    using QueuePtr = std::unique_ptr<SharedQueue>;

    void updateLower(const LowerBound& lb);

    SharedMinimizeData* mini_ = nullptr;
    QueuePtr            queue_;
    ValueVec            values_;
    SumVec              costs_;
    LitVec              sym_;
    Model               model_{};
};

//! A solver-local (i.e. thread-local) constraint to support enumeration.
/*!
 * An enumeration constraint is used to extract/store enumeration-related information
 * from models.
 */
class EnumerationConstraint : public Constraint {
public:
    using ConPtr   = EnumerationConstraint*;
    using MinPtr   = MinimizeConstraint*;
    using QueuePtr = Enumerator::SharedQueue*;
    //! Returns true if search-path is disjoint from all others.
    [[nodiscard]] bool disjointPath() const { return disjoint_; }
    [[nodiscard]] auto state() const -> Val_t { return state_; }
    //! Returns true if optimization is active.
    [[nodiscard]] bool optimize() const;
    [[nodiscard]] auto minimizer() const -> MinPtr { return mini_; }
    // Methods used by enumerator
    void init(Solver& s, SharedMinimizeData* min, QueuePtr q);
    bool start(Solver& s, LitView path, bool disjoint);
    void end(Solver& s);
    bool update(Solver& s);
    void setDisjoint(bool x);
    bool integrateBound(Solver& s);
    bool integrateNogoods(Solver& s);
    bool commitModel(Enumerator& ctx, Solver& s);
    bool commitUnsat(Enumerator& ctx, Solver& s);
    void setMinimizer(MinPtr min) { mini_ = min; }
    void add(Constraint* c);
    void modelHeuristic(Solver& s);
    bool extractModel(Solver& s, ValueVec& out);

protected:
    EnumerationConstraint();
    ~EnumerationConstraint() override;
    // base interface
    void destroy(Solver* s, bool detach) override;
    auto propagate(Solver&, Literal, uint32_t&) -> PropResult override { return PropResult(true, true); }
    void reason(Solver&, Literal, LitVec&) override {}
    bool simplify(Solver& s, bool reinit) override;
    bool valid(Solver& s) override;
    auto cloneAttach(Solver& s) -> Constraint* override;
    // own interface
    virtual auto       clone() -> ConPtr   = 0;
    virtual bool       doUpdate(Solver& s) = 0;
    virtual void       doCommitModel(Enumerator&, Solver&) {}
    virtual void       doCommitUnsat(Enumerator&, Solver&) {}
    virtual bool       doExtractModel(Solver& s, ValueVec& out, bool sat);
    [[nodiscard]] auto rootLevel() const -> uint32_t { return root_; }

private:
    struct QueueReader;
    using QPtr                = std::unique_ptr<QueueReader>;
    MinimizeConstraint* mini_ = nullptr;
    QPtr                queue_;
    ConstraintVec       nogoods_;
    LitVec              next_;
    uint32_t            root_{0};
    Val_t               state_{value_free};
    uint8_t             heuristic_{0};
    bool                disjoint_{false};
};
//@}
} // namespace Clasp
