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

#include <clasp/shared_context.h>
#include <clasp/solver_strategies.h>
#include <clasp/solver_types.h>

namespace Clasp {

/**
 * \file
 * \defgroup solver Solver
 * \brief %Solver and related classes.
 */
//@{

//! clasp's Solver class.
/*!
 * A Solver-object maintains the state and provides the functions
 * necessary to implement our CDNL-algorithm.
 *
 * The interface supports incremental solving (search under assumptions) as well as
 * solution enumeration. To make this possible the solver maintains two special
 * decision levels: the root-level and the backtrack-level.
 *
 * The root-level is the lowest decision level to which a search
 * can return. Conflicts on the root-level are non-resolvable and end a search - the
 * root-level therefore acts as an artificial top-level during search.
 * Incremental solving is then implemented by first adding a list of unit assumptions
 * and second initializing the root-level to the current decision level.
 * Once search terminates assumptions can be undone by calling clearAssumptions
 * and a new a search can be started using different assumptions.
 *
 * For model enumeration the solver maintains a backtrack-level that restricts
 * backjumping in order to prevent repeating already enumerated solutions.
 * The solver will never backjump above that level and conflicts on the backtrack-level
 * are resolved by backtracking, i.e. flipping the corresponding decision literal.
 *
 * \see "Conflict-Driven Answer Set Enumeration" for a detailed description of this approach.
 *
 */
class Solver {
public:
    using ConstraintDB = PodVector_t<Constraint*>;
    using DBRef        = const ConstraintDB&;

private:
    friend class SharedContext;
    using AlwaysTrue = decltype([](const void*) { return true; });
    // Creates an empty solver object with all strategies set to their default value.
    Solver(SharedContext* ctx, uint32_t id);
    ~Solver();
    // Resets a solver object to the state it had after construction.
    void reset();
    void resetConfig();
    void startInit(uint32_t constraintGuess, const SolverParams& params);
    void updateVars();
    bool cloneDB(const ConstraintDB& db);
    bool preparePost();
    bool endInit();
    bool endStep(uint32_t top, const SolverParams& params);

public:
    using SearchMode    = SolverStrategies::SearchStrategy;
    using UpdateMode    = SolverStrategies::UpdateMode;
    using WatchInitMode = SolverStrategies::WatchInit;
    //! Returns a pointer to the shared context object of this solver.
    const SharedContext* sharedContext() const { return shared_; }
    //! Returns a pointer to the sat-preprocessor used by this solver.
    SatPreprocessor* satPrepro() const;
    //! Returns the solver's solve parameters.
    const SolveParams& searchConfig() const;
    SearchMode         searchMode() const { return static_cast<SearchMode>(strategy_.search); }
    UpdateMode         updateMode() const { return static_cast<UpdateMode>(strategy_.upMode); }
    WatchInitMode      watchInitMode() const { return static_cast<WatchInitMode>(strategy_.initWatches); }
    uint32_t           compressLimit() const { return strategy_.compress ? strategy_.compress : UINT32_MAX; }
    bool               restartOnModel() const { return strategy_.restartOnModel; }
    DecisionHeuristic* heuristic() const { return heuristic_; }
    uint32_t           id() const { return strategy_.id; }
    VarInfo            varInfo(Var_t v) const { return shared_->validVar(v) ? shared_->varInfo(v) : VarInfo(); }
    const OutputTable& outputTable() const { return shared_->output; }
    Literal            tagLiteral() const { return tag_; }
    bool               isMaster() const { return this == sharedContext()->master(); }
    /*!
     * \name Setup functions.
     * Functions in this group are typically used before a search is started.
     * @{ */
    //! Adds the problem constraint c to the solver.
    /*!
     * Problem constraints shall only be added to the master solver of
     * a SharedContext object and only during the setup phase.
     * \pre this == sharedContext()->master() && !sharedContext()->frozen().
     */
    void add(Constraint* c);
    //! Adds a suitable representation of the given clause to the solver.
    /*!
     * Depending on the type and size of the given clause, the function
     * either adds a (learnt) constraint to this solver or an implication
     * to the shared implication graph.
     * \note If c is a problem clause, the precondition of add(Constraint* c) applies.
     */
    bool add(const ClauseRep& c, bool isNew = true);
    //! Returns whether c can be stored in the shared short implication graph.
    bool allowImplicit(const ClauseRep& c) const {
        return c.isImp() ? shared_->allowImplicit(c.info.type()) && not c.info.aux() &&
                               (c.prep == 1 || (not auxVar(c.lits[0].var()) && not auxVar(c.lits[1].var()) &&
                                                (c.size == 2 || not auxVar(c.lits[2].var()))))
                         : c.size <= 1;
    }
    //! Returns the first post propagator with the given priority or nullptr if no such post propagator exists.
    auto getPost(uint32_t prio) const -> PostPropagator*;
    //! Returns the first post propagator that matches the given predicate or nullptr if no such post propagator exists.
    template <typename Pred>
    requires(std::is_invocable_r_v<bool, Pred, PostPropagator*>)
    auto getPost(const Pred& pred, uint32_t maxPrio = UINT32_MAX) const -> PostPropagator* {
        return post_.find(pred, maxPrio);
    }
    //! Returns the first post propagator with type `T` or nullptr if no such post propagator exists.
    template <typename T, typename Pred = AlwaysTrue>
    requires(std::is_base_of_v<PostPropagator, T> && std::is_invocable_r_v<bool, Pred, T*>)
    auto getPost(const Pred& pred = Pred{}, uint32_t prio = UINT32_MAX) const -> T* {
        if constexpr (requires { T::prio; }) {
            prio = prio == UINT32_MAX ? static_cast<uint32_t>(T::prio) : prio;
        }
        return static_cast<T*>(post_.find(
            [&](PostPropagator* x) {
                auto* tx = dynamic_cast<T*>(x);
                return tx && pred(tx);
            },
            prio));
    }
    //! Adds p as post propagator to this solver.
    /*!
     * \pre p was not added previously and is not part of any other solver.
     * \note Post propagators are stored and called in priority order.
     * \see PostPropagator::priority()
     */
    bool addPost(PostPropagator* p);
    //! Removes p from the solver's list of post propagators.
    /*!
     * \note The function shall not be called during propagation of any other post propagator.
     */
    void removePost(PostPropagator* p);

    //! Adds path to the current root-path and adjusts the root-level accordingly.
    bool pushRoot(LitView path, bool pushStep = false);
    bool pushRoot(Literal p);
    void setEnumerationConstraint(Constraint* c);
    //! Requests a special aux variable for tagging conditional knowledge.
    /*!
     * Once a tag variable t is set, learnt clauses containing ~t are
     * tagged as "conditional". Conditional clauses are removed once t becomes
     * unassigned or Solver::removeConditional() is called. Furthermore, calling
     * Solver::strengthenConditional() removes ~t from conditional clauses and
     * transforms them to unconditional knowledge.
     *
     * \note Typically, the tag variable is a root assumption and hence true during
     *       the whole search.
     */
    Var_t pushTagVar(bool pushToRoot);
    //@}

    /*!
     * \name CDNL functions
     * Top level functions that are important to the CDNL algorithm.
     * @{ */

    //! Searches for a model as long as the given limit is not reached.
    /*!
     * The function searches for a model as long as none of the limits given by limit
     * is reached. The limits are updated during search.
     *
     * \param limit Imposed limit on conflicts and number of learnt constraints.
     * \param randf Pick next decision variable randomly with a probability of randf.
     * \return
     *  - value_true: if a model was found.
     *  - value_false: if the problem is unsatisfiable (under assumptions, if any).
     *  - value_free: if search was stopped because limit was reached.
     *  .
     *
     * \note search treats the root level as top-level, i.e. it will never backtrack below that level.
     */
    Val_t search(SearchLimits& limit, double randf = 0.0);
    Val_t search(uint64_t maxC = UINT64_MAX, uint32_t maxL = UINT32_MAX, bool local = false, double rp = 0.0);

    //! Moves the root-level 'n' levels down (i.e. away from the top-level).
    /*!
     * The root-level is similar to the top-level in that it cannot be
     * undone during search, i.e. the solver will not resolve conflicts that are on or
     * above the root-level.
     */
    void pushRootLevel(uint32_t n = 1) {
        levels_.root = std::min(decisionLevel(), levels_.root + n);
        levels_.flip = std::max(levels_.flip, levels_.root);
    }

    //! Moves the root-level 'n' levels up (i.e. towards the top-level).
    /*!
     * The function removes all levels between the new root level and the current decision level,
     * resets the current backtrack-level, and re-assigns any implied literals.
     * \param      n      Number of root decisions to pop.
     * \param[out] popped Optional storage for popped root decisions.
     * \param      aux    Whether aux variables should be added to @c popped.
     * \post decisionLevel() == rootLevel()
     * \note The function first calls clearStopConflict() to remove any stop conflicts.
     * \note The function *does not* propagate any asserted literals. It is
     *       the caller's responsibility to call propagate() after the function returned.
     */
    bool popRootLevel(uint32_t n = 1, LitVec* popped = nullptr, bool aux = true);

    //! Removes a previously set stop conflict and restores the root level.
    void clearStopConflict();

    //! Returns the current root level.
    uint32_t rootLevel() const { return levels_.root; }

    //! Removes any implications made between the top-level and the root-level.
    /*!
     * The function also resets the current backtrack-level and re-assigns learnt facts.
     * \note
     *   Equivalent to popRootLevel(rootLevel()) followed by simplify().
     */
    bool clearAssumptions();

    //! Adds c as a learnt constraint to the solver.
    void addLearnt(Constraint* c, uint32_t size, ConstraintType type) {
        learnts_.push_back(c);
        stats.addLearnt(size, type);
    }
    void addLearnt(Constraint* c, uint32_t size) { addLearnt(c, size, c->type()); }
    //! Tries to receive at most maxOut clauses.
    /*!
     * The function queries the distributor object for new clauses to be delivered to
     * this solver. Clauses are stored in out.
     * \return The number of clauses received.
     */
    uint32_t receive(SharedLiterals** out, uint32_t maxOut) const;
    //! Distributes the clause in lits via the distributor.
    /*!
     * The function first calls the distribution strategy
     * to decides whether the clause is a valid candidate for distribution.
     * If so and a distributor was set, it distributes the clause and returns a handle to the
     * now shared literals of the clause. Otherwise, it returns 0.
     *
     * \param lits  The literals of the clause.
     * \param extra Additional information about the clause.
     * \note
     *   If the return value is not null, it is the caller's
     *   responsibility to release the returned handle (i.e. by calling release()).
     * \note If the clause contains aux vars, it is not distributed.
     */
    SharedLiterals* distribute(LitView lits, const ConstraintInfo& extra);

    //! Returns to the maximum of rootLevel() and backtrackLevel() and increases the number of restarts.
    void restart();

    enum UndoMode : uint32_t {
        undo_default        = 0u,
        undo_pop_bt_level   = 1u,
        undo_pop_proj_level = 2u,
        undo_save_phases    = 4u
    };
    //! Sets the backtracking level to dl.
    /*!
     * Depending on mode, the backtracking level either applies
     * to normal or projective solution enumeration.
     * \see "Solution Enumeration for Projected Boolean Search Problems".
     */
    void setBacktrackLevel(uint32_t dl, UndoMode mode = undo_pop_bt_level) {
        if (Potassco::to_underlying(mode) >= levels_.mode) {
            levels_.flip = std::max(std::min(dl, decisionLevel()), rootLevel());
            levels_.mode = std::max(mode & 3u, Potassco::to_underlying(undo_pop_bt_level));
        }
    }
    //! Returns the current backtracking level.
    uint32_t backtrackLevel() const { return levels_.flip; }
    //! Returns the backjump level during an undo operation.
    uint32_t jumpLevel() const { return decisionLevel() - levels_.jump; }

    //! Returns whether the solver can split-off work.
    bool splittable() const;
    //! Notifies the solver about a split request.
    /*!
     * \return splittable()
     */
    bool requestSplit();
    //! Clears last split request and returns true if there was an open request.
    bool clearSplitRequest();

    //! Tries to split-off disjoint work from the solver's current guiding path and returns it in out.
    /*!
     * On split, any open split request is also cleared.
     * \return splittable()
     */
    bool split(LitVec& out);

    //! Copies the solver's current guiding path to gp.
    /*!
     * \note The solver's guiding path consists of:
     *   - the decisions from levels [1, rootLevel()]
     *   - any literals that are implied on a level <= rootLevel() because of newly learnt
     *     information. This particularly includes literals that were flipped during model enumeration.
     *
     * \param[out] out Where to store the guiding path.
     */
    void copyGuidingPath(LitVec& out);

    //! If called on top-level, removes SAT-clauses + Constraints for which Constraint::simplify returned true.
    /*!
     * \note If this method is called on a decision-level > 0, it is a noop and will
     * simply return true.
     * \return false, if a top-level conflict is detected. Otherwise, true.
     */
    bool simplify();
    //! Shuffle constraints upon next simplification.
    void shuffleOnNextSimplify() { shufSimp_ = 1; }

    //! Removes all conditional knowledge, i.e. all previously tagged learnt clauses.
    /*!
     * \see Solver::pushTagVar()
     */
    void removeConditional();

    //! Resolves all tagged clauses with the tag literal and thereby strengthens the learnt db.
    /*!
     * \see Solver::pushTagVar()
     */
    void strengthenConditional();

    //! Sets the literal p to true and schedules p for propagation.
    /*!
     * Setting a literal p to true means assigning the appropriate value to
     * p's variable. That is: value_false if p is a negative literal and value_true
     * if p is a positive literal.
     * \param p The literal that should become true.
     * \param a The reason for the literal to become true or 0 if no reason exists.
     *
     * \return
     *  - false if p is already false
     *  - otherwise true.
     *
     * \pre hasConflict() == false
     * \pre a.isNull() == false || decisionLevel() <= rootLevel() || searchMode() == no_learning
     * \post
     *  p.var() == trueValue(p) || p.var() == falseValue(p) && hasConflict() == true
     *
     * \note if setting p to true leads to a conflict, the nogood that caused the
     * conflict can be requested using the conflict() function.
     */
    bool force(const Literal& p, const Antecedent& a) {
        assert(not hasConflict() || isTrue(p));
        if (assign_.assign(p, decisionLevel(), a)) {
            return true;
        }
        setConflict(p, a, UINT32_MAX);
        return false;
    }
    /*!
     * \overload bool Solver::force(const Literal&, const Antecedent&)
     */
    bool force(const Literal& p, const Antecedent& a, uint32_t data) {
        return data != UINT32_MAX ? assign_.assign(p, decisionLevel(), a, data) || (setConflict(p, a, data), false)
                                  : force(p, a);
    }

    //! Assigns p at dl because of r.
    /*!
     * \pre dl <= decisionLevel()
     * \note
     *   If dl < ul = max(rootLevel(), backtrackLevel()), p is actually assigned
     *   at ul but the solver stores enough information to reassign
     *   p on backtracking.
     */
    bool force(Literal p, uint32_t dl, const Antecedent& r, uint32_t d = UINT32_MAX) {
        return dl == decisionLevel() ? force(p, r, d) : force(ImpliedLiteral(p, dl, r, d));
    }
    //! Assigns p as a fact at decision level 0.
    bool force(Literal p) { return force(p, 0, Antecedent(lit_true)); }

    //! Assumes the literal p if possible.
    /*!
     * If p is currently unassigned, sets p to true and starts a new decision level.
     * \pre validVar(p.var()) == true
     * \param p The literal to assume.
     * \return !isFalse(p)
     */
    bool assume(const Literal& p);

    //! Selects and assumes the next branching literal by calling the installed decision heuristic.
    /*!
     * \pre queueSize() == 0
     * \note The next decision literal will be selected randomly with probability f.
     * \return
     *  - true if the assignment is not total and a literal was assumed (or forced).
     *  - false otherwise
     *  .
     * \see DecisionHeuristic
     */
    bool decideNextBranch(double f = 0.0);

    //! Sets a conflict that forces the solver to terminate its search.
    /*!
     * \pre  !hasConflict()
     * \post hasConflict()
     *
     * \note
     *   To prevent the solver from resolving the stop conflict, the
     *   function sets the root level to the current decision level.
     *   Call clearStopConflict() to remove the conflict and to restore
     *   the previous root-level.
     */
    void setStopConflict();

    /*!
     * Propagates all enqueued literals. If a conflict arises during propagation
     * propagate returns false and the current conflict (as a set of literals)
     * is stored in the solver's conflict variable.
     * \pre !hasConflict()
     * \see Solver::force
     * \see Solver::assume
     * \note Shall not be called recursively.
     */
    bool propagate();

    /*!
     * Does unit propagation and calls x->propagateFixpoint(*this)
     * for all post propagators x up to but not including p.
     * \note The function is meant to be called only in the context of p.
     * \pre  p is a post propagator of this solver, i.e. was previously added via addPost().
     * \pre  Post propagators are active, i.e. the solver is fully initialized.
     */
    bool propagateUntil(PostPropagator* p);

    /*!
     * Calls x->propagateFixpoint(*this) for all post propagators x starting from and including p.
     * \note The function is meant to be called only in the context of p.
     * \pre  p is a post propagator of this solver, i.e. was previously added via addPost().
     * \pre  Post propagators are active, i.e. the solver is fully initialized.
     * \pre  Assignment is fully (unit) propagated up to p.
     */
    bool propagateFrom(const PostPropagator* p);

    //! Executes a one-step lookahead on p.
    /*!
     * Assumes p and propagates this assumption. If propagations leads to
     * a conflict, false is returned. Otherwise, the assumption is undone and
     * the function returns true.
     * \param p The literal to test.
     * \param c The constraint that wants to test p (can be 0).
     * \pre p is free
     * \note If c is not null and testing p does not lead to a conflict,
     *       c->undoLevel() is called *before* p is undone. Hence, the
     *       range [s.levelStart(s.decisionLevel()), s.assignment().size())
     *       contains p followed by all literals that were forced because of p.
     * \note propagateUntil(c) is used to propagate p.
     */
    bool test(Literal p, PostPropagator* c);

    //! Estimates the number of assignments following from setting p to true.
    /*!
     * \note For the estimate only binary clauses are considered.
     */
    uint32_t estimateBCP(Literal p, int maxRecursionDepth = 5) const;

    //! Computes the number of in-edges for each assigned literal.
    /*!
     * \pre  !hasConflict()
     * \note For a literal p assigned on level(p), only in-edges from
     *       levels < level(p) are counted.
     * \return The maximum number of in-edges.
     */
    uint32_t inDegree(WeightLitVec& out);
    //! Bumps var activities of assigned variables based on their in-degree.
    /*!
     * Let `vMax` be the assigned variable with the highest in-degree `maxIn = inDegree(vMax)`.
     * Bumps all assigned variables `v` by `inDegree(v) * bump/maxIn`.
     */
    void counterBumpVars(uint32_t bump);

    struct DBInfo {
        uint32_t size;
        uint32_t locked;
        uint32_t pinned;
    };
    //! Removes upto remMax percent of the learnt nogoods.
    /*!
     * \param remMax  Fraction of nogoods to remove ([0.0,1.0]).
     * \param rs      Strategy to apply during nogood deletion.
     * \return        The number of locked and active/glue clauses currently exempt from deletion.
     * \note
     *   Nogoods that are the reason for a literal to be in the assignment
     *   are said to be locked and won't be removed.
     */
    DBInfo reduceLearnts(double remMax, const ReduceStrategy& rs = ReduceStrategy());

    //! Resolves the active conflict using the selected strategy.
    /*!
     * If searchMode() is set to learning, resolveConflict implements
     * First-UIP learning and backjumping. Otherwise, it simply applies
     * chronological backtracking.
     * \pre hasConflict()
     * \return
     *  - true if the conflict was successfully resolved
     *  - false otherwise
     * \note
     *  If decisionLevel() == rootLevel() false is returned.
     */
    bool resolveConflict();

    //! Backtracks the last decision and updates the backtrack-level if necessary.
    /*!
     * \return
     *  - true if backtracking was possible
     *  - false if decisionLevel() == rootLevel()
     */
    bool backtrack();

    //! Undoes all assignments up to (but not including) decision level dl.
    /*!
     * \post decision level == max(min(decisionLevel(), dl), max(rootLevel(), backtrackLevel()))
     * \return The decision level after undoing assignments.
     * \note
     *   undoUntil() stops at the current backtrack level unless undoMode includes the mode
     *   that was used when setting the backtrack level.
     * \note
     *   If undoMode contains undo_save_phases, the functions saves the values of variables that are undone.
     *   Otherwise, phases are only saved if indicated by the active strategy.
     */
    uint32_t undoUntil(uint32_t dl, uint32_t undoMode);
    //! Behaves like undoUntil(dl, undo_default).
    uint32_t undoUntil(uint32_t dl) { return undoUntilImpl(dl, false); }
    //! Returns whether undoUntil(decisionLevel()-1) is valid and would remove decisionLevel().
    bool isUndoLevel() const;

    //! Adds a new auxiliary variable to this solver.
    /*!
     * Auxiliary variables are local to one solver and are not considered
     * as part of the problem. They shall be added/used only during solving, i.e.
     * after problem setup is completed.
     */
    Var_t pushAuxVar();
    //! Pops the num most recently added auxiliary variables and destroys all constraints in auxCons.
    void popAuxVar(uint32_t num = UINT32_MAX, ConstraintDB* auxCons = nullptr);
    //@}

    /*!
     * \name State inspection
     * Functions for inspecting the state of the solver & search.
     * \note validVar(v) is a precondition for all functions that take a variable as
     * parameter.
     * @{ */
    //! Returns the number of problem variables.
    uint32_t numProblemVars() const { return shared_->numVars(); }
    //! Returns the number of active solver-local aux variables.
    uint32_t numAuxVars() const { return numVars() - numProblemVars(); }
    //! Returns the number of solver variables, i.e. numProblemVars() + numAuxVars()
    uint32_t numVars() const { return assign_.numVars() - 1; }
    //! Returns the solver variables as an iterable view.
    auto vars(uint32_t off = 1u) const { return irange(off, numVars() + 1); }
    //! Returns the problem variables as an iterable view.
    auto problemVars(uint32_t off = 1u) const { return irange(off, numProblemVars() + 1); }
    //! Returns true if var represents a valid variable in this solver.
    bool validVar(Var_t var) const { return var <= numVars(); }
    //! Returns true if var is a solver-local aux var.
    bool auxVar(Var_t var) const { return shared_->numVars() < var; }
    //! Returns the number of assigned variables.
    uint32_t numAssignedVars() const { return assign_.assigned(); }
    //! Returns the number of free variables.
    /*!
     * The number of free variables is the number of vars that are neither
     * assigned nor eliminated.
     */
    uint32_t numFreeVars() const { return assign_.free() - 1; }
    //! Returns the value of v w.r.t the current assignment.
    Val_t value(Var_t v) const {
        assert(validVar(v));
        return assign_.value(v);
    }
    //! Returns the value of v w.r.t the top level.
    Val_t topValue(Var_t v) const { return level(v) == 0 ? value(v) : value_free; }
    //! Returns the set of preferred values of v.
    ValueSet pref(Var_t v) const {
        assert(validVar(v));
        return assign_.pref(v);
    }
    //! Returns true if p is true w.r.t the current assignment.
    bool isTrue(Literal p) const {
        assert(validVar(p.var()));
        return assign_.value(p.var()) == trueValue(p);
    }
    //! Returns true if p is false w.r.t the current assignment.
    bool isFalse(Literal p) const {
        assert(validVar(p.var()));
        return assign_.value(p.var()) == falseValue(p);
    }
    //! Returns the literal of v being true in the current assignment.
    /*!
     * \pre v is assigned a value in the current assignment
     */
    Literal trueLit(Var_t v) const {
        assert(value(v) != value_free);
        return {v, valSign(value(v))};
    }
    Literal defaultLit(Var_t v) const;
    //! Returns the decision level on which v was assigned.
    /*!
     * \note The returned value is only meaningful if value(v) != value_free.
     */
    uint32_t level(Var_t v) const {
        assert(validVar(v));
        return assign_.level(v);
    }
    //! Returns true if v is currently marked as seen.
    /*!
     * Note: variables assigned on level 0 are always marked.
     */
    bool seen(Var_t v) const {
        assert(validVar(v));
        return assign_.seen(v);
    }
    //! Returns true if the literal p is currently marked as seen.
    bool seen(Literal p) const {
        assert(validVar(p.var()));
        return assign_.seen(p);
    }
    //! Returns the current decision level.
    uint32_t decisionLevel() const { return size32(levels_); }
    bool     validLevel(uint32_t dl) const { return dl != 0 && dl <= decisionLevel(); }
    //! Returns the starting position of decision level dl in the trail.
    /*!
     * \pre validLevel(dl)
     */
    uint32_t levelStart(uint32_t dl) const {
        assert(validLevel(dl));
        return levels_[dl - 1].trailPos;
    }
    //! Returns the decision literal of the decision level dl.
    /*!
     * \pre validLevel(dl)
     */
    Literal decision(uint32_t dl) const {
        assert(validLevel(dl));
        return assign_.trail[levels_[dl - 1].trailPos];
    }
    //! Returns true, if the current assignment is conflicting.
    bool hasConflict() const { return not conflict_.empty(); }
    bool hasStopConflict() const { return hasConflict() && conflict_[0] == lit_false; }
    //! Returns the number of (unprocessed) literals in the propagation queue.
    uint32_t queueSize() const { return assign_.qSize(); }
    //! Number of problem constraints in this solver.
    uint32_t numConstraints() const;
    //! Returns the number of constraints that are currently in the solver's learnt database.
    uint32_t numLearntConstraints() const { return size32(learnts_); }
    //! Returns the reason for p being true.
    /*!
     * \pre p is true w.r.t the current assignment
     */
    const Antecedent& reason(Literal p) const {
        assert(isTrue(p));
        return assign_.reason(p.var());
    }
    //! Returns the additional reason data associated with p.
    uint32_t reasonData(Literal p) const { return assign_.data(p.var()); }
    //! Returns the current (partial) assignment as a set of true literals.
    /*!
     * \note Although the special var 0 always has a value it is not considered to be
     * part of the assignment.
     */
    LitView trailView(uint32_t offset = 0) const {
        return {assign_.trail.data() + offset, size32(assign_.trail) - offset};
    }
    const Assignment& assignment() const { return assign_; }
    //! Returns the current conflict as a set of literals.
    LitView conflict() const { return conflict_; }
    //! Returns the most recently derived conflict clause.
    LitView conflictClause() const { return cc_; }
    //! Returns the enumeration constraint set by the enumerator used.
    Constraint* enumerationConstraint() const { return enum_; }
    DBRef       constraints() const { return constraints_; }
    //! Returns the idx-th learnt constraint.
    /*!
     * \pre idx < numLearntConstraints()
     */
    Constraint& getLearnt(uint32_t idx) const {
        assert(idx < numLearntConstraints());
        return *learnts_[idx];
    }

    mutable Rng rng;   //!< Random number generator for this object.
    SolverStats stats; //!< Stores statistics about the solving process.
    //@}

    /*!
     * \name Watch management
     * Functions for setting/removing watches.
     * \pre validVar(v)
     * @{ */
    //! Returns the number of constraints watching the literal p.
    uint32_t numWatches(Literal p) const;
    //! Returns true if the constraint c watches the literal p.
    bool hasWatch(Literal p, Constraint* c) const;
    bool hasWatch(Literal p, ClauseHead* c) const;
    //! Returns c's watch-structure associated with p.
    /*!
     * \note returns 0, if hasWatch(p, c) == false
     */
    GenericWatch* getWatch(Literal p, Constraint* c) const;
    //! Adds c to the watch-list of p.
    /*!
     * When p becomes true, c->propagate(p, data, *this) is called.
     * \post hasWatch(p, c) == true
     */
    void addWatch(Literal p, Constraint* c, uint32_t data = 0) {
        assert(validWatch(p));
        watches_[p.id()].push_right(GenericWatch(c, data));
    }
    //! Adds w to the clause watch-list of p.
    void addWatch(Literal p, const ClauseWatch& w) {
        assert(validWatch(p));
        watches_[p.id()].push_left(w);
    }
    //! Removes c from p's watch-list.
    /*!
     * \post hasWatch(p, c) == false
     */
    void removeWatch(const Literal& p, Constraint* c);
    void removeWatch(const Literal& p, ClauseHead* c);
    //! Adds c to the watch-list of decision-level dl.
    /*!
     * Constraints in the watch-list of a decision level are
     * notified when that decision level is about to be backtracked.
     * \pre validLevel(dl)
     */
    void addUndoWatch(uint32_t dl, Constraint* c) {
        assert(validLevel(dl));
        if (levels_[dl - 1].undo != nullptr) {
            levels_[dl - 1].undo->push_back(c);
        }
        else {
            levels_[dl - 1].undo = allocUndo(c);
        }
    }
    //! Removes c from the watch-list of the decision level dl.
    bool removeUndoWatch(uint32_t dl, Constraint* c);
    //@}

    /*!
     * \name Misc functions
     * Low-level implementation functions. Use with care and only if you
     * know what you are doing!
     * @{ */
    bool addPost(PostPropagator* p, bool init);
    //! Updates the reason for p being true.
    /*!
     * \pre p is true and x is a valid reason for p
     */
    bool setReason(Literal p, const Antecedent& x, uint32_t data = UINT32_MAX) {
        assert(isTrue(p) || shared_->eliminated(p.var()));
        assign_.setReason(p.var(), x);
        if (data != UINT32_MAX) {
            assign_.setData(p.var(), data);
        }
        return true;
    }
    void setPref(Var_t v, ValueSet::Value which, Val_t to) {
        assert(validVar(v) && to <= value_false);
        assign_.requestPrefs();
        assign_.setPref(v, which, to);
    }
    void resetPrefs() { assign_.resetPrefs(); }
    void resetLearntActivities();
    //! Returns the reason for p being true as a set of literals.
    void reason(Literal p, LitVec& out) {
        assert(isTrue(p));
        out.clear();
        return assign_.reason(p.var()).reason(*this, p, out);
    }

    //! Helper function for updating antecedent scores during conflict resolution.
    /*!
     * \param sc   The current score of the active antecedent.
     * \param p    The literal implied by the active antecedent.
     * \param lits The literals of the active antecedent.
     * \return true if a score was updated.
     *
     * \note Depending on the active solver strategies, the function
     *       increases the activity and/or updates the lbd of the given antecedent.
     *
     * \note If SolverStrategies::bumpVarAct is active, p's activity
     *       is increased if the new lbd is smaller than the lbd of the
     *       conflict clause that is currently being derived.
     */
    bool updateOnReason(ConstraintScore& sc, Literal p, const LitVec& lits) {
        // update only during conflict resolution
        if (&lits != &conflict_) {
            return false;
        }
        sc.bumpActivity();
        if (uint32_t up = strategy_.updateLbd; up != SolverStrategies::lbd_fixed && not lits.empty()) {
            uint32_t lbd  = sc.lbd();
            auto     inc  = static_cast<uint32_t>(up != SolverStrategies::lbd_updated_less);
            uint32_t nLbd = countLevels(lits, lbd - inc);
            if ((nLbd + inc) < lbd) {
                sc.bumpLbd(nLbd + static_cast<uint32_t>(up == SolverStrategies::lbd_update_pseudo));
            }
        }
        if (strategy_.bumpVarAct && isTrue(p)) {
            bumpAct_.push_back(WeightLiteral{p, static_cast<Weight_t>(sc.lbd())});
        }
        return true;
    }

    //! Helper function for increasing antecedent activities during conflict clause minimization.
    bool updateOnMinimize(ConstraintScore& sc) const { return not strategy_.ccMinKeepAct && (sc.bumpActivity(), true); }

    //! Helper function for antecedents to be called during conflict clause minimization.
    bool ccMinimize(Literal p, CCMinRecursive* rec) const {
        return seen(p.var()) || (rec && hasLevel(level(p.var())) && ccMinRecurse(*rec, p));
    }

    //! Allocates a small block (32-bytes) from the solver's small block pool.
    void* allocSmall() { return smallAlloc_.allocate(); }
    //! Frees a small block previously allocated from the solver's small block pool.
    void freeSmall(void* m) { smallAlloc_.free(m); }

    void addLearntBytes(uint32_t bytes) { memUse_ += bytes; }
    void freeLearntBytes(uint64_t bytes) { memUse_ -= (bytes < memUse_) ? bytes : memUse_; }

    bool restartReached(const SearchLimits& limit) const;
    bool reduceReached(const SearchLimits& limit) const;

    //! simplifies cc and returns finalizeConflictClause(cc, info);
    uint32_t simplifyConflictClause(LitVec& cc, ConstraintInfo& info, ClauseHead* rhs);
    uint32_t finalizeConflictClause(LitVec& cc, ConstraintInfo& info, uint32_t ccRepMode = 0);
    uint32_t countLevels(LitView lits, uint32_t maxLevels = Clasp::lbd_max);
    bool     hasLevel(uint32_t dl) const {
        assert(validLevel(dl));
        return levels_[dl - 1].marked != 0;
    }
    bool frozenLevel(uint32_t dl) const {
        assert(validLevel(dl));
        return levels_[dl - 1].freeze != 0;
    }
    bool inputVar(Literal p) const { return varInfo(p.var()).input(); }
    void markLevel(uint32_t dl) {
        assert(validLevel(dl));
        levels_[dl - 1].marked = 1;
    }
    void freezeLevel(uint32_t dl) {
        assert(validLevel(dl));
        levels_[dl - 1].freeze = 1;
    }
    void unmarkLevel(uint32_t dl) {
        assert(validLevel(dl));
        levels_[dl - 1].marked = 0;
    }
    void unfreezeLevel(uint32_t dl) {
        assert(validLevel(dl));
        levels_[dl - 1].freeze = 0;
    }
    void markSeen(Var_t v) {
        assert(validVar(v));
        assign_.setSeen(v);
    }
    void markSeen(Literal p) {
        assert(validVar(p.var()));
        assign_.setSeen(p);
    }
    void clearSeen(Var_t v) {
        assert(validVar(v));
        assign_.clearSeen(v);
    }
    void    values(ValueVec& out) const { assign_.values(out); }
    void    setHeuristic(DecisionHeuristic* h);
    void    destroyDB(ConstraintDB& db);
    auto    strategies() -> SolverStrategies& { return strategy_; }
    bool    resolveToFlagged(LitView conflictClause, uint8_t vflag, LitVec& out, uint32_t& lbd) const;
    void    resolveToCore(LitVec& out);
    void    acquireProblemVar(Var_t var);
    void    acquireProblemVars() { acquireProblemVar(numProblemVars()); }
    auto    trailLit(uint32_t pos) const -> Literal { return assign_.trail[pos]; }
    LitView levelLits(uint32_t dl) const {
        auto start = levelStart(dl);
        return {assign_.trail.data() + start,
                (dl < decisionLevel() ? levelStart(dl + 1) : size32(assign_.trail)) - start};
    }
    //@}
private:
    struct DLevel {
        explicit DLevel(uint32_t pos = 0, ConstraintDB* u = nullptr) : trailPos(pos), marked(0), freeze(0), undo(u) {}
        uint32_t      trailPos : 30;
        uint32_t      marked   : 1;
        uint32_t      freeze   : 1;
        ConstraintDB* undo;
    };
    struct DecisionLevels : PodVector_t<DLevel> {
        uint32_t root      = 0; // root level
        uint32_t flip : 30 = 0; // backtrack level
        uint32_t mode : 2  = 0; // type of backtrack level
        uint32_t jump      = 0; // length of active undo
    };
    using ReasonVec   = PodVector_t<Antecedent>;
    using Watches     = PodVector_t<WatchList>;
    using CCMinRecPtr = std::unique_ptr<CCMinRecursive>;
    struct Dirty;
    struct CmpScore {
        using ViewPair = std::pair<uint32_t, ConstraintScore>;
        CmpScore(const ConstraintDB& learnts, ReduceStrategy::Score sc, uint32_t g, uint32_t f = 0)
            : db(learnts)
            , rs(sc)
            , glue(g)
            , freeze(f) {}
        [[nodiscard]] uint32_t score(const ConstraintScore& act) const { return ReduceStrategy::asScore(rs, act); }
        bool operator()(uint32_t lhsId, uint32_t rhsId) const { return (*this)(db[lhsId], db[rhsId]); }
        bool operator()(const ViewPair& lhs, const ViewPair& rhs) const {
            return this->operator()(lhs.second, rhs.second);
        }
        bool operator()(ConstraintScore lhs, ConstraintScore rhs) const {
            return ReduceStrategy::compare(rs, lhs, rhs) < 0;
        }
        bool operator()(const Constraint* lhs, const Constraint* rhs) const {
            return this->operator()(lhs->activity(), rhs->activity());
        }
        [[nodiscard]] bool    isFrozen(const ConstraintScore& a) const { return a.bumped() && a.lbd() <= freeze; }
        [[nodiscard]] bool    isGlue(const ConstraintScore& a) const { return a.lbd() <= glue; }
        const ConstraintDB&   db;
        ReduceStrategy::Score rs;
        uint32_t              glue;
        uint32_t              freeze;
    };
    bool               validWatch(Literal p) const { return p.id() < size32(watches_); }
    void               freeMem();
    void               resetHeuristic(Solver* detach, DecisionHeuristic* h = nullptr);
    bool               simplifySat();
    bool               unitPropagate();
    bool               postPropagate(PostPropagator** start, PostPropagator* stop);
    void               cancelPropagation();
    uint32_t           undoUntilImpl(uint32_t dl, bool sp);
    void               undoLevel(bool sp);
    uint32_t           analyzeConflict();
    bool               isModel();
    bool               resolveToFlagged(LitView conflictClause, uint8_t vf, LitVec& out, uint32_t& lbd);
    void               otfs(Antecedent& lhs, const Antecedent& rhs, Literal p, bool final);
    ClauseHead*        otfsRemove(ClauseHead* c, const LitVec* newC);
    uint32_t           ccMinimize(LitVec& cc, LitVec& removed, uint32_t antes, CCMinRecursive* ccMin);
    void               ccMinRecurseInit(CCMinRecursive& ccMin);
    bool               ccMinRecurse(CCMinRecursive& ccMin, Literal p) const;
    bool               ccRemovable(Literal p, uint32_t antes, CCMinRecursive* ccMin);
    Antecedent         ccHasReverseArc(Literal p, uint32_t maxLevel, uint32_t maxNew);
    void               ccResolve(LitVec& cc, uint32_t pos, const LitVec& reason);
    void               undoFree(ConstraintDB* x);
    void               setConflict(Literal p, const Antecedent& a, uint32_t data);
    bool               force(const ImpliedLiteral& p);
    void               updateBranch(uint32_t n);
    uint32_t           incEpoch(uint32_t size, uint32_t inc = 1);
    DBInfo             reduceLinear(uint32_t maxR, const CmpScore& cmp);
    DBInfo             reduceSort(uint32_t maxR, const CmpScore& cmp);
    DBInfo             reduceSortInPlace(uint32_t maxR, const CmpScore& cmp, bool onlyPartialSort);
    Literal            popVars(uint32_t num, bool popLearnt, ConstraintDB* popAux);
    ConstraintDB*      allocUndo(Constraint* c);
    SharedContext*     shared_;        // initialized by master thread - otherwise read-only!
    SolverStrategies   strategy_;      // strategies used by this object
    DecisionHeuristic* heuristic_;     // active decision heuristic
    CCMinRecPtr        ccMin_;         // additional data for supporting recursive strengthen
    PostPropagator**   postHead_;      // head of post propagator list to propagate
    ConstraintDB*      undoHead_;      // free list of undo DBs
    Constraint*        enum_;          // enumeration constraint - set by enumerator
    uint64_t           memUse_;        // memory used by learnt constraints (estimate)
    Dirty*             lazyRem_;       // set of watch lists that contain invalid constraints
    DynamicLimit*      dynLimit_;      // active dynamic limit
    SmallClauseAlloc   smallAlloc_;    // allocator object for small clauses
    Assignment         assign_;        // three-valued assignment.
    DecisionLevels     levels_;        // information (e.g. position in trail) on each decision level
    ConstraintDB       constraints_;   // problem constraints
    ConstraintDB       learnts_;       // learnt constraints
    PropagatorList     post_;          // (possibly empty) list of post propagators
    Watches            watches_;       // for each literal p: list of constraints watching p
    LitVec             conflict_;      // conflict-literals for later analysis
    LitVec             cc_;            // temporary: conflict clause within analyzeConflict
    LitVec             temp_;          // temporary: redundant literals in simplifyConflictClause
    WeightLitVec       bumpAct_;       // temporary: lits from current dl whose activity might get an extra bump
    VarVec             epoch_;         // temporary vector for computing LBD
    VarVec             cflStamp_;      // temporary vector for computing number of conflicts in branch
    ImpliedList        impliedLits_;   // lits that were asserted on current dl but are logically implied earlier
    ConstraintInfo     ccInfo_;        // temporary: information about conflict clause cc_
    Literal            tag_;           // aux literal for tagging learnt constraints
    uint32_t           dbIdx_;         // position of first new problem constraint in master db
    uint32_t           lastSimp_ : 30; // number of top-level assignments on last call to simplify
    uint32_t           shufSimp_ : 1;  // shuffle db on next simplify?
    uint32_t           initPost_ : 1;  // initialize new post propagators?
    bool               splitReq_;      // unhandled split request?
};
inline bool isRevLit(const Solver& s, Literal p, uint32_t maxL) {
    return s.isFalse(p) && (s.seen(p) || s.level(p.var()) < maxL);
}
//! Simplifies the constraints in db and removes those that are satisfied.
template <typename C>
void simplifyDB(Solver& s, C& db, bool shuffle) {
    typename C::size_type j = 0;
    for (Constraint* c : db) {
        if (c->simplify(s, shuffle)) {
            c->destroy(&s, false);
        }
        else {
            db[j++] = c;
        }
    }
    shrinkVecTo(db, j);
}
//! Destroys (and optionally detaches) all constraints in db.
void destroyDB(Solver::ConstraintDB& db, Solver* s, bool detach);
//! Returns the default decision literal of the given variable.
inline Literal Solver::defaultLit(Var_t v) const {
    switch (strategy_.signDef) {
        default: //
        case SolverStrategies::sign_atom: return {v, not varInfo(v).has(VarInfo::flag_body)};
        case SolverStrategies::sign_pos : return posLit(v);
        case SolverStrategies::sign_neg : return negLit(v);
        case SolverStrategies::sign_rnd : return {v, rng.drand() < 0.5};
    }
}
//! Event type optionally emitted after a conflict.
struct NewConflictEvent : SolveEvent {
    template <typename C>
    NewConflictEvent(const Solver& s, const C& c, const ConstraintInfo& i)
        : SolveEvent(this, s, verbosity_quiet)
        , learnt(c)
        , info(i) {}
    LitView        learnt; //!< Learnt conflict clause.
    ConstraintInfo info;   //!< Additional information associated with the conflict clause.
};
//@}

/**
 * \defgroup heuristic Decision Heuristics
 * \brief Decision heuristics and related classes.
 * \ingroup solver
 */
//@{
//! Base class for decision heuristics to be used in a Solver.
/*!
 * During search the decision heuristic is used whenever the DPLL-procedure must pick
 * a new variable to branch on. Each concrete decision heuristic can implement a
 * different algorithm for selecting the next decision variable.
 */
class DecisionHeuristic {
public:
    DecisionHeuristic() = default;
    virtual ~DecisionHeuristic();
    DecisionHeuristic(DecisionHeuristic&&) = delete;

    /*!
     * Called once after all problem variables are known to the solver.
     * The default-implementation is a noop.
     * \param s The solver in which this heuristic is used.
     */
    virtual void startInit(const Solver& s) { static_cast<void>(s); }

    /*!
     * Called once after all problem constraints are known to the solver
     * and the problem was simplified.
     * The default-implementation is a noop.
     * \param s The solver in which this heuristic is used.
     */
    virtual void endInit(Solver& s) { static_cast<void>(s); }

    //! Called once if s switches to a different heuristic.
    virtual void detach(Solver& s) { static_cast<void>(s); }

    //! Called if configuration has changed.
    virtual void setConfig(const HeuParams& p) { static_cast<void>(p); }

    /*!
     * Called if the state of one or more variables changed.
     * A state change is one of:
     *   - A previously eliminated variable is resurrected.
     *   - A new aux variable was added.
     *   - An aux variable was removed.
     *   .
     * \param s Solver in which the state change occurred.
     * \param v The first variable affected by the change.
     * \param n The range of variables affected, i.e. [v, v+n).
     * \note Use s.validVar(v) and s.auxVar(v) to determine the reason for the update.
     */
    virtual void updateVar(const Solver& s, Var_t v, uint32_t n) = 0;

    /*!
     * Called on decision level 0. Variables that are assigned on this level
     * may be removed from any decision heuristic.
     * \note Whenever the solver returns to dl 0, simplify is only called again
     * if the solver learnt new facts since the last call to simplify.
     *
     * \param s The solver that reached decision level 0.
     * \param newFacts List of newly derived facts.
     */
    virtual void simplify(const Solver& s, LitView newFacts) {
        static_cast<void>(s);
        static_cast<void>(newFacts);
    }

    /*!
     * Called whenever the solver backtracks.
     * Literals in 'undo' are subject to backtracking.
     * The default-implementation is a noop.
     * \param s The solver that is about to backtrack.
     * \param undo Literals that will be backtracked.
     */
    virtual void undo(const Solver& s, LitView undo) {
        static_cast<void>(s);
        static_cast<void>(undo);
    }

    /*!
     * Called whenever a new constraint is added to the given solver.
     * The default-implementation is a noop.
     * \param s The solver to which the constraint is added.
     * \param lits Literals of the new constraint.
     * \param t Type of the new constraint.
     */
    virtual void newConstraint(const Solver& s, LitView lits, ConstraintType t) {
        static_cast<void>(s);
        static_cast<void>(lits);
        static_cast<void>(t);
    }

    /*!
     * Called for each new reason-set that is traversed during conflict analysis.
     * The default-implementation is a noop.
     * \param s The solver in which the conflict is analyzed.
     * \param lits The current reason-set under inspection.
     * \param resolveLit The literal that is currently resolved.
     * \note When a conflict is detected, the solver passes the conflicting literals
     * in lits during the first call to updateReason. On that first call resolveLit
     * is the sentinel-literal.
     */
    virtual void updateReason(const Solver& s, LitView lits, Literal resolveLit) {
        static_cast<void>(s);
        static_cast<void>(lits);
        static_cast<void>(resolveLit);
    }

    //! Shall bump the activity of literals `l` in `lits` by `l.weight * adj`.
    /*!
     * The default-implementation is a noop and always returns false.
     * \return true if heuristic supports activities, false otherwise.
     */
    virtual bool bump(const Solver& s, WeightLitView lits, double adj) {
        static_cast<void>(s);
        static_cast<void>(lits);
        static_cast<void>(adj);
        return false;
    }

    /*!
     * Called whenever the solver must pick a new variable to branch on.
     * \param s The solver that needs a new decision variable.
     * \return
     *  - true  : if the decision heuristic assumed a literal
     *  - false : if no decision could be made because assignment is total or there is a conflict
     *  .
     * \post
     * If true is returned, the heuristic has asserted a literal.
     */
    bool select(Solver& s) { return s.numFreeVars() != 0 && s.assume(doSelect(s)); }

    //! Implements the actual selection process.
    /*!
     * \pre s.numFreeVars() > 0, i.e. there is at least one variable to branch on.
     * \return
     *  - a literal that is currently free or
     *  - a sentinel literal. In that case, the heuristic shall have asserted a literal!
     */
    virtual Literal doSelect(Solver& s) = 0;

    /*!
     * Shall select one of the literals in the given non-empty range.
     * \param s     The solver that needs a new decision variable.
     * \param range Range of literals to select from.
     * \pre lits is a non-empty range of currently unassigned literals.
     * \note The default implementation returns the first literal in lits.
     */
    virtual Literal selectRange(Solver& s, LitView range) {
        static_cast<void>(s);
        static_cast<void>(range);
        return range[0];
    }
    static Literal selectLiteral(const Solver& s, Var_t v, int signScore) {
        auto prefs = s.pref(v);
        if (signScore != 0 && not prefs.has(ValueSet::user_value | ValueSet::saved_value | ValueSet::pref_value)) {
            return {v, signScore < 0};
        }
        if (not prefs.empty()) {
            return {v, prefs.sign()};
        }
        return s.defaultLit(v);
    }
};
//! Selects the first free literal w.r.t to the initial variable order.
class SelectFirst : public DecisionHeuristic {
public:
    void    updateVar(const Solver&, Var_t, uint32_t) override {}
    Literal doSelect(Solver& s) override;
};
//@}
} // namespace Clasp
