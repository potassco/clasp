//
// Copyright (c) 2015-present Benjamin Kaufmann
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
 * \brief Types for implementing theory propagation from clingo.
 */
#include <clasp/clasp_facade.h>
#include <clasp/solver.h>

#include <potassco/clingo.h>
namespace Clasp {

/*!
 * \defgroup clingo Clingo
 * \brief Additional classes mainly used by clingo.
 * \ingroup facade
 * @{ */

//! Lock interface called by libclasp during (multithreaded) theory propagation.
/*!
 * The interface may be implemented by the application to lock
 * certain global data structures. For example, in clingo,
 * this interface wraps python's global interpreter lock.
 */
class ClingoPropagatorLock {
public:
    virtual ~ClingoPropagatorLock();
    virtual void lock()   = 0;
    virtual void unlock() = 0;
};

//! Supported check modes for clingo propagators.
enum class ClingoPropagatorCheckType {
    no       = 0u, //!< Never call AbstractPropagator::check().
    total    = 1u, //!< Call AbstractPropagator::check() only on total assignment.
    fixpoint = 2u, //!< Call AbstractPropagator::check() on every propagation fixpoint.
    both     = 3u  //!< Call AbstractPropagator::check() on every fixpoint and total assignment.
};

//! Supported undo modes for clingo propagators.
enum class ClingoPropagatorUndoType {
    def    = 0u, //!< Call AbstractPropagator::undo() only on levels with non-empty changelist.
    always = 1u  //!< Call AbstractPropagator::undo() on all levels that have been propagated or checked.
};

//! Initialization adaptor for a Potassco::AbstractPropagator.
/*!
 * The class provides a function for registering watches for the propagator.
 * Furthermore, it can be added to a clasp configuration so that
 * a (suitably adapted) propagator is added to solvers that are attached to the configuration.
 */
class ClingoPropagatorInit : public ClaspConfig::Configurator {
public:
    using CheckType = ClingoPropagatorCheckType;
    using UndoType  = ClingoPropagatorUndoType;
    //! Creates a new adaptor.
    /*!
     * \param cb The (theory) propagator that should be added to solvers.
     * \param lock An optional lock that should be applied during theory propagation.
     * \param check The check mode that should be used for the propagator.
     *
     * If lock is not null, calls to cb are wrapped in a lock->lock()/lock->unlock() pair
     */
    explicit ClingoPropagatorInit(Potassco::AbstractPropagator& cb, ClingoPropagatorLock* lock = nullptr,
                                  CheckType check = CheckType::total);
    ~ClingoPropagatorInit() override;
    ClingoPropagatorInit(ClingoPropagatorInit&&) = delete;
    // base class
    void prepare(SharedContext&) override;
    //! Adds a ClingoPropagator adapting the propagator() to s.
    bool applyConfig(Solver& s) override;
    void unfreeze(SharedContext&) override;

    // for clingo
    //! Sets the type of checks to enable during solving.
    /*!
     * \param checkMode A set of ClingoPropagatorCheckType values.
     */
    void enableClingoPropagatorCheck(CheckType checkMode);

    //! Sets the undo mode to use when checks are enabled.
    /*!
     * \param undoMode The undo mode to use.
     *
     * \note By default, AbstractPropagator::undo() is only called for levels on which
     *       at least one watched literal has been assigned. However, if undoMode is set
     *       to "Always", AbstractPropagator::undo() is also called for levels L with an
     *       empty change list if AbstractPropagator::check() has been called on L.
     */
    void enableClingoPropagatorUndo(UndoType undoMode);

    void enableHistory(bool b);

    //! Adds a watch for lit to all solvers and returns encodeLit(lit).
    Potassco::Lit_t addWatch(Literal lit);
    //! Removes the watch for lit from all solvers.
    void removeWatch(Literal lit);
    //! Adds a watch for lit to the solver with the given id and returns encodeLit(lit).
    Potassco::Lit_t addWatch(uint32_t solverId, Literal lit);
    //! Removes the watch for lit from solver with the given id.
    void removeWatch(uint32_t solverId, Literal lit);
    //! Freezes the given literal making it exempt from Sat-preprocessing.
    /*!
     * \note Watched literals are automatically frozen.
     */
    void freezeLit(Literal lit);

    //! Returns the propagator that was given on construction.
    [[nodiscard]] Potassco::AbstractPropagator* propagator() const { return prop_; }
    [[nodiscard]] ClingoPropagatorLock*         lock() const { return lock_; }
    [[nodiscard]] CheckType                     checkMode() const { return check_; }
    [[nodiscard]] UndoType                      undoMode() const { return undo_; }

    uint32_t init(uint32_t lastStep, Potassco::AbstractSolver& s);

private:
    using Lit_t = Potassco::Lit_t;
    enum Action { remove_watch = 0, add_watch = 1, freeze_lit = 2 };
    struct History;
    struct Change {
        struct Less;
        Change(Lit_t p, Action a);
        Change(Lit_t p, Action a, uint32_t sId);
        void                   apply(Potassco::AbstractSolver& s) const;
        [[nodiscard]] uint64_t solverMask() const;
        Lit_t                  lit;
        int16_t                sId;
        int16_t                action;
    };
    using ChangeList = PodVector_t<Change>;
    Potassco::AbstractPropagator* prop_;
    ClingoPropagatorLock*         lock_;
    std::unique_ptr<History>      history_;
    ChangeList                    changes_;
    uint32_t                      step_;
    CheckType                     check_;
    UndoType                      undo_;
};

//! Adaptor for a Potassco::AbstractPropagator.
/*!
 * The class adapts a given Potassco::AbstractPropagator so that
 * it is usable as a PostPropagator within libclasp.
 */
class ClingoPropagator final : public PostPropagator {
public:
    using ChangeList = Potassco::AbstractPropagator::ChangeList;
    using PPair      = Clasp::PostPropagator::PropResult;

    explicit ClingoPropagator(ClingoPropagatorInit* init);

    // PostPropagator
    [[nodiscard]] uint32_t priority() const override;

    bool  init(Solver& s) override;
    bool  propagateFixpoint(Solver& s, PostPropagator* ctx) override;
    PPair propagate(Solver&, Literal, uint32_t&) override;
    bool  isModel(Solver& s) override;
    void  reason(Solver&, Literal, LitVec&) override;
    void  undoLevel(Solver& s) override;
    bool  simplify(Solver& s, bool reinit) override;
    void  destroy(Solver* s, bool detach) override;

private:
    using Lit_t = Potassco::Lit_t;
    class Control;
    enum State : uint32_t { state_ctrl = 1u, state_prop = 2u, state_init = 4u };
    struct ClauseTodo {
        [[nodiscard]] bool empty() const { return mem.empty(); }
        void               clear() { mem.clear(); }
        LitVec             mem;
        ClauseRep          clause;
        uint32_t           flags;
    };
    using AspifVec   = PodVector_t<Lit_t>;
    using ClauseDB   = PodVector_t<Constraint*>;
    using Propagator = ClingoPropagatorInit;
    using ClingoLock = ClingoPropagatorLock*;
    [[nodiscard]] bool inTrail(Literal p) const;

    bool addClause(Solver& s, State state);
    void toClause(Solver& s, const Potassco::LitSpan& clause, Potassco::ClauseType prop);
    void registerUndoCheck(Solver& s);
    void registerUndo(Solver& s, uint32_t data);

    Propagator* call_;              // wrapped theory propagator
    AspifVec    trail_;             // assignment trail: watched literals that are true
    AspifVec    temp_;              // temporary buffer used to pass changes to user
    VarVec      undo_;              // offsets into trail marking beginnings of decision levels
    ClauseDB    db_;                // clauses added with flag static
    ClauseTodo  todo_{};            // active clause to be added (received from theory propagator)
    uint32_t    prop_{0};           // offset into trail: literals [0, prop_) were propagated
    uint32_t    epoch_{0};          // number of calls into callback
    uint32_t    level_{0};          // highest undo level
    uint32_t    propL_{UINT32_MAX}; // decision level on handling propagate() from theory propagator
    int32_t     front_{-1};         // global assignment position for fixpoint checks
    uint32_t    init_{0};           // last time init() was called
    Literal     aux_;               // max active literal
};

class ClingoAssignment : public Potassco::AbstractAssignment {
public:
    using BaseType = Potassco::AbstractAssignment;
    using Value_t  = Potassco::TruthValue;
    using Lit_t    = Potassco::Lit_t;

    explicit ClingoAssignment(const Solver& s);

    [[nodiscard]] uint32_t size() const override;
    [[nodiscard]] uint32_t unassigned() const override;
    [[nodiscard]] bool     hasConflict() const override;
    [[nodiscard]] uint32_t level() const override;
    [[nodiscard]] uint32_t rootLevel() const override;
    [[nodiscard]] bool     hasLit(Lit_t lit) const override;
    [[nodiscard]] Value_t  value(Lit_t lit) const override;
    [[nodiscard]] uint32_t level(Lit_t lit) const override;
    [[nodiscard]] Lit_t    decision(uint32_t) const override;
    [[nodiscard]] bool     isTotal() const override;
    [[nodiscard]] uint32_t trailSize() const override;
    [[nodiscard]] Lit_t    trailAt(uint32_t) const override;
    [[nodiscard]] uint32_t trailBegin(uint32_t) const override;

    [[nodiscard]] const Solver& solver() const { return *solver_; }

private:
    const Solver* solver_;
};

class ClingoHeuristic : public DecisionHeuristic {
public:
    // Returns a factory for adding the given heuristic to solvers.
    /*!
     * \param clingoHeuristic The heuristic that should be added to solvers.
     * \param lock An optional lock that should be applied during calls to AbstractHeuristic::decide().
     */
    static BasicSatConfig::HeuristicCreator creator(Potassco::AbstractHeuristic& clingoHeuristic,
                                                    ClingoPropagatorLock*        lock = nullptr);

    explicit ClingoHeuristic(Potassco::AbstractHeuristic& clingoHeuristic, DecisionHeuristic* claspHeuristic,
                             ClingoPropagatorLock* lock);
    void    startInit(const Solver& s) override;
    void    endInit(Solver& s) override;
    void    detach(Solver& s) override;
    void    setConfig(const HeuParams& p) override;
    void    updateVar(const Solver& s, Var_t v, uint32_t n) override;
    void    simplify(const Solver& s, LitView) override;
    void    undo(const Solver& s, LitView undo) override;
    void    newConstraint(const Solver& s, LitView lits, ConstraintType t) override;
    void    updateReason(const Solver& s, LitView lits, Literal resolveLit) override;
    bool    bump(const Solver& s, WeightLitView lits, double adj) override;
    Literal doSelect(Solver& s) override;
    Literal selectRange(Solver& s, LitView range) override;

    [[nodiscard]] DecisionHeuristic* fallback() const;

private:
    using HeuPtr = std::unique_ptr<DecisionHeuristic>;
    Potassco::AbstractHeuristic* clingo_;
    HeuPtr                       clasp_;
    ClingoPropagatorLock*        lock_;
};

///@}
} // namespace Clasp
