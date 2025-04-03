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
#include <clasp/solver.h>

#include <potassco/clingo.h>
namespace Clasp {
/*!
 * \defgroup clingo Clingo
 * \brief Additional classes mainly used by clingo.
 * \ingroup facade
 * @{ */

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

//! Initialization adaptor for a Potassco::AbstractPropagator.
/*!
 * The class provides functions for registering watches for the propagator and for adding a (suitably adapted)
 * propagator to a solver.
 */
class ClingoPropagatorInit : public Potassco::AbstractPropagator::Init {
public:
    using Lit_t    = Potassco::Lit_t;
    using MapLitCb = std::function<Lit_t(Lit_t)>;

    //! Creates a new adaptor.
    /*!
     * \param ctx Context-object storing the problem.
     * \param cb The (theory) propagator that should be added to solvers.
     * \param mapLit Optional function for mapping program to solver literals.
     * \param check The check mode that should be used for the propagator.
     */
    explicit ClingoPropagatorInit(SharedContext& ctx, Potassco::AbstractPropagator& cb, MapLitCb mapLit,
                                  CheckMode check = CheckMode::total);
    ~ClingoPropagatorInit();
    ClingoPropagatorInit(ClingoPropagatorInit&&) = delete;
    // own interface
    void enableHistory(bool b);
    //! Finishes initialization of watches and invokes init() on the propagator().
    /*!
     * Shall be called once before the context object passed on construction is frozen.
     */
    void endInit();
    //! Adds a ClingoPropagator adapting the propagator() to s.
    bool addPropagator(Solver& s);
    //! Prepares this object for a new solving step.
    /*!
     * Shall be called once after the context object passed on construction was unfrozen.
     */
    void unfreeze();

    using Init::addWatch;
    using Init::removeWatch;
    void addWatch(Literal lit) { addWatch(encodeLit(lit)); }
    void addWatch(uint32_t solverId, Literal lit) { ClingoPropagatorInit::addWatch(encodeLit(lit), solverId); }
    void removeWatch(Literal lit) { removeWatch(encodeLit(lit)); }
    void removeWatch(uint32_t solverId, Literal lit) { removeWatch(encodeLit(lit), solverId); }
    void freezeLit(Literal lit) { ClingoPropagatorInit::freezeLiteral(encodeLit(lit)); }
    //! Returns the propagator that was given on construction.
    [[nodiscard]] Potassco::AbstractPropagator* propagator() const { return prop_; }
    //! Returns whether the init object is currently frozen, i.e. endInit() was called.
    [[nodiscard]] bool frozen() const;
    [[nodiscard]] bool hasConflict() const;
    uint32_t           attach(uint32_t gen, Potassco::AbstractSolver& s);

    // base interface
    [[nodiscard]] CheckMode checkMode() const override { return check_; }
    [[nodiscard]] UndoMode  undoMode() const override { return undo_; }
    [[nodiscard]] uint32_t  numSolver() const override;
    [[nodiscard]] Lit_t     solverLiteral(Lit_t lit) const override;
    [[nodiscard]] auto      assignment() const -> const Potassco::AbstractAssignment& override;

    void  setCheckMode(CheckMode m) override;
    void  setUndoMode(UndoMode m) override;
    void  addWatch(Lit_t lit, uint32_t solverId) override;
    void  removeWatch(Lit_t lit, uint32_t solverId) override;
    void  freezeLiteral(Lit_t lit) override;
    Lit_t addLiteral(bool freeze) override;
    bool  addClause(Potassco::LitSpan clause) override;
    bool  addWeightConstraint(Lit_t con, Potassco::WeightLitSpan lits, Weight_t bound, int32_t type, bool eq) override;
    void  addMinimize(Weight_t prio, Potassco::WeightLit lit) override;
    bool  propagate() override;

private:
    enum Action { remove_watch = 0, add_watch = 1 };
    struct History;
    struct Change {
        Change(Lit_t p, Action a, uint32_t solverId = UINT32_MAX);
        [[nodiscard]] uint64_t solverMask() const;
        Lit_t                  lit;
        int16_t                sId;
        int16_t                action;
    };
    void addChange(Lit_t lit, Action action, uint32_t solverId = UINT32_MAX);
    using ChangeList = PodVector_t<Change>;
    SharedContext*                ctx_;
    ClingoAssignment              assignment_;
    Potassco::AbstractPropagator* prop_;
    MapLitCb                      mapLit_;
    std::unique_ptr<History>      history_;
    LitVec                        mem_;
    ChangeList                    changes_;
    CheckMode                     check_;
    UndoMode                      undo_;
    bool                          frozen_;
};

//! Adaptor for a Potassco::AbstractPropagator.
/*!
 * The class adapts a given Potassco::AbstractPropagator so that
 * it is usable as a PostPropagator within libclasp.
 */
class ClingoPropagator final : public PostPropagator {
public:
    static constexpr auto prio = PostPropagator::priority_class_general;

    using ChangeList = Potassco::AbstractPropagator::ChangeList;
    using PPair      = Clasp::PostPropagator::PropResult;
    using CheckMode  = Potassco::PropagatorCheckMode;
    using UndoMode   = Potassco::PropagatorUndoMode;

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

    [[nodiscard]] bool matches(ClingoPropagatorInit*) const;

private:
    using Lit_t = Potassco::Lit_t;
    class Control;
    struct ScopedCall;
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
    uint32_t    myGen_{0};          // last time init() was called
    Literal     aux_;               // max active literal
    const char* op_{nullptr};       // active operation
};

class ClingoHeuristic : public DecisionHeuristic {
public:
    static HeuristicFactory creator(Potassco::AbstractHeuristic& clingoHeuristic);
    explicit ClingoHeuristic(Potassco::AbstractHeuristic& clingoHeuristic, DecisionHeuristic* claspHeuristic);
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
};

///@}
} // namespace Clasp
