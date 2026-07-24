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
    using BaseType = AbstractAssignment;
    using Value_t  = Potassco::TruthValue;
    using Lit_t    = Potassco::Lit_t;

    explicit ClingoAssignment(const Solver& s);
    [[nodiscard]] auto solverId() const -> Potassco::Id_t override { return solver_->id(); }
    [[nodiscard]] auto size() const -> uint32_t override;
    [[nodiscard]] auto unassigned() const -> uint32_t override;
    [[nodiscard]] auto hasConflict() const -> bool override;
    [[nodiscard]] auto level() const -> uint32_t override;
    [[nodiscard]] auto rootLevel() const -> uint32_t override;
    [[nodiscard]] auto hasLit(Lit_t lit) const -> bool override;
    [[nodiscard]] auto value(Lit_t lit) const -> Value_t override;
    [[nodiscard]] auto level(Lit_t lit) const -> uint32_t override;
    [[nodiscard]] auto decision(uint32_t) const -> Lit_t override;
    [[nodiscard]] auto isTotal() const -> bool override;
    [[nodiscard]] auto trailSize() const -> uint32_t override;
    [[nodiscard]] auto trailAt(uint32_t) const -> Lit_t override;
    [[nodiscard]] auto trailBegin(uint32_t) const -> uint32_t override;

    [[nodiscard]] auto solver() const -> const Solver& { return *solver_; }

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
    ~ClingoPropagatorInit() override;
    ClingoPropagatorInit(ClingoPropagatorInit&&) = delete;
    //! Calls init() on the theory propagator.
    /*!
     * Shall be called once before the context object passed on construction is frozen.
     * \post frozen() returns true.
     */
    void init();
    //! Adds a ClingoPropagator adapting the theory propagator to `s`.
    bool addPropagator(Solver& s);
    //! Prepares this object for a new solving step.
    /*!
     * Shall be called once after the context object passed on construction was unfrozen.
     * \post frozen() returns false.
     */
    void unfreeze();

    using Init::addWatch;
    using Init::removeWatch;
    void addWatch(Literal lit) { addWatch(encodeLit(lit)); }
    void removeWatch(Literal lit) { removeWatch(encodeLit(lit)); }
    void freezeLit(Literal lit) { ClingoPropagatorInit::freezeVariable(encodeLit(lit)); }
    //! Returns the propagator given on construction.
    [[nodiscard]] auto propagator() const -> Potassco::AbstractPropagator* { return &prop_; }
    //! Returns whether the init object is currently frozen; i.e., init() was called.
    [[nodiscard]] bool frozen() const;
    [[nodiscard]] bool hasConflict() const;
    auto               initWatches(uint32_t gen, Potassco::AbstractPropagator::Control& s) -> uint32_t;

    // base interface
    [[nodiscard]] auto checkMode() const -> CheckMode override { return check_; }
    [[nodiscard]] auto undoMode() const -> UndoMode override { return undo_; }
    [[nodiscard]] auto numSolver() const -> uint32_t override;
    [[nodiscard]] auto solverLiteral(Lit_t lit) const -> Lit_t override;
    [[nodiscard]] bool hasWatch(Lit_t lit) const override;

    void setCheckMode(CheckMode m) override;
    void setUndoMode(UndoMode m) override;
    void addWatch(Lit_t lit) override;
    void removeWatch(Lit_t lit) override;
    void freezeVariable(Lit_t lit) override;
    auto addVariable(bool freeze) -> Lit_t override;
    bool addClause(Potassco::LitSpan clause, Potassco::ClauseType) override;
    bool addWeightConstraint(Lit_t con, Potassco::WeightLitSpan lits, Weight_t bound, int32_t type) override;
    void addMinimize(Weight_t prio, Potassco::WeightLit lit) override;
    bool propagate() override;

private:
    class WatchList;
    using WatchListPtr = std::unique_ptr<WatchList>;
    using Propagator   = Potassco::AbstractPropagator;

    SharedContext& ctx_;
    Propagator&    prop_;
    MapLitCb       mapLit_;
    LitVec         mem_;
    WatchListPtr   watches_;
    CheckMode      check_;
    UndoMode       undo_;
    bool           frozen_;
};

//! Adaptor for a Potassco::AbstractPropagator.
/*!
 * The class adapts a given Potassco::AbstractPropagator so that
 * it is usable as a PostPropagator within libclasp.
 */
class ClingoPropagator final : public PostPropagator {
public:
    static constexpr auto prio = priority_class_general;

    using ChangeList = Potassco::AbstractPropagator::ChangeList;
    using CheckMode  = Potassco::PropagatorCheckMode;
    using UndoMode   = Potassco::PropagatorUndoMode;

    explicit ClingoPropagator(ClingoPropagatorInit* init);

    // PostPropagator
    [[nodiscard]] auto priority() const -> uint32_t override;

    bool init(Solver& s) override;
    bool propagateFixpoint(Solver& s, PostPropagator* ctx) override;
    auto propagate(Solver&, Literal, uint32_t&) -> PropResult override;
    bool isModel(Solver& s) override;
    void reason(Solver&, Literal, LitVec&) override;
    void undoLevel(Solver& s) override;
    bool simplify(Solver& s, bool reinit) override;
    void destroy(Solver* s, bool detach) override;

    [[nodiscard]] bool matches(ClingoPropagatorInit*) const;
    [[nodiscard]] auto numConstraints() const -> uint32_t { return size32(db_); }

private:
    using Lit_t = Potassco::Lit_t;
    class CallAdaptor;
    enum State : uint32_t { state_ctrl = 1u, state_prop = 2u, state_init = 4u };
    struct Todo {
        [[nodiscard]] bool empty() const { return flags == 0; }
        void               clear() { flags = 0; }
        LitVec             lits;
        WeightLitVec       wLits;
        ClauseRep          clause;
        uint32_t           flags;
    };
    using AspifVec   = Vector_t<Lit_t>;
    using Propagator = ClingoPropagatorInit;
    [[nodiscard]] bool inTrail(Literal p) const;

    bool addTodo(Solver& s, State state);
    bool prepareAdd(Solver& s, uint32_t dl, State state);
    void toClause(Solver& s, const Potassco::LitSpan& clause, Potassco::ClauseType prop);
    void toWeightCon(Solver& s, Potassco::Lit_t con, const Potassco::WeightLitSpan& lits, Weight_t bound, int32_t type);
    bool propagate(Solver& s, State state);
    void addWatch(Solver& s, Literal p, State state);
    void registerUndoCheck(Solver& s);
    void registerUndo(Solver& s, uint32_t data);

    Propagator*   call_;        // wrapped theory propagator
    AspifVec      trail_;       // assignment trail: watched literals that are true
    AspifVec      temp_;        // temporary buffer used to pass changes to user
    VarVec        undo_;        // offsets into trail marking beginnings of decision levels
    ConstraintVec db_;          // clauses added with flag static
    Todo          todo_{};      // active clause/constraint to be added (received from theory propagator)
    const char*   op_{nullptr}; // active operation
    uint32_t      prop_{0};     // offset into trail: literals [0, prop_) were propagated
    uint32_t      level_{0};    // highest undo level
    int32_t       front_{-1};   // global assignment position for fixpoint checks
    uint32_t      myGen_{0};    // last time init() was called
    Literal       aux_;         // max active literal
    Val_t         propRes_{0};  // last result in Control::propagate()
};

class ClingoHeuristic : public DecisionHeuristic {
public:
    explicit ClingoHeuristic(Potassco::AbstractHeuristic& clingoHeuristic, DecisionHeuristic* claspHeuristic);
    void startInit(const Solver& s) override;
    void endInit(Solver& s) override;
    void detach(Solver& s) override;
    void setConfig(const HeuParams& p) override;
    void updateVar(const Solver& s, Var_t v, uint32_t n) override;
    void simplify(const Solver& s, LitView) override;
    void undo(const Solver& s, LitView undo) override;
    void newConstraint(const Solver& s, LitView lits, ConstraintType t) override;
    void updateReason(const Solver& s, LitView lits, Literal resolveLit) override;
    bool bump(const Solver& s, WeightLitView lits, double adj) override;
    auto doSelect(Solver& s) -> Literal override;
    auto selectRange(Solver& s, LitView range) -> Literal override;

    [[nodiscard]] auto fallback() const -> DecisionHeuristic*;

private:
    using HeuPtr = std::unique_ptr<DecisionHeuristic>;
    Potassco::AbstractHeuristic* clingo_;
    HeuPtr                       clasp_;
};

///@}
} // namespace Clasp
