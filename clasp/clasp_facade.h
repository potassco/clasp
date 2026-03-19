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

#include <clasp/config.h>

#include <clasp/enumerator.h>
#include <clasp/logic_program.h>
#include <clasp/parser.h>
#include <clasp/program_builder.h>
#include <clasp/shared_context.h>
#include <clasp/solver_types.h>
#if CLASP_HAS_THREADS
#include <clasp/mt/parallel_solve.h>

#include <potassco/clingo.h>

namespace Clasp {
using BaseSolveOptions = mt::ParallelSolveOptions;
} // namespace Clasp
#else
#include <clasp/solve_algorithms.h>
namespace Clasp {
using BaseSolveOptions = BasicSolveOptions;
} // namespace Clasp
#endif

#include <csignal>
#ifndef SIGALRM
#define SIGALRM 14
#endif

/*!
 * \file
 * \brief High-level API
 *
 * This file provides a facade around the clasp library.
 * I.e., a simplified interface for (multishot) solving a problem using
 * some configuration (set of parameters).
 * \ingroup facade
 */
namespace Clasp {
/////////////////////////////////////////////////////////////////////////////////////////
// Configuration
/////////////////////////////////////////////////////////////////////////////////////////
//! Options for controlling enumeration and solving.
struct SolveOptions
    : BaseSolveOptions
    , EnumOptions {};

/*!
 * \defgroup facade Facade
 * \brief Simplified interface for (multishot) solving.
 *
 * @{
 */
//! Configuration object for configuring solving via the ClaspFacade.
class ClaspConfig : public BasicSatConfig {
public:
    //! Interface for injecting user-provided propagators and heuristics.
    class Configurator {
    public:
        virtual ~Configurator();
        //! Notifies the configurator that it should detach from the given configuration.
        virtual void detach(const ClaspConfig&);
        //! Adds necessary post-propagators to the given solver.
        [[nodiscard]] virtual bool addPropagators(Solver& s) = 0;
        //! Creates and sets the heuristic to be used in the given solver.
        virtual void setHeuristic(Solver& s) = 0;
    };
    using UserConfig = BasicSatConfig;
    using AspOptions = Asp::LogicProgram::AspOptions;
    ClaspConfig()    = default;
    ~ClaspConfig() override;
    // Base interface
    void           prepare(SharedContext&) override;
    void           reset() override;
    auto config(const char*) -> Configuration* override;
    //! Adds an unfounded set checker to the given solver if necessary.
    bool addPost(Solver& s) const override;
    void setHeuristic(Solver& s) const override;
    // own interface
    [[nodiscard]] auto testerConfig() const -> UserConfig* { return tester_.get(); }
    auto addTesterConfig() -> UserConfig*;
    //! Registers `c` as a configurator to be called when addPost() or setHeuristic() is called.
    void setConfigurator(Configurator* c, bool notifyDetach = true);

    SolveOptions  solve;           //!< Options for solve algorithm and enumerator.
    AspOptions    asp;             //!< Options for asp preprocessing.
    ParserOptions parse;           //!< Options for input parser.
    bool          onlyPre{false};  //!< Prepare program only.
    bool          prepared{false}; //!< Whether prepare() was called on the configuration.
private:
    std::unique_ptr<UserConfig> tester_;
    TaggedPtr<Configurator>     configurator_{nullptr};
};
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspFacade
/////////////////////////////////////////////////////////////////////////////////////////
//! Result of a solving step.
struct SolveResult {
    //! Possible solving results.
    enum Res {
        res_unknown = 0, //!< Satisfiability unknown - a given solve-limit was hit.
        res_sat     = 1, //!< Problem is satisfiable (a model was found).
        res_unsat   = 2, //!< Problem is unsatisfiable.
    };
    //! Additional flags applicable to a solve-result.
    enum Ext {
        ext_exhaust   = 4, //!< Search space is exhausted.
        ext_interrupt = 8, //!< The run was interrupted from outside.
    };
    [[nodiscard]] constexpr bool sat() const { return Potassco::test_any(flags, res_sat); }
    [[nodiscard]] constexpr bool unsat() const { return Potassco::test_any(flags, res_unsat); }
    [[nodiscard]] constexpr bool unknown() const { return static_cast<Res>(*this) == res_unknown; }
    [[nodiscard]] constexpr bool exhausted() const { return Potassco::test_any(flags, ext_exhaust); }
    [[nodiscard]] constexpr bool interrupted() const { return Potassco::test_any(flags, ext_interrupt); }
    constexpr                    operator Res() const { return static_cast<Res>(flags & 3u); }

    uint8_t flags;  //!< Set of Base and Ext flags.
    uint8_t signal; //!< Term signal or 0.
};

//! A bitmask type for representing supported solve modes.
enum class SolveMode : uint32_t {
    def   = 0, //!< Solve synchronously in the current thread.
    async = 1, //!< Solve asynchronously in a worker thread.
    yield = 2, //!< Yield models one by one via a handle.
    async_yield
};
POTASSCO_ENABLE_BIT_OPS(SolveMode);

//! Provides a simplified interface to the services of the clasp library.
class ClaspFacade final
    : public ModelHandler
    , private ClaspConfig::Configurator {
    struct SolveData;
    struct SolveStrategy;

public:
    //! A handle to a possibly asynchronously computed SolveResult.
    class SolveHandle {
    public:
        using Result   = SolveResult;
        using ModelRef = const Model*;
        explicit SolveHandle(SolveStrategy*);
        SolveHandle(const SolveHandle&);
        ~SolveHandle();
        auto operator=(SolveHandle temp) -> SolveHandle& {
            swap(*this, temp);
            return *this;
        }
        friend void swap(SolveHandle& lhs, SolveHandle& rhs) noexcept { std::swap(lhs.strat_, rhs.strat_); }
        /*!
         * \name Blocking functions
         * @{ */
        //! Waits until a result is ready and returns it.
        [[nodiscard]] auto get() const -> Result;
        //! Returns an unsat core if `get()` returned unsat under assumptions.
        [[nodiscard]] auto unsatCore() const -> LitView;
        //! Waits until a result is ready and returns it if it is a model.
        /*!
         * \note If the active solve operation was not started with
         * SolveMode_t::yield, the function always returns nullptr.
         * \note A call to resume() invalidates the returned model and starts
         * the search for the next model.
         */
        [[nodiscard]] auto model() const -> ModelRef;
        //! Waits until a result is ready.
        void wait() const;
        //! Waits for a result but for at most sec seconds.
        [[nodiscard]] bool waitFor(double sec) const;
        //! Tries to cancel the active operation.
        void cancel() const;
        //! Behaves like resume() followed by return model() != nullptr.
        [[nodiscard]] bool next() const;
        //@}
        /*!
         * \name Non-blocking functions
         * @{ */
        //! Tests whether a result is ready.
        [[nodiscard]] bool ready() const;
        //! Tests whether the operation was interrupted and if so returns the interruption signal.
        [[nodiscard]] int interrupted() const;
        //! Tests whether a result is ready and has a stored exception.
        [[nodiscard]] bool error() const;
        //! Tests whether the operation is still active.
        [[nodiscard]] bool running() const;
        //! Releases ownership of the active model and schedules search for the next model.
        void resume() const;
        //@}
    private:
        SolveStrategy* strat_;
    };
    using Result             = SolveResult;
    using AbstractStatistics = Potassco::AbstractStatistics;
    //! Stats key for user-defined (clingo) step statistics.
    static constexpr auto user_step_stats = std::string_view{"user_step"};
    //! Stats key for user-defined (clingo) accu statistics.
    static constexpr auto user_accu_stats = std::string_view{"user_accu"};
    //! Type summarizing one or more solving steps.
    struct Summary {
        using FacadePtr = const ClaspFacade*;
        void init(const ClaspFacade& f);
        //! Logic program elements added in the current step or nullptr if not an asp problem.
        [[nodiscard]] auto lpStep() const -> const Asp::LpStats*;
        //! Logic program stats or nullptr if not an asp problem.
        [[nodiscard]] auto lpStats() const -> const Asp::LpStats*;
        //! Active problem.
        [[nodiscard]] auto ctx() const -> const SharedContext& { return facade->ctx; }
        /*!
         * \name Result functions
         * Solve and enumeration result - not accumulated.
         * @{
         */
        [[nodiscard]] bool         sat() const { return result.sat(); }
        [[nodiscard]] bool         unsat() const { return result.unsat(); }
        [[nodiscard]] bool         complete() const { return result.exhausted(); }
        [[nodiscard]] bool         optimum() const { return hasCosts() && (complete() || model()->opt); }
        [[nodiscard]] auto model() const -> const Model*;
        [[nodiscard]] auto unsatCore() const -> LitView;
        [[nodiscard]] auto consequences() const -> const char*; /**< Cautious/brave reasoning active? */
        [[nodiscard]] bool         optimize() const;     /**< Optimization active? */
        [[nodiscard]] auto costs() const -> SumView;        /**< Models have associated costs? */
        [[nodiscard]] auto optimal() const -> uint64_t;      /**< Number of optimal models found. */
        [[nodiscard]] bool         hasCosts() const;
        [[nodiscard]] bool         hasLower() const;
        [[nodiscard]] auto lower() const -> SumView;
        //@}
        //! Visits this summary object and all associated statistics (including any user-added clingo stats).
        void      accept(StatsVisitor& out) const;
        FacadePtr facade;     //!< Facade object of this run.
        double    totalTime;  //!< Total wall clock time.
        double    cpuTime;    //!< Total cpu time.
        double    solveTime;  //!< Wall clock time for solving.
        double    unsatTime;  //!< Wall clock time to prove unsat.
        double    satTime;    //!< Wall clock time to the first model.
        double    killTime;   //!< Wall clock time for (async) shutdown.
        uint64_t  numEnum;    //!< Total models enumerated.
        uint64_t  numOptimal; //!< Optimal models enumerated.
        uint32_t  step;       //!< Step number (multishot solving).
        Result    result;     //!< Result of the step.
    };
    ClaspFacade();
    ~ClaspFacade() override;

    /*!
     * \name Query functions.
     * Functions for checking the state of this object.
     * @{ */
    //! Returns whether the problem is still valid.
    [[nodiscard]] bool ok() const { return program() ? program()->ok() : ctx.ok(); }
    //! Returns whether the active step is ready for solving.
    [[nodiscard]] bool prepared() const;
    //! Returns whether the active step is currently being solved.
    [[nodiscard]] bool solving() const;
    //! Returns whether the active step has been solved, i.e., has a result.
    [[nodiscard]] bool solved() const;
    //! Returns whether solving of the active step was interrupted.
    [[nodiscard]] bool interrupted() const;
    //! Returns the summary of the active step.
    [[nodiscard]] auto summary() const -> const Summary& { return step_; }
    //! Returns the summary of the active (accu = false) or all steps.
    [[nodiscard]] auto summary(bool accu) const -> const Summary&;
    //! Returns solving statistics or throws std::logic_error if solving() is true.
    [[nodiscard]] auto getStats() const -> AbstractStatistics*;
    //! Returns the active configuration.
    [[nodiscard]] auto config() const -> const ClaspConfig* { return config_; }
    //! Returns the current solving step (starts at 0).
    [[nodiscard]] int step() const { return static_cast<int>(step_.step); }
    //! Returns the result of the active step (unknown if run is not yet completed).
    [[nodiscard]] auto result() const -> Result { return step_.result; }
    //! Returns the active program or nullptr if it was already released.
    [[nodiscard]] auto program() const -> ProgramBuilder* { return builder_.get(); }
    //! Returns the active program if it is of type Asp::LogicProgram.
    [[nodiscard]] auto asp() const -> Asp::LogicProgram*;
    //! Returns whether program updates are enabled.
    [[nodiscard]] bool incremental() const;
    //! Returns the active enumerator or nullptr if there is none.
    [[nodiscard]] auto enumerator() const -> Enumerator*;
    //@}

    //! Event type used to signal that a new step has started.
    struct StepStart : Event {
        explicit StepStart(const ClaspFacade& f) : Event(this, subsystem_facade, verbosity_quiet), facade(&f) {}
        const ClaspFacade* facade;
    };
    //! Event type used to signal that a solve-step has terminated.
    struct StepReady : Event {
        explicit StepReady(const Summary& x) : Event(this, subsystem_facade, verbosity_quiet), summary(&x) {}
        const Summary* summary;
    };
    //! Event type used to signal that a problem is being prepared it for solving.
    struct Prepare : Event {
        explicit Prepare(ClaspFacade& f) : Event(this, subsystem_facade, verbosity_quiet), facade(&f) {}
        ClaspFacade* facade;
    };

    SharedContext ctx; //!< Context-object used to store a problem.

    /*!
     * \name Start functions.
     * Functions for defining a problem.
     * Calling one of the start functions discards any previous problem and emits a StepStart event.
     * \note The start functions register the facade as configurator with the given config.
     *
     * @{ */
    //! Starts definition of an ASP problem.
    Asp::LogicProgram& startAsp(ClaspConfig& config, bool enableProgramUpdates = false);
    //! Starts definition of a SAT problem.
    auto startSat(ClaspConfig& config) -> SatBuilder&;
    //! Starts definition of a PB problem.
    auto startPB(ClaspConfig& config) -> PBBuilder&;
    //! Starts definition of a problem of type `t`.
    auto start(ClaspConfig& config, ProblemType t) -> ProgramBuilder&;
    //! Starts definition of a problem given in `stream`.
    auto start(ClaspConfig& config, std::istream& stream) -> ProgramBuilder&;
    //! Enables support for program updates if supported by the program.
    /*!
     * \pre program() != nullptr and not prepared().
     * \return whether program updates are supported.
     */
    bool enableProgramUpdates();
    //! Enables support for (asynchronous) solve interrupts.
    void enableSolveInterrupts();
    //! Disables program disposal in non-incremental mode after a problem has been prepared for solving.
    /*!
     * \pre program() != nullptr and not prepared().
     */
    void keepProgram();
    //! Tries to detect the problem type from the given input stream.
    static auto detectProblemType(std::istream& str) -> ProblemType;
    //! Tries to read the next program part from the stream passed to start().
    /*!
     * \return false if nothing was read because the stream is exhausted, solving was interrupted,
     * or the problem is unconditionally unsat.
     */
    bool read();

    //! Registers the given propagator.
    /*!
     * The facade will add a corresponding post-propagator to all solvers.
     * \param prop The propagator to add.
     * \param distinctTrue Whether the propagator requires a distinct true literal for each solving step.
     */
    void registerPropagator(Potassco::AbstractPropagator& prop, bool distinctTrue);

    //! Registers the given heuristic.
    /*!
     * The facade will decorate the decision heuristic of all solvers so that the given heuristic is called, whenever
     * a new decision is made.
     */
    void registerHeuristic(Potassco::AbstractHeuristic& heuristic);

    //@}

    /*!
     * \name Solve functions.
     * Functions for solving a problem.
     * @{ */

    enum EnumMode { enum_volatile, enum_static };

    //! Finishes the definition of a problem and prepares it for solving.
    /*!
     * \pre !solving()
     * \post prepared() || !ok() || config()->onlyPre
     * \param m Mode to be used for handling enumeration-related knowledge.
     *          If m is enum_volatile, enumeration knowledge is learnt under an
     *          assumption retracted on program update. Otherwise,
     *          no special assumption is used and enumeration-related knowledge
     *          might become unretractable.
     * \return prepared()
     * \note If solved() is true, prepare() first starts a new solving step.
     * \note If config()->onlyPre, prepare() only finishes the definition of the program.
     */
    bool prepare(EnumMode m = enum_volatile);

    //! Solves the current problem.
    /*!
     * If prepared() is false, the function first calls prepare() to prepare the problem for solving.
     * \pre !solving() and !config()->onlyPre
     * \post solved()
     * \param a A list of unit-assumptions under which solving should operate.
     * \param eh An optional event handler that is notified on each model and
     *           once the solve operation has completed.
     */
    Result solve(LitView a = {}, EventHandler* eh = nullptr);
    auto solve(EventHandler* eh) -> Result { return solve({}, eh); }

    //! Solves the current problem using the given solve-mode.
    /*!
     * If prepared() is false, the function first calls prepare() to prepare the problem for solving.
     * \pre !solving()
     * \param mode The solve-mode to use.
     * \param a A list of unit-assumptions under which solving should operate.
     * \param eh An optional event handler that is notified on each model and
     *           once the solve operation has completed.
     * \throws std::logic_error   if mode contains SolveMode_t::async but thread support is disabled.
     * \throws std::runtime_error if mode contains SolveMode_t::async but solve is unable to start a thread.
     *
     * \note If `mode` contains SolveMode_t::async, the optional event handler is notified in the
     *       context of the asynchronous thread.
     *
     * \note If `mode` contains SolveMode_t::yield, models are signaled one by one via the
     *       returned handle object.
     *       It is the caller's responsibility to finish the solve operation,
     *       either by extracting models until SolveHandle::model() returns nullptr, or
     *       by calling SolveHandle::cancel().
     *
     * To iterate over models one by one, use a loop like:
     * \code
     * SolveMode_t p = ...
     * for (auto it = facade.solve(p|SolveMode_t::yield); it.model(); it.resume()) {
     *   printModel(*it.model());
     * }
     * \endcode
     */
    SolveHandle solve(SolveMode mode, LitView a = {}, EventHandler* eh = nullptr);

    //! Tries to interrupt the active solve operation.
    /*!
     * The function sends the given signal to the active solve operation.
     * If no solve operation is active (i.e., solving() is false), the signal
     * is queued and applied to the next solve operation.
     *
     * \param sig The signal to raise or 0, to re-raise a previously queued signal.
     * \return false if no operation was interrupted, because
     *         there is no active solve operation,
     *         or the operation does not support interrupts,
     *         or sig was 0 and there was no queued signal.
     *
     * \see enableSolveInterrupts()
     */
    bool interrupt(int sig);

    //! Forces termination of the current solving step.
    /*!
     * \post solved()
     * \return summary(true)
     */
    auto shutdown() -> const Summary&;

    //! Starts update of the active problem and/or configuration if necessary.
    /*!
     * The function updates the configuration if it is marked as "unprepared" (i.e., dirty) and unfreezes the active
     * problem if it is currently frozen.
     * \pre solving() is false, and either program updates are enabled or prepared() is false.
     * \post !prepared()
     * \param sigQ An action to be performed for any queued signal. The default is to apply the signal in the next
     *             solve operation. SIGN_IGN can be used to discard queued signals.
     * \return ok()
     */
    bool update(void (*sigQ)(int) = SIG_DFL);
    //@}
private:
    struct Statistics;
    using SolvePtr    = std::unique_ptr<SolveData>;
    using BuilderPtr  = std::unique_ptr<ProgramBuilder>;
    using SummaryPtr  = std::unique_ptr<Summary>;
    using StatsPtr    = std::unique_ptr<Statistics>;
    using PropInitVec = PodVector_t<Potassco::AbstractPropagator::Init*>;
    using HeuPtr      = std::unique_ptr<Potassco::AbstractHeuristic>;
    void         init(ClaspConfig& cfg);
    void         detach(const ClaspConfig& cfg) override;
    bool         addPropagators(Solver& s) override;
    void         setHeuristic(Solver& s) override;
    auto         initBuilder(ClaspConfig& cfg, std::unique_ptr<ProgramBuilder> in, ProblemType t) -> ProgramBuilder&;
    void         discardProblem();
    void         startStep(uint32_t num);
    auto stopStep(int signal, bool complete) -> Result;
    void         updateStats();
    bool         onModel(const Solver& s, const Model& m) override;
    bool         onUnsat(const Solver& s, const Model& m) override;
    void         doUpdate(ProgramBuilder* p, void (*sig)(int));
    ProblemType  type_{};
    Summary      step_{};
    LitVec       assume_;
    SumVec       lower_;
    ClaspConfig* config_ = nullptr;
    BuilderPtr   builder_;
    PropInitVec  propagators_;
    HeuPtr       heuristic_;
    SummaryPtr   accu_;
    StatsPtr     stats_; // statistics: only if requested
    SolvePtr     solve_; // NOTE: last so that it is destroyed first;
};

/**
 * \example example2.cpp
 * This is an example of how to use the ClaspFacade class for basic solving.
 *
 * \example example3.cpp
 * This is an example of how to use the ClaspFacade class for generator-based solving.
 */

//!@}

} // namespace Clasp
