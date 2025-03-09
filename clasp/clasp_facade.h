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

namespace Clasp {
//! Options for controlling enumeration and solving.
struct SolveOptions
    : mt::ParallelSolveOptions
    , EnumOptions {};
} // namespace Clasp
#else
#include <clasp/solve_algorithms.h>
namespace Clasp {
struct SolveOptions
    : BasicSolveOptions
    , EnumOptions {};
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
 * I.e. a simplified interface for (multishot) solving a problem using
 * some configuration (set of parameters).
 * \ingroup facade
 */
namespace Clasp {
/////////////////////////////////////////////////////////////////////////////////////////
// Configuration
/////////////////////////////////////////////////////////////////////////////////////////
/*!
 * \defgroup facade Facade
 * \brief Simplified interface for (multishot) solving.
 *
 * @{
 */
//! Configuration object for configuring solving via the ClaspFacade.
class ClaspConfig : public BasicSatConfig {
public:
    //! Interface for injecting user-provided configurations.
    class Configurator {
    public:
        virtual ~Configurator();
        virtual void prepare(SharedContext&);
        virtual bool applyConfig(Solver& s) = 0;
        virtual void unfreeze(SharedContext&);
    };
    using UserConfig = BasicSatConfig;
    using AspOptions = Asp::LogicProgram::AspOptions;
    ClaspConfig();
    ~ClaspConfig() override;
    // Base interface
    void           prepare(SharedContext&) override;
    void           reset() override;
    Configuration* config(const char*) override;
    //! Adds an unfounded set checker to the given solver if necessary.
    /*!
     * If asp.suppMod is false and the problem in s is a non-tight asp-problem,
     * the function adds an unfounded set checker to s.
     */
    bool addPost(Solver& s) const override;
    // own interface
    [[nodiscard]] UserConfig* testerConfig() const { return tester_.get(); }
    UserConfig*               addTesterConfig();
    //! Registers c as additional callback for when addPost() is called.
    /*!
     * \param c    Additional configuration to apply.
     * \param once Whether c should be called once in the first step or also in each subsequent step.
     */
    void          addConfigurator(Configurator& c, bool once = true);
    void          unfreeze(SharedContext&);
    SolveOptions  solve; //!< Options for solve algorithm and enumerator.
    AspOptions    asp;   //!< Options for asp preprocessing.
    ParserOptions parse; //!< Options for input parser.
private:
    struct Impl;
    std::unique_ptr<UserConfig> tester_;
    std::unique_ptr<Impl>       impl_;
};
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspFacade
/////////////////////////////////////////////////////////////////////////////////////////
//! Result of a solving step.
struct SolveResult {
    //! Possible solving results.
    enum Res {
        res_unknown = 0, //!< Satisfiability unknown - a given solve limit was hit.
        res_sat     = 1, //!< Problem is satisfiable (a model was found).
        res_unsat   = 2, //!< Problem is unsatisfiable.
    };
    //! Additional flags applicable to a solve result.
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
    def   = 0, //!< Solve synchronously in current thread.
    async = 1, //!< Solve asynchronously in worker thread.
    yield = 2, //!< Yield models one by one via handle.
    async_yield
};
POTASSCO_ENABLE_BIT_OPS(SolveMode);

//! Provides a simplified interface to the services of the clasp library.
class ClaspFacade final : public ModelHandler {
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
        SolveHandle& operator=(SolveHandle temp) {
            swap(*this, temp);
            return *this;
        }
        friend void swap(SolveHandle& lhs, SolveHandle& rhs) noexcept { std::swap(lhs.strat_, rhs.strat_); }
        /*!
         * \name Blocking functions
         * @{ */
        //! Waits until a result is ready and returns it.
        [[nodiscard]] Result get() const;
        //! Returns an unsat core if `get()` returned unsat under assumptions.
        [[nodiscard]] LitView unsatCore() const;
        //! Waits until a result is ready and returns it if it is a model.
        /*!
         * \note If the active solve operation was not started with
         * SolveMode_t::yield, the function always returns nullptr.
         * \note A call to resume() invalidates the returned model and starts
         * the search for the next model.
         */
        [[nodiscard]] ModelRef model() const;
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
    //! Type summarizing one or more solving steps.
    struct Summary {
        using FacadePtr = const ClaspFacade*;
        void init(ClaspFacade& f);
        //! Logic program elements added in the current step or nullptr if not an asp problem.
        [[nodiscard]] const Asp::LpStats* lpStep() const;
        //! Logic program stats or nullptr if not an asp problem.
        [[nodiscard]] const Asp::LpStats* lpStats() const;
        //! Active problem.
        [[nodiscard]] const SharedContext& ctx() const { return facade->ctx; }
        /*!
         * \name Result functions
         * Solve and enumeration result - not accumulated.
         * @{
         */
        [[nodiscard]] bool         sat() const { return result.sat(); }
        [[nodiscard]] bool         unsat() const { return result.unsat(); }
        [[nodiscard]] bool         complete() const { return result.exhausted(); }
        [[nodiscard]] bool         optimum() const { return hasCosts() && (complete() || model()->opt); }
        [[nodiscard]] const Model* model() const;
        [[nodiscard]] LitView      unsatCore() const;
        [[nodiscard]] const char*  consequences() const; /**< Cautious/brave reasoning active? */
        [[nodiscard]] bool         optimize() const;     /**< Optimization active? */
        [[nodiscard]] SumView      costs() const;        /**< Models have associated costs? */
        [[nodiscard]] uint64_t     optimal() const;      /**< Number of optimal models found. */
        [[nodiscard]] bool         hasCosts() const;
        [[nodiscard]] bool         hasLower() const;
        [[nodiscard]] SumView      lower() const;
        //@}
        //! Visits this summary object.
        void      accept(StatsVisitor& out) const;
        FacadePtr facade;     //!< Facade object of this run.
        double    totalTime;  //!< Total wall clock time.
        double    cpuTime;    //!< Total cpu time.
        double    solveTime;  //!< Wall clock time for solving.
        double    unsatTime;  //!< Wall clock time to prove unsat.
        double    satTime;    //!< Wall clock time to first model.
        uint64_t  numEnum;    //!< Total models enumerated.
        uint64_t  numOptimal; //!< Optimal models enumerated.
        uint32_t  step;       //!< Step number (multishot solving).
        Result    result;     //!< Result of step.
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
    [[nodiscard]] const Summary& summary() const { return step_; }
    //! Returns the summary of the active (accu = false) or all steps.
    [[nodiscard]] const Summary& summary(bool accu) const;
    //! Returns solving statistics or throws std::logic_error if solving() is true.
    [[nodiscard]] AbstractStatistics* getStats() const;
    //! Returns the active configuration.
    [[nodiscard]] const ClaspConfig* config() const { return config_; }
    //! Returns the current solving step (starts at 0).
    [[nodiscard]] int step() const { return static_cast<int>(step_.step); }
    //! Returns the result of the active step (unknown if run is not yet completed).
    [[nodiscard]] Result result() const { return step_.result; }
    //! Returns the active program or nullptr if it was already released.
    [[nodiscard]] ProgramBuilder* program() const { return builder_.get(); }
    //! Returns the active program if it is of type Asp::LogicProgram.
    [[nodiscard]] Asp::LogicProgram* asp() const;
    //! Returns whether program updates are enabled.
    [[nodiscard]] bool incremental() const;
    //! Returns the active enumerator or nullptr if there is none.
    [[nodiscard]] Enumerator* enumerator() const;
    //@}

    //! Event type used to signal that a new step has started.
    struct StepStart : Event {
        explicit StepStart(const ClaspFacade& f) : Event(this, subsystem_facade, verbosity_quiet), facade(&f) {}
        const ClaspFacade* facade;
    };
    //! Event type used to signal that a solve step has terminated.
    struct StepReady : Event {
        explicit StepReady(const Summary& x) : Event(this, subsystem_facade, verbosity_quiet), summary(&x) {}
        const Summary* summary;
    };

    SharedContext ctx; //!< Context-object used to store problem.

    /*!
     * \name Start functions.
     * Functions for defining a problem.
     * Calling one of the start functions discards any previous problem
     * and emits a StepStart event.
     * @{ */
    //! Starts definition of an ASP-problem.
    Asp::LogicProgram& startAsp(ClaspConfig& config, bool enableProgramUpdates = false);
    //! Starts definition of a SAT-problem.
    SatBuilder& startSat(ClaspConfig& config);
    //! Starts definition of a PB-problem.
    PBBuilder& startPB(ClaspConfig& config);
    //! Starts definition of a problem of type t.
    ProgramBuilder& start(ClaspConfig& config, ProblemType t);
    //! Starts definition of a problem given in stream.
    ProgramBuilder& start(ClaspConfig& config, std::istream& stream);
    //! Enables support for program updates if supported by the program.
    /*!
     * \pre program() != nullptr and not prepared().
     * \return true if program updates are supported. Otherwise, false.
     */
    bool enableProgramUpdates();
    //! Enables support for (asynchronous) solve interrupts.
    void enableSolveInterrupts();
    //! Disables program disposal in non-incremental mode after problem has been prepared for solving.
    /*!
     * \pre program() != nullptr and not prepared().
     */
    void keepProgram();
    //! Tries to detect the problem type from the given input stream.
    static ProblemType detectProblemType(std::istream& str);
    //! Tries to read the next program part from the stream passed to start().
    /*!
     * \return false if nothing was read because the stream is exhausted, solving was interrupted,
     * or the problem is unconditionally unsat.
     */
    bool read();

    //@}

    /*!
     * \name Solve functions.
     * Functions for solving a problem.
     * @{ */

    enum EnumMode { enum_volatile, enum_static };

    //! Finishes the definition of a problem and prepares it for solving.
    /*!
     * \pre !solving()
     * \post prepared() || !ok()
     * \param m Mode to be used for handling enumeration-related knowledge.
     *          If m is enum_volatile, enumeration knowledge is learnt under an
     *          assumption that is retracted on program update. Otherwise,
     *          no special assumption is used and enumeration-related knowledge
     *          might become unretractable.
     * \note If solved() is true, prepare() first starts a new solving step.
     */
    void prepare(EnumMode m = enum_volatile);

    //! Solves the current problem.
    /*!
     * If prepared() is false, the function first calls prepare() to prepare the problem for solving.
     * \pre !solving()
     * \post solved()
     * \param a A list of unit-assumptions under which solving should operate.
     * \param eh An optional event handler that is notified on each model and
     *           once the solve operation has completed.
     */
    Result solve(LitView a = {}, EventHandler* eh = nullptr);
    Result solve(EventHandler* eh) { return solve({}, eh); }

    //! Solves the current problem using the given solve mode.
    /*!
     * If prepared() is false, the function first calls prepare() to prepare the problem for solving.
     * \pre !solving()
     * \param mode The solve mode to use.
     * \param a A list of unit-assumptions under which solving should operate.
     * \param eh An optional event handler that is notified on each model and
     *           once the solve operation has completed.
     * \throws std::logic_error   if mode contains SolveMode_t::async but thread support is disabled.
     * \throws std::runtime_error if mode contains SolveMode_t::async but solve is unable to start a thread.
     *
     * \note If mode contains SolveMode_t::async, the optional event handler is notified in the
     *       context of the asynchronous thread.
     *
     * \note If mode contains SolveMode_t::yield, models are signaled one by one via the
     *       returned handle object.
     *       It is the caller's responsibility to finish the solve operation,
     *       either by extracting models until SolveHandle::model() returns nullptr, or
     *       by calling SolveHandle::cancel().
     *
     * To iterate over models one by one use a loop like:
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
     * If no solve operation is active (i.e. solving() is false), the signal
     * is queued and applied to the next solve operation.
     *
     * \param sig The signal to raise or 0, to re-raises a previously queued signal.
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
    const Summary& shutdown();

    //! Starts update of the active problem.
    /*!
     * \pre solving() is false and program updates are enabled (incremental() is true).
     * \post !solved()
     * \param updateConfig If true, the function applies any configuration changes.
     * \param sigQ An action to be performed for any queued signal.
     *        The default is to apply the signal to the next solve operation, while
     *        SIGN_IGN can be used to discard queued signals.
     */
    ProgramBuilder& update(bool updateConfig, void (*sigQ)(int));
    ProgramBuilder& update(bool updateConfig = false) { return update(updateConfig, SIG_DFL); }
    //@}
private:
    struct Statistics;
    using SolvePtr   = std::unique_ptr<SolveData>;
    using BuilderPtr = std::unique_ptr<ProgramBuilder>;
    using SummaryPtr = std::unique_ptr<Summary>;
    using StatsPtr   = std::unique_ptr<Statistics>;
    void         init(ClaspConfig& cfg, bool discardProblem);
    void         initBuilder(ProgramBuilder* in);
    void         discardProblem();
    void         startStep(uint32_t num);
    Result       stopStep(int signal, bool complete);
    void         updateStats();
    bool         onModel(const Solver& s, const Model& m) override;
    void         doUpdate(ProgramBuilder* p, bool updateConfig, void (*sig)(int));
    ProblemType  type_{};
    Summary      step_{};
    LitVec       assume_;
    SumVec       lower_;
    ClaspConfig* config_ = nullptr;
    BuilderPtr   builder_;
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
