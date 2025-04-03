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

#include <clasp/config.h>
#if !CLASP_HAS_THREADS
#error Thread support required for parallel solving
#endif
#include <clasp/constraint.h>
#include <clasp/mt/thread.h>
#include <clasp/shared_context.h>
#include <clasp/solve_algorithms.h>
#include <clasp/solver_types.h>

/*!
 * \file
 * \brief Defines classes controlling multithreaded parallel solving.
 */
//! Namespace for types and functions needed for implementing multithreaded parallel solving.
namespace Clasp::mt {

/**
 * \defgroup mt Multi-threading
 * \brief Parallel solving and related classes.
 * \ingroup enumerator
 */
//@{

class ParallelHandler;
class ParallelSolve;

//! Options for controlling parallel solving.
struct ParallelSolveOptions : BasicSolveOptions {
    //! Nogood distribution options.
    struct Distribution : Distributor::Policy {
        enum Mode { mode_global = 0, mode_local = 1 };
        Distribution(Mode m = mode_global) : mode(m) {}
        Policy&  policy() { return *this; }
        uint32_t mode;
    };
    ParallelSolveOptions() = default;
    //! Algorithm options.
    struct Algorithm {
        //! Possible search strategies.
        enum SearchMode { mode_split = 0, mode_compete = 1 };
        uint32_t   threads{1};
        SearchMode mode{mode_compete};
    };
    //! Nogood integration options.
    struct Integration {
        static constexpr uint32_t grace_max = (1u << 28) - 1;
        enum Filter { filter_no = 0, filter_gp = 1, filter_sat = 2, filter_heuristic = 3 };
        enum Topology { topo_all = 0, topo_ring = 1, topo_cube = 2, topo_cubex = 3 };
        uint32_t grace  : 28 {1024};     /**< Lower bound on number of shared nogoods to keep. */
        uint32_t filter : 2 {filter_gp}; /**< Filter for integrating shared nogoods (one of Filter). */
        uint32_t topo   : 2 {topo_all};  /**< Integration topology */
    };
    //! Global restart options.
    struct GRestarts {
        uint32_t         maxR{0};
        ScheduleStrategy sched;
    };
    Integration  integrate;  //!< Nogood integration options to apply during search.
    Distribution distribute; //!< Nogood distribution options to apply during search.
    GRestarts    restarts;   //!< Global restart strategy to apply during search.
    Algorithm    algorithm;  //!< Parallel algorithm to use.
    //! Allocates a new solve object.
    [[nodiscard]] SolveAlgorithm* createSolveObject() const;
    //! Returns the number of threads that can run concurrently on the current hardware.
    static uint32_t recommendedSolvers() { return Clasp::mt::thread::hardware_concurrency(); }
    //! Returns number of maximal number of supported threads.
    static uint32_t supportedSolvers() { return 64; }
    //! Returns the peers of the solver with the given id assuming the given topology.
    static SolverSet initPeerSet(uint32_t sId, Integration::Topology topo, uint32_t numThreads);
    //! Returns all peers of the solver with the given id.
    static constexpr SolverSet fullPeerSet(uint32_t sId, uint32_t numThreads) {
        return SolverSet::fromRep(Potassco::toggle_bit(Potassco::bit_max<uint64_t>(numThreads), sId));
    }
    [[nodiscard]] uint32_t numSolver() const { return algorithm.threads; }
    void                   setSolvers(uint32_t i) { algorithm.threads = std::max(1u, i); }
    [[nodiscard]] bool     defaultPortfolio() const { return algorithm.mode == Algorithm::mode_compete; }
};

//! A parallel algorithm for multithreaded solving with and without search-space splitting.
/*!
 * The class adapts clasp's basic solve algorithm to a parallel solve algorithm
 * that solves a problem using a given number of threads.
 * It supports guiding path based solving, portfolio based solving, as well
 * as a combination of these two approaches.
 */
class ParallelSolve : public SolveAlgorithm {
public:
    explicit ParallelSolve(const ParallelSolveOptions& opts);
    ~ParallelSolve() override;
    ParallelSolve(ParallelSolve&&) = delete;
    // base interface
    [[nodiscard]] bool interrupted() const override;
    void               resetSolve() override;
    void               enableInterrupts() override;
    // own interface
    //! Returns the number of active threads.
    [[nodiscard]] uint32_t numThreads() const;
    [[nodiscard]] bool     integrateUseHeuristic() const { return Potassco::test_bit(intFlags_, 31); }
    [[nodiscard]] uint32_t integrateGrace() const { return intGrace_; }
    [[nodiscard]] uint32_t integrateFlags() const { return intFlags_; }
    [[nodiscard]] uint64_t hasErrors() const;
    //! Requests a global restart.
    void requestRestart();
    bool handleMessages(Solver& s);
    bool integrateModels(Solver& s, uint32_t& mCount);
    void pushWork(LitView path);
    bool commitModel(Solver& s);
    bool commitUnsat(Solver& s);
    enum GpType { gp_none = 0, gp_split = 1, gp_fixed = 2 };

private:
    // -------------------------------------------------------------------------------------------
    // Thread setup
    void destroyThread(uint32_t id);
    void allocThread(uint32_t id, Solver& s);
    int  joinThreads();
    // -------------------------------------------------------------------------------------------
    // Algorithm steps
    void setIntegrate(uint32_t grace, uint8_t filter);
    void setRestarts(uint32_t maxR, const ScheduleStrategy& rs);
    bool beginSolve(SharedContext& ctx, LitView assume);
    bool doSolve(SharedContext& ctx, LitView assume) override;
    void doStart(SharedContext& ctx, LitView assume) override;
    auto doNext(Val_t last) -> Val_t override;
    void doStop() override;
    void doDetach() override;
    bool doInterrupt() override;
    void solveParallel(uint32_t id);
    void initQueue();
    bool requestWork(Solver& s, Path& out);
    void terminate(const Solver& s, bool complete);
    bool waitOnSync(const Solver& s);
    void exception(uint32_t id, Path path, int err, const char* what);
    void reportProgress(const Event& ev) const;
    void reportProgress(const Solver& s, const char* msg) const;
    // -------------------------------------------------------------------------------------------
    using Distribution = ParallelSolveOptions::Distribution;
    struct SharedData;
    using DataPtr    = std::unique_ptr<SharedData>;
    using HandlerPtr = std::unique_ptr<ParallelHandler>;
    using ControlPtr = std::unique_ptr<HandlerPtr[]>;
    // SHARED DATA
    DataPtr    shared_; // Shared control data
    ControlPtr thread_; // Thread-local control data
    // READ ONLY
    Distribution distribution_;  // distribution options
    uint32_t     maxRestarts_;   // disable global restarts once reached
    uint32_t     intGrace_ : 30; // grace period for clauses to integrate
    uint32_t     intTopo_  : 2;  // integration topology
    uint32_t     intFlags_;      // bitset controlling clause integration
    bool         modeSplit_;
};
//! An event type for debugging messages sent between threads.
struct MessageEvent : SolveEvent {
    enum Action { sent, received, completed };
    MessageEvent(const Solver& s, const char* message, Action a, double t = 0.0)
        : SolveEvent(this, s, verbosity_high)
        , msg(message)
        , time(t) {
        op = static_cast<uint32_t>(a);
    }
    const char* msg;  // name of message
    double      time; // only for action completed
};
//! A per-solver (i.e. thread) class that implements message handling and knowledge integration.
/*!
 * The class adds itself as a post propagator to the given solver. During propagation,
 * it checks for new messages and lemmas to integrate.
 */
class ParallelHandler final : public MessageHandler {
public:
    using GpType = ParallelSolve::GpType;

    //! Creates a new parallel handler to be used in the given solve group.
    /*!
     * \param ctrl The object controlling the parallel solve operation.
     * \param s    The solver that is to be controlled by this object.
     */
    explicit ParallelHandler(ParallelSolve& ctrl, Solver& s);
    ~ParallelHandler() override;
    //! Attaches the object's solver to ctx and adds this object as a post propagator.
    bool attach(SharedContext& ctx);
    //! Removes this object from the list of post propagators of its solver and detaches the solver from ctx.
    void detach(SharedContext& ctx, bool fastExit);

    bool               setError(int e);
    [[nodiscard]] int  error() const;
    void               setWinner();
    [[nodiscard]] bool winner() const;

    //! True if *this has an associated thread of execution, false otherwise.
    [[nodiscard]] bool joinable() const;
    void               setThread(Clasp::mt::thread x);
    //! Waits for the thread of execution associated with *this to finish.
    int join();

    // overridden methods

    //! Integrates new information.
    bool propagateFixpoint(Solver& s, PostPropagator*) override;
    bool handleMessages() override;
    void reset() override;
    bool simplify(Solver& s, bool shuffle) override;
    //! Checks whether new information has invalidated current model.
    bool isModel(Solver& s) override;

    // own interface
    bool isModelLocked(Solver& s);

    //! Returns true if handler has a guiding path.
    [[nodiscard]] bool hasPath() const;
    [[nodiscard]] bool disjointPath() const;
    void               setGpType(GpType t);

    //! Entry point for solving the given guiding path.
    /*!
     * \param solve   The object used for solving.
     * \param type    The guiding path's type.
     * \param restart Request restart after restart number of conflicts.
     */
    Val_t solveGP(BasicSolve& solve, GpType type, uint64_t restart);

    /*!
     * \name Message handlers
     * \note
     *   Message handlers are intended as callbacks for ParallelSolve::handleMessages().
     *   They shall not change the assignment of the solver object.
     */
    //@{

    //! Algorithm is about to terminate.
    /*!
     * Removes this object from the solver's list of post propagators.
     */
    void handleTerminateMessage();

    //! Request for split.
    /*!
     * Splits off a new guiding path and adds it to the control object.
     * \pre The guiding path of this object is "splittable"
     */
    void handleSplitMessage();

    //! Request for (global) restart.
    /*!
     * \return true if restart is valid, else false.
     */
    bool handleRestartMessage();

    Solver& solver();
    //@}

    void* operator new(std::size_t count);
    void  operator delete(void* ptr, std::size_t sz);

private:
    using ClauseDB  = PodVector_t<Constraint*>;
    using RecBuffer = std::unique_ptr<SharedLiterals*[]>;
    void add(ClauseHead* h);
    void clearDB(Solver* s);
    bool integrate(Solver& s);
    struct GP {
        uint64_t restart  = UINT64_MAX;             // don't give up before restart number of conflicts
        uint32_t modCount = 0;                      // integration counter for synchronizing models
        GpType   type     = ParallelSolve::gp_none; // type of gp
    };
    thread         thread_;     // active thread or empty for master
    GP             gp_;         // active guiding path
    LitVec         temp_;       // buffer for splitting
    ParallelSolve* ctrl_;       // message source
    Solver*        solver_;     // associated solver
    RecBuffer      received_;   // received clauses not yet integrated
    ClauseDB       integrated_; // integrated clauses
    uint32_t       recEnd_;     // where to put next received clause
    uint32_t       intEnd_;     // where to put next clause
    uint32_t       error_ : 28; // error code or 0 if ok
    uint32_t       win_   : 1;  // 1 if thread was the first to terminate the search
    uint32_t       up_    : 1;  // 1 if next propagate should check for new lemmas/models
    uint32_t       act_   : 1;  // 1 if gp is active
    uint32_t       lbd_   : 1;  // 1 if integrate should compute lbds
};
//! A class that uses a global list to exchange nogoods between threads.
class GlobalDistribution final : public Distributor {
public:
    explicit GlobalDistribution(const Policy& p, uint32_t maxShare, uint32_t topo);
    ~GlobalDistribution() override;
    uint32_t receive(const Solver& in, SharedLiterals** out, uint32_t maxOut) override;
    void     publish(const Solver& source, SharedLiterals* n) override;

private:
    class Queue;
    std::unique_ptr<Queue> queue_;
};
//! A class that uses thread-local lists to exchange nogoods between threads.
class LocalDistribution final : public Distributor {
public:
    explicit LocalDistribution(const Policy& p, uint32_t maxShare, uint32_t topo);
    ~LocalDistribution() override;
    uint32_t receive(const Solver& in, SharedLiterals** out, uint32_t maxOut) override;
    void     publish(const Solver& source, SharedLiterals* n) override;

private:
    struct ThreadData;
    using ThreadPtr   = std::unique_ptr<ThreadData>;
    using ThreadArray = std::unique_ptr<ThreadPtr[]>;
    ThreadArray thread_;    // one entry for each thread
    uint32_t    numThread_; // number of threads, i.e. size of array thread_
};
//@}
} // namespace Clasp::mt
