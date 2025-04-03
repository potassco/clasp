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
#include <clasp/mt/parallel_solve.h>

#include <clasp/clause.h>
#include <clasp/enumerator.h>
#include <clasp/solver.h>
#include <clasp/util/multi_queue.h>
#include <clasp/util/timer.h>

#include <potassco/error.h>

#include <amc/vector.hpp>

#include <memory>
#include <string>

namespace Clasp::mt {
/////////////////////////////////////////////////////////////////////////////////////////
// ParallelSolve::SharedData
/////////////////////////////////////////////////////////////////////////////////////////
struct ParallelSolve::SharedData {
    static_assert(amc::is_trivially_relocatable_v<Path>);
    using PathQueue    = std::pair<amc::vector<Path>, uint32_t>;
    using ConditionVar = condition_variable;
    enum MsgFlag : uint32_t {
        terminate_flag         = 1u,
        sync_flag              = 2u,
        split_flag             = 4u,
        restart_flag           = 8u,
        complete_flag          = 16u,
        interrupt_flag         = 32u,  // set on terminate from outside
        allow_split_flag       = 64u,  // set if splitting mode is active
        forbid_restart_flag    = 128u, // set if restarts are no longer allowed
        cancel_restart_flag    = 256u, // set if current restart request was cancelled by some thread
        restart_abandoned_flag = 512u, // set to signal that threads must not give up their gp
    };
    enum Message : uint32_t {
        msg_terminate    = terminate_flag,
        msg_interrupt    = terminate_flag | interrupt_flag,
        msg_sync_restart = sync_flag | restart_flag,
        msg_split        = split_flag
    };
    struct Generator {
        enum State { start = 0, search = 1, model = 2, done = 3 };
        mutex              genM;
        condition_variable cond;
        State              waitWhile(State st) {
            State r;
            for (unique_lock lock(genM); (r = state) == st;) { cond.wait(lock); }
            return r;
        }
        void pushModel() {
            notify(model);
            waitWhile(model);
        }
        void notify(State st) {
            unique_lock lock(genM);
            state = st;
            cond.notify_one();
        }
        State state{start};
    };
    SharedData() = default;
    void reset(SharedContext& a_ctx) {
        clearQueue();
        syncT.reset();
        msg.clear();
        globalR.reset();
        discardVec(path);
        maxConflict = globalR.current();
        threads     = a_ctx.concurrency();
        waiting     = 0;
        errorSet    = 0;
        initVec     = 0;
        ctx         = &a_ctx;
        nextId      = 1;
        workReq     = 0;
        restartReq  = 0;
        generator   = nullptr;
        errorCode   = 0;
    }
    void clearQueue() {
        workQ.first.clear();
        workQ.second = 0;
    }
    bool requestWork(const Solver& s, Path& out) {
        if (const auto m = Potassco::nth_bit<uint64_t>(s.id()); Potassco::test_mask(initVec.load(), m)) {
            // do not take over ownership of initial gp!
            if (not allowSplit()) {
                // portfolio mode - all solvers can start with initial path
                initVec -= m;
                out      = Path::borrow(path);
                return true;
            }
            if (initVec.exchange(0) != 0) {
                // splitting mode - only one solver must start with initial path
                out = Path::borrow(path);
                return true;
            }
        }
        if (not allowSplit()) {
            return false;
        }
        ctx->report(MessageEvent(s, "SPLIT", MessageEvent::sent));
        // try to get work from split
        bool ok = false;
        for (unique_lock lock(workM); not hasControl(terminate_flag | sync_flag);) {
            if (auto& [vec, pos] = workQ; not vec.empty()) {
                out = std::move(vec[pos++]);
                ok  = true;
                if (pos == size32(vec)) {
                    clearQueue();
                }
                break;
            }
            postMessage(msg_split, false);
            if (not enterWait(lock)) {
                break;
            }
        }
        ctx->report("resume after wait", &s);
        return ok;
    }
    void pushWork(Path gp) {
        POTASSCO_ASSERT(gp.owner());
        unique_lock lock(workM);
        workQ.first.push_back(std::move(gp));
        notifyWaitingThreads(&lock, 1);
    }
    void notifyWaitingThreads(unique_lock<mutex>* lock = nullptr, int n = 0) {
        assert(not lock || lock->owns_lock());
        if (lock) {
            lock->unlock();
        }
        else {
            unique_lock preventLostWakeup(workM);
        }
        n == 1 ? workCond.notify_one() : workCond.notify_all();
    }
    bool enterWait(unique_lock<mutex>& lock) {
        assert(lock.owns_lock());
        if ((waiting + 1) >= threads) {
            return false;
        }
        ++waiting;
        workCond.wait(lock);
        --waiting;
        return true;
    }
    bool waitSync() {
        for (unique_lock lock(workM); synchronize();) {
            if (not enterWait(lock)) {
                assert(synchronize());
                return true;
            }
        }
        return false;
    }
    uint32_t leaveAlgorithm() {
        assert(threads);
        unique_lock lock(workM);
        uint32_t    res = --threads;
        notifyWaitingThreads(&lock);
        return res;
    }
    // MESSAGES
    bool               postMessage(Message m, bool notify);
    [[nodiscard]] bool hasMessage() const { return Potassco::test_any(control.load(), 7u); }
    [[nodiscard]] bool synchronize() const { return Potassco::test_any(control.load(), sync_flag); }
    [[nodiscard]] bool terminate() const { return Potassco::test_any(control.load(), terminate_flag); }
    [[nodiscard]] bool split() const { return Potassco::test_any(control.load(), split_flag); }
    void               aboutToSplit() {
        if (--workReq == 0) {
            updateSplitFlag();
        }
    }
    void updateSplitFlag();
    // CONTROL FLAGS
    [[nodiscard]] bool hasControl(uint32_t f) const { return Potassco::test_any(control.load(), f); }
    [[nodiscard]] bool interrupt() const { return hasControl(interrupt_flag); }
    [[nodiscard]] bool complete() const { return hasControl(complete_flag); }
    [[nodiscard]] bool restart() const { return hasControl(restart_flag); }
    [[nodiscard]] bool allowSplit() const { return hasControl(allow_split_flag); }
    [[nodiscard]] bool allowRestart() const { return not hasControl(forbid_restart_flag); }
    bool               setControl(uint32_t flags) { return (control.fetch_or(flags) & flags) != flags; }
    bool               clearControl(uint32_t flags) { return (control.fetch_and(~flags) & flags) == flags; }
    using GeneratorPtr = std::unique_ptr<Generator>;
    std::string           msg;            // global error message
    ScheduleStrategy      globalR;        // global restart strategy
    LitVec                path;           // initial guiding path - typically empty
    uint64_t              maxConflict{0}; // current restart limit
    std::atomic<uint64_t> errorSet{0};    // bitmask of erroneous solvers
    SharedContext*        ctx{nullptr};   // shared context object
    std::atomic<uint64_t> initVec{0};     // vector of initial gp - represented as bitset
    GeneratorPtr          generator;      // optional data for model generation
    Timer<RealTime>       syncT;          // thread sync time
    mutex                 modelM;         // model-mutex
    mutex                 workM;          // work-mutex
    ConditionVar          workCond;       // work-condition
    PathQueue             workQ;          // work-queue (must be protected by workM)
    uint32_t              waiting{0};     // number of worker threads waiting on workCond
    uint32_t              nextId{1};      // next solver id to use
    LowerBound            lower;          // last reported lower bound (if any)
    std::atomic<uint32_t> threads{0};     // number of threads in the algorithm
    std::atomic<int>      workReq{0};     // > 0: someone needs work
    std::atomic<uint32_t> restartReq{0};  // == numThreads(): restart
    std::atomic<uint32_t> control{0};     // set of active message flags
    std::atomic<uint32_t> modCount{0};    // counter for synchronizing models
    int32_t               errorCode{0};   // global error code
};

// post message to all threads
bool ParallelSolve::SharedData::postMessage(Message m, bool notifyWaiting) {
    if (m == msg_split) {
        if (++workReq == 1) {
            updateSplitFlag();
        }
        return true;
    }
    if (setControl(m)) {
        // control message - notify all if requested
        if (notifyWaiting) {
            notifyWaitingThreads();
        }
        if ((static_cast<uint32_t>(m) & (terminate_flag | sync_flag)) != 0) {
            syncT.reset();
            syncT.start();
        }
        return true;
    }
    return false;
}

void ParallelSolve::SharedData::updateSplitFlag() {
    for (bool splitF;;) {
        splitF = (workReq > 0);
        if (split() == splitF) {
            return;
        }
        if (splitF) {
            control.fetch_or(split_flag);
        }
        else {
            control.fetch_and(~split_flag);
        }
    }
}
/////////////////////////////////////////////////////////////////////////////////////////
// ParallelSolve
/////////////////////////////////////////////////////////////////////////////////////////
static constexpr uint32_t master_id = 0u;
ParallelSolve::ParallelSolve(const ParallelSolveOptions& opts)
    : SolveAlgorithm(opts.limit)
    , shared_(std::make_unique<SharedData>())
    , thread_(nullptr)
    , distribution_(opts.distribute)
    , maxRestarts_(0)
    , intGrace_(1024)
    , intTopo_(opts.integrate.topo)
    , intFlags_(ClauseCreator::clause_not_root_sat | ClauseCreator::clause_no_add)
    , modeSplit_(opts.algorithm.mode == ParallelSolveOptions::Algorithm::mode_split) {
    setRestarts(opts.restarts.maxR, opts.restarts.sched);
    setIntegrate(opts.integrate.grace, opts.integrate.filter);
}

ParallelSolve::~ParallelSolve() {
    if (shared_->nextId > 1) {
        // algorithm was not started but there may be active threads -
        // force orderly shutdown
        ParallelSolve::doInterrupt();
        shared_->notifyWaitingThreads();
        joinThreads();
    }
    destroyThread(master_id);
    shared_.reset();
}

bool ParallelSolve::beginSolve(SharedContext& ctx, LitView path) {
    assert(ctx.concurrency() && "Illegal number of threads");
    if (shared_->terminate()) {
        return false;
    }
    shared_->reset(ctx);
    if (not enumerator().supportsParallel() && numThreads() > 1) {
        ctx.warn("Selected reasoning mode implies #Threads=1.");
        shared_->threads = 1;
        modeSplit_       = false;
        ctx.setConcurrency(1, SharedContext::resize_reserve);
    }
    shared_->setControl(modeSplit_ ? SharedData::allow_split_flag : SharedData::forbid_restart_flag);
    shared_->modCount = static_cast<uint32_t>(enumerator().optimize());
    shared_->path.assign(path.begin(), path.end());
    if (distribution_.types != 0 && ctx.distributor.get() == nullptr && numThreads() > 1) {
        auto topo = intTopo_;
        if (distribution_.mode == ParallelSolveOptions::Distribution::mode_local) {
            ctx.distributor = std::make_unique<LocalDistribution>(distribution_, ctx.concurrency(), topo);
        }
        else {
            ctx.distributor = std::make_unique<GlobalDistribution>(distribution_, ctx.concurrency(), topo);
        }
    }
    shared_->setControl(SharedData::sync_flag); // force initial sync with all threads
    shared_->syncT.start();
    reportProgress(MessageEvent(*ctx.master(), "SYNC", MessageEvent::sent));
    assert(ctx.master()->id() == master_id);
    allocThread(master_id, *ctx.master());
    for ([[maybe_unused]] auto i : irange(ctx.concurrency() - 1)) {
        uint32_t id = shared_->nextId++;
        allocThread(id, *ctx.solver(id));
        // start in new thread
        thread_[id]->setThread(Clasp::mt::thread(std::mem_fn(&ParallelSolve::solveParallel), this, id));
    }
    return true;
}

void ParallelSolve::setIntegrate(uint32_t grace, uint8_t filter) {
    using Dist = ParallelSolveOptions::Integration;
    intGrace_  = grace;
    intFlags_  = ClauseCreator::clause_no_add;
    if (filter == Dist::filter_heuristic) {
        Potassco::store_set_bit(intFlags_, 31);
    }
    if (filter != Dist::filter_no) {
        intFlags_ |= ClauseCreator::clause_not_root_sat;
    }
    if (filter == Dist::filter_sat) {
        intFlags_ |= ClauseCreator::clause_not_sat;
    }
}

void ParallelSolve::setRestarts(uint32_t maxR, const ScheduleStrategy& rs) {
    maxRestarts_         = maxR;
    shared_->globalR     = maxR ? rs : ScheduleStrategy::none();
    shared_->maxConflict = shared_->globalR.current();
}

uint32_t ParallelSolve::numThreads() const { return shared_->threads; }

void ParallelSolve::allocThread(uint32_t id, Solver& s) {
    if (not thread_) {
        thread_ = std::make_unique<HandlerPtr[]>(numThreads());
    }
    thread_[id] = std::make_unique<ParallelHandler>(*this, s);
}

void ParallelSolve::destroyThread(uint32_t id) {
    if (thread_ && thread_[id]) {
        assert(not thread_[id]->joinable() && "Shutdown not completed!");
        thread_[id].reset();
        if (id == master_id) {
            thread_.reset();
        }
    }
}

inline void ParallelSolve::reportProgress(const Event& ev) const { return shared_->ctx->report(ev); }
inline void ParallelSolve::reportProgress(const Solver& s, const char* msg) const {
    return shared_->ctx->report(msg, &s);
}

// joins with and destroys all active threads
int ParallelSolve::joinThreads() {
    uint32_t winner = thread_[master_id]->winner() ? master_id : UINT32_MAX;
    // detach master only after all client threads are done
    for (uint32_t i : irange(1u, shared_->nextId)) {
        assert(thread_ && thread_[i]);
        auto* handler = thread_[i].get();
        handler->join();
        if (handler->winner() && i < winner) {
            winner = i;
        }
        Solver* s = &handler->solver();
        reportProgress(*s, "joined");
        destroyThread(i);
        reportProgress(*s, "destroyed");
    }
    if (shared_->complete()) {
        enumerator().commitComplete();
    }
    thread_[master_id]->handleTerminateMessage();
    shared_->ctx->setWinner(winner);
    shared_->nextId = 1;
    shared_->syncT.stop();
    reportProgress(MessageEvent(*shared_->ctx->master(), "TERMINATE", MessageEvent::completed, shared_->syncT.total()));
    return not shared_->interrupt() ? thread_[master_id]->error() : shared_->errorCode;
}

void ParallelSolve::doStart(SharedContext& ctx, LitView assume) {
    if (beginSolve(ctx, assume)) {
        // start computation in new thread
        shared_->generator = std::make_unique<SharedData::Generator>();
        thread_[master_id]->setThread(Clasp::mt::thread(std::mem_fn(&ParallelSolve::solveParallel), this, master_id));
    }
}
Val_t ParallelSolve::doNext(Val_t) {
    POTASSCO_CHECK_PRE(shared_->generator.get(), "Invalid operation");
    if (int s = shared_->generator->state; s != SharedData::Generator::done) {
        shared_->generator->notify(SharedData::Generator::search);
        if (shared_->generator->waitWhile(SharedData::Generator::search) == SharedData::Generator::model) {
            return value_true;
        }
    }
    return shared_->complete() ? value_false : value_free;
}
void ParallelSolve::doStop() {
    if (shared_->nextId <= 1) {
        return;
    }
    reportProgress(*shared_->ctx->master(), "joining with other threads");
    if (shared_->generator.get()) {
        shared_->setControl(SharedData::terminate_flag);
        shared_->generator->notify(SharedData::Generator::done);
        thread_[master_id]->join();
    }
    int err            = joinThreads();
    shared_->generator = nullptr;
    shared_->ctx->distributor.reset(nullptr);
    POTASSCO_CHECK(err == 0, err, "%s", shared_->msg.c_str());
}

void ParallelSolve::doDetach() {
    // detach master only after all client threads are done
    thread_[master_id]->detach(*shared_->ctx, shared_->interrupt());
    destroyThread(master_id);
}

// Entry point for master solver
bool ParallelSolve::doSolve(SharedContext& ctx, LitView assume) {
    if (beginSolve(ctx, assume)) {
        solveParallel(master_id);
        ParallelSolve::doStop();
    }
    return not shared_->complete();
}

// main solve loop executed by all threads
void ParallelSolve::solveParallel(uint32_t id) {
    Solver&     s = thread_[id]->solver();
    SolverStats agg;
    Path        a;
    if (id == master_id && shared_->generator.get()) {
        shared_->generator->waitWhile(SharedData::Generator::start);
    }
    try {
        // establish solver<->handler connection and attach to shared context
        // should this fail because of an initial conflict, we'll terminate
        // in requestWork.
        thread_[id]->attach(*shared_->ctx);
        BasicSolve solve(s, limits());
        agg.enable(s.stats);
        for (GpType t; requestWork(s, a);) {
            agg.accu(s.stats);
            s.stats.reset();
            thread_[id]->setGpType(t = ((a.owner() || modeSplit_) ? gp_split : gp_fixed));
            reportProgress(s, "solving path...");
            if (enumerator().start(s, a, a.owner()) &&
                thread_[id]->solveGP(solve, t, shared_->maxConflict) == value_free) {
                terminate(s, false);
            }
            s.clearStopConflict();
            s.undoUntil(0);
            enumerator().end(s);
            reportProgress(s, "done with path");
        }
    }
    catch (const std::bad_alloc&) {
        exception(id, std::move(a), ENOMEM, "bad alloc");
    }
    catch (const std::logic_error& e) {
        exception(id, std::move(a), Potassco::to_underlying(Potassco::Errc::invalid_argument), e.what());
    }
    catch (const std::exception& e) {
        exception(id, std::move(a), Potassco::to_underlying(std::errc::interrupted), e.what());
    }
    catch (...) {
        exception(id, std::move(a), Potassco::to_underlying(std::errc::interrupted), "unknown");
    }
    assert(shared_->terminate() || thread_[id]->error());
    auto remaining = shared_->leaveAlgorithm();
    // update stats
    s.stats.accu(agg);
    if (id != master_id) {
        // remove solver<->handler connection and detach from shared context
        // note: since detach can change the problem, we must not yet detach the master
        // because some client might still be in the middle of an attach operation
        thread_[id]->detach(*shared_->ctx, shared_->interrupt());
        s.stats.addCpuTime(ThreadTime::getTime());
    }
    if (remaining == 0 && shared_->generator.get()) {
        shared_->generator->notify(SharedData::Generator::done);
    }
}

void ParallelSolve::exception(uint32_t id, Path path, int e, const char* what) {
    try {
        if (not thread_[id]->setError(e) || e != ENOMEM || id == master_id) {
            ParallelSolve::doInterrupt();
            if (shared_->errorSet.fetch_or(Potassco::nth_bit<uint64_t>(id)) == 0) {
                shared_->errorCode = e;
                shared_->msg.append(1, '[').append(std::to_string(id)).append("]: ").append(what);
            }
        }
        else if (path.owner() && shared_->allowSplit()) {
            shared_->pushWork(std::move(path));
        }
        reportProgress(thread_[id]->solver(),
                       e == ENOMEM ? "Thread failed with out of memory" : "Thread failed with error");
    }
    catch (...) {
        ParallelSolve::doInterrupt();
    }
}

// forced termination from outside
bool ParallelSolve::doInterrupt() {
    // do not notify blocked threads to avoid possible
    // deadlock in semaphore!
    shared_->postMessage(SharedData::msg_interrupt, false);
    return true;
}

// tries to get new work for the given solver
bool ParallelSolve::requestWork(Solver& s, Path& out) {
    bool gotWork = false;
    for (int popped = 0; not shared_->terminate();) {
        // only clear path and stop conflict - we don't propagate() here
        // because we would then have to handle any eventual conflicts
        if (++popped == 1 && not s.popRootLevel(s.rootLevel())) {
            // s has a real top-level conflict - problem is unsat
            terminate(s, true);
        }
        else if (shared_->synchronize()) {
            // a synchronize request is active - we are fine with
            // this but did not yet have a chance to react on it
            waitOnSync(s);
        }
        else if (gotWork = gotWork || shared_->requestWork(s, out); gotWork) {
            assert(s.decisionLevel() == 0);
            // got new work from work-queue
            // propagate any new facts before starting new work
            if (s.simplify()) {
                return true;
            }
            // s now has a conflict - either an artificial stop conflict
            // or a real conflict - we'll handle it in the next iteration
            // via the call to popRootLevel()
            popped = 0;
        }
        else if (not shared_->synchronize()) {
            // no work left - quitting time?
            terminate(s, true);
        }
    }
    return false;
}

// terminated from inside of algorithm
// check if there is more to do
void ParallelSolve::terminate(const Solver& s, bool complete) {
    if (not shared_->terminate()) {
        if (enumerator().tentative() && complete) {
            if (shared_->setControl(SharedData::sync_flag | SharedData::complete_flag)) {
                thread_[s.id()]->setWinner();
                reportProgress(MessageEvent(s, "SYNC", MessageEvent::sent));
            }
        }
        else {
            reportProgress(MessageEvent(s, "TERMINATE", MessageEvent::sent));
            shared_->postMessage(SharedData::msg_terminate, true);
            thread_[s.id()]->setWinner();
            if (complete) {
                shared_->setControl(SharedData::complete_flag);
            }
        }
    }
}

// handles an active synchronization request
// returns true to signal that s should restart otherwise false
bool ParallelSolve::waitOnSync(const Solver& s) {
    if (not thread_[s.id()]->handleRestartMessage()) {
        shared_->setControl(SharedData::cancel_restart_flag);
    }
    bool hasPath   = thread_[s.id()]->hasPath();
    bool tentative = enumerator().tentative();
    if (shared_->waitSync()) {
        // last man standing - complete synchronization request
        shared_->workReq    = 0;
        shared_->restartReq = 0;
        bool restart        = shared_->hasControl(SharedData::restart_flag);
        bool init           = true;
        if (restart) {
            init = shared_->allowRestart() && not shared_->hasControl(SharedData::cancel_restart_flag);
            if (init) {
                shared_->globalR.next();
            }
            shared_->maxConflict = shared_->allowRestart() && shared_->globalR.idx < maxRestarts_
                                       ? shared_->globalR.current()
                                       : UINT64_MAX;
        }
        else if (shared_->maxConflict != UINT64_MAX && not shared_->allowRestart()) {
            shared_->maxConflict = UINT64_MAX;
        }
        if (init) {
            initQueue();
        }
        else {
            shared_->setControl(SharedData::restart_abandoned_flag);
        }
        if (tentative && shared_->complete()) {
            if (enumerator().commitComplete()) {
                shared_->setControl(SharedData::terminate_flag);
            }
            else {
                shared_->modCount = 0u;
                shared_->clearControl(SharedData::complete_flag);
            }
        }
        shared_->clearControl(SharedData::msg_split | SharedData::msg_sync_restart |
                              SharedData::restart_abandoned_flag | SharedData::cancel_restart_flag);
        shared_->syncT.lap();
        reportProgress(MessageEvent(s, "SYNC", MessageEvent::completed, shared_->syncT.elapsed()));
        assert(not shared_->synchronize());
        // wake up all blocked threads
        shared_->notifyWaitingThreads();
    }
    return shared_->terminate() || (hasPath && not shared_->hasControl(SharedData::restart_abandoned_flag));
}

// If guiding path scheme is active only one
// thread can start with gp (typically empty) and this
// thread must then split up search-space dynamically.
// Otherwise, all threads can start with initial gp
// TODO:
//  heuristic for initial splits?
void ParallelSolve::initQueue() {
    shared_->clearQueue();
    if (shared_->allowSplit() && modeSplit_ && not enumerator().supportsSplitting(*shared_->ctx)) {
        shared_->ctx->warn("Selected strategies imply Mode=compete.");
        shared_->clearControl(SharedData::allow_split_flag);
        shared_->setControl(SharedData::forbid_restart_flag);
        modeSplit_ = false;
    }
    shared_->initVec = UINT64_MAX;
    assert(shared_->allowSplit() || shared_->hasControl(SharedData::forbid_restart_flag));
}

// adds work to the work-queue
void ParallelSolve::pushWork(LitView path) { shared_->pushWork(Path::acquire(path)); }

// called whenever some solver proved unsat
bool ParallelSolve::commitUnsat(Solver& s) {
    const int supUnsat = enumerator().unsatType();
    if (supUnsat == Enumerator::unsat_stop || shared_->terminate() || shared_->synchronize()) {
        return false;
    }
    auto        fullPath = not thread_[s.id()]->disjointPath();
    unique_lock lock(shared_->modelM, defer_lock_t());
    if (supUnsat == Enumerator::unsat_sync) {
        lock.lock();
    }
    if (not enumerator().commitUnsat(s)) {
        if (fullPath) {
            terminate(s, true);
        }
        return false;
    }
    if (fullPath && not shared_->terminate()) {
        if (not lock.owns_lock()) {
            lock.lock();
        }
        bool report = enumerator().lastModel().up;
        if (auto lb = enumerator().lowerBound(); lb.bound > shared_->lower.bound || lb.level > shared_->lower.level) {
            shared_->lower = lb;
            report         = true;
        }
        not report || reportUnsat(s);
        ++shared_->modCount;
        lock.unlock();
    }
    return true;
}

// called whenever some solver has found a model
bool ParallelSolve::commitModel(Solver& s) {
    // grab lock - models must be processed sequentially
    // in order to simplify printing and to avoid duplicates
    // in all non-trivial enumeration modes
    bool stop = false;
    {
        lock_guard lock(shared_->modelM);
        // first check if the model is still valid once all
        // information is integrated into the solver
        if (thread_[s.id()]->isModelLocked(s) && (stop = shared_->terminate()) == false &&
            enumerator().commitModel(s)) {
            if (enumerator().lastModel().num == 1 && not enumerator().supportsRestarts()) {
                // switch to backtracking based splitting algorithm
                // the solver's gp will act as the root for splitting and is
                // from now on disjoint from all other guiding paths
                shared_->setControl(SharedData::forbid_restart_flag | SharedData::allow_split_flag);
                thread_[s.id()]->setGpType(gp_split);
                enumerator().setDisjoint(s, true);
                shared_->initVec = 0;
            }
            if (shared_->generator.get()) {
                shared_->generator->pushModel();
            }
            else if (stop = not reportModel(s); stop) {
                // must be called while holding the lock - otherwise
                // we have a race condition with solvers that
                // are currently blocking on the mutex and we could enumerate
                // more models than requested by the user
                terminate(s, not moreModels(s));
            }
            ++shared_->modCount;
        }
    }
    return not stop;
}

uint64_t ParallelSolve::hasErrors() const { return shared_->errorSet != 0u; }
bool     ParallelSolve::interrupted() const { return shared_->interrupt(); }
void     ParallelSolve::resetSolve() { shared_->control = 0; }
void     ParallelSolve::enableInterrupts() {}
// updates s with new messages and uses s to create a new guiding path
// if necessary and possible
bool ParallelSolve::handleMessages(Solver& s) {
    // check if there are new messages for s
    if (not shared_->hasMessage()) {
        // nothing to do
        return true;
    }
    ParallelHandler* h = thread_[s.id()].get();
    if (shared_->terminate()) {
        reportProgress(MessageEvent(s, "TERMINATE", MessageEvent::received));
        h->handleTerminateMessage();
        s.setStopConflict();
        return false;
    }
    if (shared_->synchronize()) {
        reportProgress(MessageEvent(s, "SYNC", MessageEvent::received));
        if (waitOnSync(s)) {
            s.setStopConflict();
            return false;
        }
        return true;
    }
    if (shared_->split() && s.requestSplit() && h->disjointPath()) {
        // First declare split request as handled
        // and only then do the actual split.
        // This way, we minimize the chance for
        // "over"-splitting, i.e. one split request handled
        // by more than one thread.
        shared_->aboutToSplit();
        reportProgress(MessageEvent(s, "SPLIT", MessageEvent::received));
        h->handleSplitMessage();
        enumerator().setDisjoint(s, true);
    }
    return true;
}

bool ParallelSolve::integrateModels(Solver& s, uint32_t& upCount) {
    uint32_t gCount = shared_->modCount;
    return gCount == upCount || (enumerator().update(s) && (upCount = gCount) == gCount);
}

void ParallelSolve::requestRestart() {
    if (shared_->allowRestart() && ++shared_->restartReq == numThreads()) {
        shared_->postMessage(SharedData::msg_sync_restart, true);
    }
}

SolveAlgorithm* ParallelSolveOptions::createSolveObject() const {
    return numSolver() > 1 ? new ParallelSolve(*this) : BasicSolveOptions::createSolveObject();
}
////////////////////////////////////////////////////////////////////////////////////
// ParallelHandler
/////////////////////////////////////////////////////////////////////////////////////////
static constexpr auto receive_buffer_size = 32u;
static constexpr auto handler_align = std::max(alignof(ParallelHandler), static_cast<std::size_t>(cache_line_size));

void* ParallelHandler::operator new(std::size_t count) {
    return ::operator new(count, std::align_val_t{handler_align});
}
void ParallelHandler::operator delete(void* ptr, std::size_t sz) {
    ::operator delete(ptr, sz, std::align_val_t{handler_align});
}
ParallelHandler::ParallelHandler(ParallelSolve& ctrl, Solver& s)
    : ctrl_(&ctrl)
    , solver_(&s)
    , received_(nullptr)
    , recEnd_(0)
    , intEnd_(0)
    , error_(0)
    , win_(0)
    , up_(0)
    , act_(0)
    , lbd_(0) {
    this->next = this;
}

ParallelHandler::~ParallelHandler() { clearDB(nullptr); }

// adds this as post propagator to its solver and attaches the solver to ctx.
bool ParallelHandler::attach(SharedContext& ctx) {
    assert(solver_);
    gp_    = {};
    error_ = 0;
    win_   = 0;
    up_    = 0;
    act_   = 0;
    lbd_   = solver_->searchConfig().reduce.strategy.glue != 0;
    next   = nullptr;
    if (not received_ && ctx.distributor.get()) {
        received_ = std::make_unique<SharedLiterals*[]>(receive_buffer_size);
    }
    ctx.report("attach", solver_);
    solver_->addPost(this);
    return ctx.attach(solver_->id());
}

int ParallelHandler::join() {
    if (joinable()) {
        thread_.join();
    }
    return error();
}

// removes this from the list of post propagators of its solver and detaches the solver from ctx.
void ParallelHandler::detach(SharedContext& ctx, bool) {
    handleTerminateMessage();
    ctx.report("detach", solver_);
    if (solver_->sharedContext() == &ctx) {
        clearDB(not error() ? solver_ : nullptr);
        ctx.report("detached db", solver_);
        ctx.detach(*solver_, error() != 0);
        ctx.report("detached ctx", solver_);
    }
}
void ParallelHandler::setThread(Clasp::mt::thread x) {
    assert(not joinable() && x.joinable());
    thread_ = std::move(x);
}
bool ParallelHandler::setError(int code) {
    error_ = static_cast<uint32_t>(code);
    return thread_.joinable() && not winner();
}

void ParallelHandler::setWinner() { win_ = 1; }
bool ParallelHandler::winner() const { return win_ != 0; }
int  ParallelHandler::error() const { return static_cast<int>(error_); }
bool ParallelHandler::joinable() const { return thread_.joinable(); }

void ParallelHandler::clearDB(Solver* s) {
    for (auto* con : integrated_) {
        if (auto* c = static_cast<ClauseHead*>(con); s) {
            s->addLearnt(c, c->size(), ConstraintType::other);
        }
        else {
            c->destroy();
        }
    }
    integrated_.clear();
    intEnd_ = 0;
    for (uint32_t i : irange(recEnd_)) { received_[i]->release(); }
    recEnd_ = 0;
}

bool ParallelHandler::disjointPath() const { return gp_.type == ParallelSolve::gp_split; }
bool ParallelHandler::hasPath() const { return gp_.type != ParallelSolve::gp_none; }
void ParallelHandler::setGpType(GpType t) { gp_.type = t; }

Val_t ParallelHandler::solveGP(BasicSolve& solve, GpType type, uint64_t restart) {
    auto    res = value_free;
    Solver& s   = solve.solver();
    auto    fin = false;
    gp_         = {.restart = restart, .modCount = 0, .type = type};
    assert(act_ == 0);
    do {
        win_ = 0;
        ctrl_->integrateModels(s, gp_.modCount);
        up_ = act_ = 1; // activate enumerator and bounds
        res        = solve.solve();
        up_ = act_ = 0; // de-activate enumerator and bounds
        fin        = true;
        if (res == value_true) {
            if (ctrl_->commitModel(s)) {
                fin = false;
            }
        }
        else if (res == value_false) {
            if (ctrl_->commitUnsat(s)) {
                fin          = false;
                gp_.restart  = restart;
                gp_.modCount = 0;
            }
        }
    } while (not fin);
    return res;
}

Solver& ParallelHandler::solver() { return *solver_; }

// detach from solver, i.e. ignore any further messages
void ParallelHandler::handleTerminateMessage() {
    if (this->next != this) {
        // mark removed propagator by creating "self-loop"
        solver_->removePost(this);
        this->next = this;
    }
}

// split-off new guiding path and add it to solve object
void ParallelHandler::handleSplitMessage() {
    assert(solver_ && "ParallelHandler::handleSplitMessage(): not attached!");
    temp_.clear();
    bool ok = solver_->split(temp_);
    POTASSCO_ASSERT(ok, "unexpected call to split");
    ctrl_->pushWork(temp_);
}

bool ParallelHandler::handleRestartMessage() {
    // TODO
    // we may want to implement some heuristic, like
    // computing a local var order.
    static_cast<void>(this);
    return true;
}

bool ParallelHandler::simplify(Solver& s, bool shuffle) {
    auto j = 0u;
    for (auto i : irange(integrated_)) {
        if (Constraint* c = integrated_[i]; c->simplify(s, shuffle)) {
            c->destroy(&s, false);
            intEnd_ -= (i < intEnd_);
        }
        else {
            integrated_[j++] = c;
        }
    }
    shrinkVecTo(integrated_, j);
    if (intEnd_ > size32(integrated_)) {
        intEnd_ = size32(integrated_);
    }
    return false;
}
void ParallelHandler::reset() { up_ = 1; }

bool ParallelHandler::propagateFixpoint(Solver& s, PostPropagator* ctx) {
    // Check for messages and integrate any new information from
    // models/lemma exchange but only if path is set up.
    // Skip updates if called from other post propagator so that we do not
    // disturb any active propagation.
    if (int up = (ctx == nullptr && up_ != 0)) {
        up_ ^= static_cast<uint32_t>(s.updateMode());
        up  += (act_ == 0 || (up_ && (s.stats.choices & 63) != 0));
        if (s.stats.conflicts >= gp_.restart) {
            ctrl_->requestRestart();
            gp_.restart *= 2;
        }
        for (uint32_t dl = s.decisionLevel();;) {
            if (bool ok = ctrl_->handleMessages(s) && (up > 1 ? integrate(s) : ctrl_->integrateModels(s, gp_.modCount));
                not ok) {
                return false;
            }
            if (dl != s.decisionLevel()) { // cancel active propagation on dl
                cancelPropagation();
                dl = s.decisionLevel();
            }
            if (not s.queueSize()) {
                if (++up == 3) {
                    return true;
                }
            }
            else if (not s.propagateUntil(this)) {
                return false;
            }
        }
    }
    return ctrl_->handleMessages(s);
}
bool ParallelHandler::handleMessages() { return ctrl_->handleMessages(solver()); }

// checks whether s still has a model once all
// information from previously found models were integrated
bool ParallelHandler::isModel(Solver& s) {
    assert(s.numFreeVars() == 0);
    // either no unprocessed updates or still a model after
    // updates were integrated
    return ctrl_->integrateModels(s, gp_.modCount) && s.numFreeVars() == 0 && s.queueSize() == 0;
}

bool ParallelHandler::isModelLocked(Solver& s) {
    const uint32_t current = gp_.modCount;
    if (not isModel(s)) {
        return false;
    }
    if (current == gp_.modCount) {
        return true;
    }
    for (PostPropagator* p = s.getPost(priority_class_general); p; p = p->next) {
        if (not p->isModel(s)) {
            return false;
        }
    }
    return true;
}

bool ParallelHandler::integrate(Solver& s) {
    uint32_t rec = recEnd_ + s.receive(received_.get() + recEnd_, receive_buffer_size - recEnd_);
    if (not rec) {
        return true;
    }
    uint32_t dl = s.decisionLevel(), added = 0, i = 0;
    auto     intFlags = ClauseCreator::CreateFlag{ctrl_->integrateFlags()};
    recEnd_           = 0;
    if (lbd_) {
        intFlags |= ClauseCreator::clause_int_lbd;
    }
    do {
        auto ret  = ClauseCreator::integrate(s, received_[i++], intFlags, ConstraintType::other);
        added    += ret.status != ClauseCreator::status_subsumed;
        if (ret.local) {
            add(ret.local);
        }
        if (ret.unit()) {
            s.stats.addIntegratedAsserting(dl, s.decisionLevel());
            dl = s.decisionLevel();
        }
        if (not ret.ok()) {
            while (i != rec) { received_[recEnd_++] = received_[i++]; }
        }
    } while (i != rec);
    s.stats.addIntegrated(added);
    return not s.hasConflict();
}

void ParallelHandler::add(ClauseHead* h) {
    if (intEnd_ < integrated_.size()) {
        auto* o              = static_cast<ClauseHead*>(integrated_[intEnd_]);
        integrated_[intEnd_] = h;
        assert(o);
        if (not ctrl_->integrateUseHeuristic() || o->locked(*solver_) || o->activity().activity() > 0) {
            solver_->addLearnt(o, o->size(), ConstraintType::other);
        }
        else {
            o->destroy(solver_, true);
            solver_->stats.removeIntegrated();
        }
    }
    else {
        integrated_.push_back(h);
    }
    if (++intEnd_ >= ctrl_->integrateGrace()) {
        intEnd_ = 0;
    }
}
/////////////////////////////////////////////////////////////////////////////////////////
// Distribution
/////////////////////////////////////////////////////////////////////////////////////////
SolverSet ParallelSolveOptions::initPeerSet(uint32_t id, Integration::Topology topo, uint32_t maxT) {
    if (topo == Integration::topo_all) {
        return fullPeerSet(id, maxT);
    }
    if (topo == Integration::topo_ring) {
        auto prev = (id > 0 ? id : maxT) - 1;
        auto next = (id + 1) % maxT;
        return {prev, next};
    }
    const auto n   = maxT;
    const auto k   = Potassco::bit_floor(maxT);
    const auto ext = topo == Integration::topo_cubex && k != n ? k : 0u;
    const auto s   = (k ^ id) >= n ? k ^ id : (k * 2);
    SolverSet  res;
    for (uint32_t m = 1u; m <= k; m *= 2) {
        auto pos = m ^ id;
        if (pos < n) {
            res.add(pos);
        }
        if (m < ext) {
            if (auto r = m ^ s; r < n) {
                res.add(r);
            }
            if (pos >= n) {
                res.add(pos ^ k);
            }
        }
    }
    assert(not res.contains(id));
    return res;
}
/////////////////////////////////////////////////////////////////////////////////////////
// GlobalDistribution
/////////////////////////////////////////////////////////////////////////////////////////
class GlobalDistribution::Queue {
public:
    struct ClausePair {
        uint32_t        sender = UINT32_MAX;
        SharedLiterals* lits   = nullptr;
    };
    using QueueType = MultiQueue<ClausePair>;
    struct alignas(cache_line_size) ThreadInfo {
        SolverSet           peers;
        QueueType::ThreadId id{};
    };
    static_assert(sizeof(ThreadInfo) >= cache_line_size, "Invalid size");
    using ThreadId = QueueType::ThreadId;
    explicit Queue(uint32_t maxT, ParallelSolveOptions::Integration::Topology topo)
        : q_(maxT)
        , thread_(std::make_unique<ThreadInfo[]>(maxT)) {
        for (uint32_t i : irange(maxT)) {
            thread_[i].peers = ParallelSolveOptions::initPeerSet(i, topo, maxT);
            thread_[i].id    = q_.addThread();
        }
    }
    ~Queue() {
        for (uint32_t i : irange(q_.maxThreads())) { clear(i); }
    }
    void publish(uint32_t tId, SharedLiterals* n) {
        assert(n->refCount() >= (q_.maxThreads() - 1) && tId < q_.maxThreads());
        q_.publish(ClausePair{tId, n});
    }
    uint32_t pop(uint32_t tId, SharedLiterals** out, uint32_t maxOut) {
        assert(tId < q_.maxThreads());
        uint32_t r        = 0;
        auto& [peers, id] = thread_[tId];
        for (const ClausePair* n; r != maxOut && (n = q_.tryConsume(id)) != nullptr;) {
            if (n->sender == tId) {
                continue;
            }
            if (not peers.contains(n->sender) && n->lits->size() > 1) {
                n->lits->release();
                continue;
            }
            out[r++] = n->lits;
        }
        return r;
    }
    void clear(uint32_t tId) {
        auto& qId = thread_[tId].id;
        while (const auto* n = q_.tryConsume(qId)) {
            if (n->sender != tId) {
                n->lits->release();
            }
        }
    }

private:
    QueueType                     q_;
    std::unique_ptr<ThreadInfo[]> thread_;
};

GlobalDistribution::GlobalDistribution(const Policy& p, uint32_t maxT, uint32_t topo) : Distributor(p) {
    assert(maxT <= ParallelSolveOptions::supportedSolvers());
    queue_ = std::make_unique<Queue>(maxT, static_cast<ParallelSolveOptions::Integration::Topology>(topo));
}
GlobalDistribution::~GlobalDistribution() = default;
void     GlobalDistribution::publish(const Solver& s, SharedLiterals* n) { queue_->publish(s.id(), n); }
uint32_t GlobalDistribution::receive(const Solver& in, SharedLiterals** out, uint32_t maxn) {
    return queue_->pop(in.id(), out, maxn);
}
/////////////////////////////////////////////////////////////////////////////////////////
// LocalDistribution
/////////////////////////////////////////////////////////////////////////////////////////
struct LocalDistribution::ThreadData {
    using Queue = MpScPtrQueue<cache_line_size>;
    using QNode = Queue::Node;
    static QNode* allocBlock(QNode*& blockStack, uint32_t numNodes) {
        ++numNodes; // +1 for metadata
        auto* mem   = ::operator new((numNodes) * sizeof(QNode), std::align_val_t{cache_line_size});
        auto* block = new (mem) QNode[numNodes]{};
        block->next.store(blockStack);
        block->data = reinterpret_cast<void*>(static_cast<uintptr_t>(numNodes));
        blockStack  = block;
        return block + 1;
    }
    explicit ThreadData(QNode& sent, SolverSet s) : received(sent), peers(s) {}
    ~ThreadData() {
        while (auto* n = blocks) {
            blocks = Queue::toNode(n->next.load());
            std::destroy_n(n, reinterpret_cast<uintptr_t>(n->data));
            ::operator delete(n, std::align_val_t{cache_line_size});
        }
    }
    QNode* allocNode(uint32_t blockHint, SharedLiterals* clause) {
        if (free == nullptr) {
            blockHint = std::max(blockHint, 1u);
            // alloc a new block of nodes and push to free list
            auto* block = allocBlock(blocks, blockHint);
            for (auto n = blockHint; n--;) {
                block[n].next.store(free);
                free = &block[n];
            }
        }
        auto* n = free;
        free    = Queue::toNode(n->next.load());
        n->data = clause;
        return n;
    }
    SharedLiterals* popRec() {
        if (auto* n = received.pop()) {
            n->next.store(free);
            free = n;
            return static_cast<SharedLiterals*>(std::exchange(free->data, nullptr));
        }
        return nullptr;
    }
    Queue     received; // queue holding received clauses
    SolverSet peers;    // set of peers from which this thread receives clauses
    QNode*    free{};   // local free list - only accessed by this thread
    QNode*    blocks{}; // allocated block list - only accessed by this thread
};

LocalDistribution::LocalDistribution(const Policy& p, uint32_t maxShare, uint32_t topo)
    : Distributor(p)
    , thread_(std::make_unique<ThreadPtr[]>(maxShare))
    , numThread_(maxShare) {
    assert(maxShare <= ParallelSolveOptions::supportedSolvers());
    auto  t          = static_cast<ParallelSolveOptions::Integration::Topology>(topo);
    auto  blockStack = static_cast<ThreadData::QNode*>(nullptr);
    auto* block      = ThreadData::allocBlock(blockStack, numThread_);
    for (uint32_t i : irange(maxShare)) {
        thread_[i] = std::make_unique<ThreadData>(block[i], ParallelSolveOptions::initPeerSet(i, t, maxShare));
    }
    thread_[0]->blocks = blockStack;
}
LocalDistribution::~LocalDistribution() {
    while (numThread_) {
        auto& td = thread_[--numThread_];
        while (auto* lits = td->popRec()) { lits->release(); }
    }
    thread_.reset();
}

void LocalDistribution::publish(const Solver& s, SharedLiterals* n) {
    auto sender    = s.id();
    auto peers     = n->size() > 1 ? thread_[sender]->peers : ParallelSolveOptions::fullPeerSet(sender, numThread_);
    auto nPeers    = peers.count();
    auto maxPeers  = (numThread_ - 1);
    auto allocHint = std::min(nPeers * 16, 254u);
    assert(nPeers <= maxPeers && n->refCount() >= maxPeers);
    if (auto diff = static_cast<int>(maxPeers - nPeers); diff > 0) {
        n->release(diff);
    }
    for (uint32_t i = 0; nPeers; ++i) {
        assert(i < numThread_);
        if (peers.contains(i)) {
            auto* node = thread_[sender]->allocNode(allocHint, n); // allocate from this thread
            thread_[i]->received.push(node);
            --nPeers;
        }
    }
}
uint32_t LocalDistribution::receive(const Solver& in, SharedLiterals** out, uint32_t maxn) {
    auto&    td = thread_[in.id()];
    uint32_t r  = 0;
    while (r != maxn && (out[r] = td->popRec()) != nullptr) { ++r; }
    return r;
}

} // namespace Clasp::mt
