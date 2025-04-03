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
#include <clasp/clasp_facade.h>

#include <clasp/dependency_graph.h>
#include <clasp/lookahead.h>
#include <clasp/minimize_constraint.h>
#include <clasp/parser.h>
#include <clasp/unfounded_check.h>
#include <clasp/util/timer.h>

#include <climits>
#include <cstdlib>
#if CLASP_HAS_THREADS
#include <clasp/mt/thread.h>
#endif
namespace Clasp {
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspConfig
/////////////////////////////////////////////////////////////////////////////////////////
struct ClaspConfig::Impl {
    struct ConfiguratorProxy {
        static constexpr uint32_t once_bit = 0u;
        ConfiguratorProxy(Configurator& c, bool once) : cfg(&c) {
            POTASSCO_ASSERT(cfg.get() == &c && not cfg.any(), "invalid configurator pointer");
            if (once) {
                cfg.set<once_bit>();
            }
        }
        bool applyConfig(Solver& s) {
            POTASSCO_ASSERT(s.id() < 64, "invalid solver id!");
            if (set.contains(s.id())) {
                return true;
            }
            if (cfg.test<once_bit>()) {
                set.add(s.id());
            }
            return cfg->applyConfig(s);
        }
        void prepare(SharedContext& ctx) {
            set.removeMax(ctx.concurrency());
            cfg->prepare(ctx);
        }
        // NOLINTBEGIN(readability-make-member-function-const)
        void unfreeze(SharedContext& ctx) { cfg->unfreeze(ctx); }
        // NOLINTEND(readability-make-member-function-const)
        using Ptr = TaggedPtr<Configurator>;
        Ptr       cfg;
        SolverSet set;
    };
    using ProxyVec = PodVector_t<ConfiguratorProxy>;
    Impl()         = default;
    ~Impl() { reset(); }
    void      reset();
    void      prepare(SharedContext& ctx);
    bool      addPost(Solver& s, const SolverParams& opts);
    void      add(Configurator& c, bool once) { pp.push_back(ConfiguratorProxy(c, once)); }
    void      unfreeze(SharedContext& ctx);
    ProxyVec  pp;
    SolverSet acycSet;
#if CLASP_HAS_THREADS
    mt::mutex mutex;
#endif
};
void ClaspConfig::Impl::reset() { pp.clear(); }

void ClaspConfig::Impl::prepare(SharedContext& ctx) {
    acycSet.removeMax(ctx.concurrency());
    for (auto& p : pp) { p.prepare(ctx); }
}
bool ClaspConfig::Impl::addPost(Solver& s, const SolverParams& opts) {
#if CLASP_HAS_THREADS
#define LOCKED(...)                                                                                                    \
    [&]() {                                                                                                            \
        mt::unique_lock lock(mutex);                                                                                   \
        return __VA_ARGS__;                                                                                            \
    }()
#else
#define LOCKED(...) __VA_ARGS__
#endif
    POTASSCO_ASSERT(s.sharedContext() != nullptr, "Solver not attached!");
    if (s.sharedContext()->sccGraph.get()) {
        if (auto* ufs = static_cast<DefaultUnfoundedCheck*>(s.getPost(PostPropagator::priority_reserved_ufs))) {
            ufs->setReasonStrategy(static_cast<DefaultUnfoundedCheck::ReasonStrategy>(opts.loopRep));
        }
        else if (not s.addPost(new DefaultUnfoundedCheck(
                     *s.sharedContext()->sccGraph, static_cast<DefaultUnfoundedCheck::ReasonStrategy>(opts.loopRep)))) {
            return false;
        }
    }
    if (s.sharedContext()->extGraph.get()) {
        // protect access to acycSet
        bool addAcyc = LOCKED(acycSet.add(s.id()));
        if (addAcyc && not s.addPost(new AcyclicityCheck(s.sharedContext()->extGraph.get()))) {
            return false;
        }
    }
    for (auto& p : pp) {
        if (not LOCKED(p.applyConfig(s))) { // protect call to user code
            return false;
        }
    }
    return true;
#undef LOCKED
}
void ClaspConfig::Impl::unfreeze(SharedContext& ctx) {
    for (auto& p : pp) { p.unfreeze(ctx); }
}

ClaspConfig::ClaspConfig() : tester_(nullptr), impl_(std::make_unique<Impl>()) {}
ClaspConfig::~ClaspConfig() = default;

void ClaspConfig::reset() {
    if (tester_) {
        tester_->reset();
    }
    impl_->reset();
    BasicSatConfig::reset();
    solve = SolveOptions();
    asp   = AspOptions();
}

BasicSatConfig* ClaspConfig::addTesterConfig() {
    if (not tester_) {
        tester_ = std::make_unique<BasicSatConfig>();
    }
    return tester_.get();
}

void ClaspConfig::prepare(SharedContext& ctx) {
    BasicSatConfig::prepare(ctx);
    uint32_t numS = solve.numSolver();
    if (numS > SolveOptions::supportedSolvers()) {
        ctx.warn("Too many solvers.");
        numS = SolveOptions::supportedSolvers();
    }
    if (numS > SolveOptions::recommendedSolvers()) {
        ctx.warnFmt("Oversubscription: #Threads=%u exceeds logical CPUs=%u.", numS, SolveOptions::recommendedSolvers());
    }
    for (auto i : irange(numS)) {
        if (solver(i).heuId == HeuristicType::domain) {
            parse.enableHeuristic();
            break;
        }
    }
    solve.setSolvers(numS);
    if (std::abs(static_cast<int>(solve.numModels)) != 1 || not solve.models()) {
        ctx.setPreserveModels(true);
    }
    ctx.setConcurrency(solve.numSolver(), SharedContext::resize_resize);
    impl_->prepare(ctx);
}

Configuration* ClaspConfig::config(const char* n) {
    return (n && std::strcmp(n, "tester") == 0) ? testerConfig() : BasicSatConfig::config(n);
}

void ClaspConfig::addConfigurator(Configurator& c, bool once) { impl_->add(c, once); }
bool ClaspConfig::addPost(Solver& s) const { return impl_->addPost(s, solver(s.id())) && BasicSatConfig::addPost(s); }
void ClaspConfig::unfreeze(SharedContext& ctx) { impl_->unfreeze(ctx); }
ClaspConfig::Configurator::~Configurator() = default;
void ClaspConfig::Configurator::prepare(SharedContext&) {}
void ClaspConfig::Configurator::unfreeze(SharedContext&) {}
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspFacade::SolveStrategy
/////////////////////////////////////////////////////////////////////////////////////////
struct ClaspFacade::SolveStrategy {
    static constexpr int sig_cancel = 9;
    static constexpr int sig_error  = 128;
    enum State : uint32_t { state_run = 1u, state_model = 2u, state_done = 4u };
    enum Event { event_attach, event_model, event_resume, event_detach };
    virtual ~SolveStrategy() = default;
    static SolveStrategy* create(SolveMode m, ClaspFacade& f, SolveAlgorithm& algo);
    void                  start(EventHandler* h, LitView a);
    [[nodiscard]] bool    running() const noexcept { return (state_ & (state_done - 1u)) != 0u; }
    [[nodiscard]] bool    error() const noexcept { return signal_ == sig_error; }
    [[nodiscard]] bool    ready() const noexcept { return state_ != state_run; }
    [[nodiscard]] int     signal() const noexcept { return signal_; }
    bool                  interrupt(int sig) {
        bool stopped = running() && signal_.set_if_unset(sig) && algo_->interrupt();
        if (sig == sig_cancel) {
            wait(-1.0);
        }
        return stopped;
    }
    bool wait(double s) { return doWait(s); }
    void resume() { doNotify(event_resume); }
    bool setModel(const Solver& s, const Model& m) {
        result_.flags |= SolveResult::res_sat;
        bool ok        = not handler_ || handler_->onModel(s, m);
        ok             = s.sharedContext()->report(s, m) && ok;
        if (Potassco::test(mode_, SolveMode::yield)) {
            doNotify(event_model);
        }
        return ok && not signal();
    }
    Result result() {
        wait(-1.0);
        POTASSCO_CHECK(not error(), std::errc::operation_canceled, "%s", error_.c_str());
        return result_;
    }
    const Model* model() {
        return state_ == state_model || (result().sat() && state_ == state_model) ? &algo_->model() : nullptr;
    }
    LitView unsatCore() { return result().unsat() ? algo_->unsatCore() : LitView{}; }
    bool    next() { return running() && (state_ != state_model || (resume(), true)) && model() != nullptr; }
    void    release() {
        if (auto n = nrefs_.release_fetch(); n == 1u) {
            interrupt(sig_cancel);
        }
        else if (n == 0) {
            delete this;
        }
    }
    SolveStrategy* share() {
        nrefs_.add();
        return this;
    }

protected:
    SolveStrategy(SolveMode m, ClaspFacade& f, SolveAlgorithm* algo);
    ClaspFacade*    facade_;
    SolveAlgorithm* algo_;
    void            startAlgo(SolveMode m);
    void            continueAlgo();

private:
    void detachAlgo(bool more);
    struct Detacher {
        explicit Detacher(SolveStrategy* s) : self(s) {}
        ~Detacher() noexcept(false) { run(); }
        void run() {
            if (auto x = std::exchange(self, nullptr); x) {
                x->detachAlgo(more < 0 ? x->algo_->more() : more > 0);
            }
        }
        SolveStrategy* self = nullptr;
        int            more = -1;
    };
    struct Async;
    virtual void doStart() { startAlgo(mode_); }
    virtual bool doWait(double maxTime) {
        POTASSCO_CHECK_PRE(maxTime < 0.0, "Timed wait not supported!");
        if (mode_ == SolveMode::yield) {
            continueAlgo();
        }
        return true;
    }
    virtual void doNotify(Event event) {
        switch (event) {
            case event_attach: state_.store(state_run); break;
            case event_model : state_.store(state_model); break;
            case event_resume: handleResume(); break;
            case event_detach: state_.store(state_done); break;
        }
    }
    bool handleResume() {
        uint32_t cmp = state_model;
        return state_.compare_exchange_strong(cmp, state_run);
    }
    using SafeIntType = mt::ThreadSafe<uint32_t>;
    std::string   error_;
    EventHandler* handler_{nullptr};
    SigAtomic     signal_;
    RefCount      nrefs_{1}; // Facade + #Handle objects
    SafeIntType   state_;
    Result        result_{};
    SolveMode     mode_{};
    uint32_t      aTop_{};
};
ClaspFacade::SolveStrategy::SolveStrategy(SolveMode m, ClaspFacade& f, SolveAlgorithm* algo)
    : facade_(&f)
    , algo_(algo)
    , mode_(m) {}

void ClaspFacade::SolveStrategy::start(EventHandler* h, LitView a) {
    ClaspFacade& f = *facade_;
    aTop_          = size32(f.assume_);
    f.assume_.insert(f.assume_.end(), a.begin(), a.end());
    if (not isSentinel(f.ctx.stepLiteral())) {
        f.assume_.push_back(f.ctx.stepLiteral());
    }
    handler_ = h;
    std::memset(&result_, 0, sizeof(SolveResult));
    // We forward models to the SharedContext ourselves.
    algo_->setReportModels(false);
    doStart();
    assert(running() || ready());
}
void ClaspFacade::SolveStrategy::startAlgo(SolveMode m) {
    doNotify(event_attach);
    Detacher detacher(this);
    try {
        facade_->interrupt(0); // handle pending interrupts
        if (not signal_ && not facade_->ctx.master()->hasConflict()) {
            auto* en = facade_->enumerator();
            POTASSCO_CHECK_PRE(en, "enumerator expected!");
            facade_->step_.solveTime = facade_->step_.unsatTime = RealTime::getTime();
            if (not Potassco::test(m, SolveMode::yield)) {
                detacher.more = algo_->solve(*en, facade_->ctx, facade_->assume_, facade_);
            }
            else {
                algo_->start(*en, facade_->ctx, facade_->assume_, facade_);
                detacher.self = nullptr;
            }
        }
        else {
            facade_->ctx.report(Clasp::Event::subsystem_solve);
            detacher.more = facade_->ctx.ok();
        }
    }
    catch (...) {
        detacher.run();
    }
}
void ClaspFacade::SolveStrategy::continueAlgo() {
    Detacher detacher(this);
    try {
        if (auto detach = (signal() && running()) || (state_ == state_run && not algo_->next()); not detach) {
            detacher.self = nullptr; // release
        }
    }
    catch (...) {
        detacher.run();
    }
}
void ClaspFacade::SolveStrategy::detachAlgo(bool more) {
    auto error = std::current_exception();
    for (unsigned state = 0; state != UINT32_MAX;) {
        try {
            switch (state) {
                case 0:
                    ++state;
                    algo_->stop();
                    [[fallthrough]];
                case 1:
                    ++state;
                    facade_->stopStep(signal_, not more);
                    [[fallthrough]];
                case 2:
                    ++state;
                    if (handler_) {
                        handler_->onEvent(StepReady(facade_->summary()));
                    }
                    [[fallthrough]];
                case 3:
                    ++state;
                    result_ = facade_->result();
                    facade_->assume_.resize(aTop_);
                    doNotify(event_detach);
                    [[fallthrough]];
                default: state = UINT32_MAX; break;
            }
        }
        catch (...) {
            if (not error) {
                error = std::current_exception();
            }
        }
    }
    if (error) {
        signal_.set_if_unset(sig_error);
        if (not Potassco::test(mode_, SolveMode::async)) {
            error_ = "Operation failed: exception thrown";
            std::rethrow_exception(error);
        }
        try {
            std::rethrow_exception(error);
        }
        catch (const std::exception& e) {
            error_ = e.what();
        }
        catch (...) {
            error_ = "unknown error";
        }
    }
}

#if CLASP_HAS_THREADS
struct ClaspFacade::SolveStrategy::Async : SolveStrategy {
    enum {
        state_async = (state_done << 1),
        state_next  = state_model | state_async,
        state_join  = state_done | state_async
    };
    Async(SolveMode m, ClaspFacade& f, SolveAlgorithm* algo) : SolveStrategy(m, f, algo) {}
    void doStart() override {
        algo_->enableInterrupts();
        task = Clasp::mt::thread([this]() { startAlgo(SolveMode::async); });
        for (mt::unique_lock lock(mqMutex); state_ == 0u;) { mqCond.wait(lock); }
    }
    bool doWait(double t) override {
        for (mt::unique_lock lock(mqMutex);;) {
            if (signal() && running()) { // propagate signal to async thread and force wait
                mqCond.notify_all();
                mqCond.wait(lock);
            }
            else if (ready()) {
                break;
            }
            else if (t < 0.0) {
                mqCond.wait(lock);
            }
            else if (t > 0.0) {
                mqCond.wait_for(lock, mt::toMillis(t));
                t = 0.0;
            }
            else {
                return false;
            }
        }
        assert(ready());
        // acknowledge current model or join if first to see done
        if (uint32_t prev = state_next; not state_.compare_exchange_strong(prev, state_model) && prev == state_done &&
                                        state_.compare_exchange_strong(prev, state_join)) {
            task.join();
        }
        return true;
    }
    void doNotify(Event event) override {
        mt::unique_lock lock(mqMutex);
        switch (event) {
            case event_attach: state_.store(state_run); break;
            case event_model : state_.store(state_next); break;
            case event_resume:
                if (handleResume()) {
                    break;
                }
                return;
            case event_detach: state_.store(state_done); break;
        }
        lock.unlock(); // synchronize-with other threads but no need to notify under lock
        mqCond.notify_all();
        if (event == event_model) {
            for (lock.lock(); state_ != state_run && not signal();) { mqCond.wait(lock); }
        }
    }
    using ConditionVar = Clasp::mt::condition_variable;
    Clasp::mt::thread task;    // async solving thread
    Clasp::mt::mutex  mqMutex; // protects mqCond
    ConditionVar      mqCond;  // for iterating over models one by one
};
#endif
ClaspFacade::SolveStrategy* ClaspFacade::SolveStrategy::create(SolveMode m, ClaspFacade& f, SolveAlgorithm& algo) {
    if (not Potassco::test(m, SolveMode::async)) {
        return new SolveStrategy(m, f, &algo);
    }
#if CLASP_HAS_THREADS
    return new SolveStrategy::Async(m, f, &algo);
#else
    POTASSCO_CHECK_PRE(CLASP_HAS_THREADS, "Solve mode not supported!");
#endif
}
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspFacade::SolveData
/////////////////////////////////////////////////////////////////////////////////////////
struct ClaspFacade::SolveData {
    struct BoundArray {
        enum Type { lower, costs };
        BoundArray(const SolveData* d, Type t) : data(d), type(t) {}
        ~BoundArray() {
            while (not refs.empty()) {
                delete refs.back();
                refs.pop_back();
            }
        }
        struct LevelRef {
            LevelRef(const BoundArray* a, uint32_t l) : arr(a), at(l) {}
            static double     value(const LevelRef* ref) { return ref->arr->bound(ref->at); }
            const BoundArray* arr;
            uint32_t          at;
        };
        using ElemVec = PodVector_t<LevelRef*>;
        uint32_t        size() const { return data->numBounds(); }
        StatisticObject at(uint32_t i) const {
            POTASSCO_CHECK_PRE(i < size(), "invalid key");
            while (i >= refs.size()) { refs.push_back(new LevelRef(this, size32(refs))); }
            return StatisticObject::value<LevelRef, &LevelRef::value>(refs[i]);
        }
        double bound(uint32_t idx) const {
            POTASSCO_CHECK_PRE(idx < size(), "expired key");
            const Wsum_t bound = data->bound(type, idx);
            return bound != SharedMinimizeData::maxBound() ? static_cast<double>(bound)
                                                           : std::numeric_limits<double>::infinity();
        }
        const SolveData* data;
        mutable ElemVec  refs;
        Type             type;
    };
    using AlgoPtr = std::unique_ptr<SolveAlgorithm>;
    using EnumPtr = std::unique_ptr<Enumerator>;
    using MinPtr  = const SharedMinimizeData*;

    SolveData() = default;
    ~SolveData() { reset(); }
    void init(AlgoPtr a, EnumPtr e);
    void reset();
    void prepareEnum(SharedContext& actx, EnumMode mode, const EnumOptions& options);
    bool interrupt(int sig) {
        if (solving()) {
            return active->interrupt(sig);
        }
        if (sig != SolveStrategy::sig_cancel) {
            qSig.set_if_unset(sig);
        }
        return false;
    }
    bool         onModel(const Solver& s, const Model& m) const { return not active || active->setModel(s, m); }
    bool         solving() const { return active && active->running(); }
    const Model* lastModel() const { return en.get() ? &en->lastModel() : nullptr; }
    LitView      unsatCore() const { return active ? active->unsatCore() : LitView{}; }
    MinPtr       minimizer() const { return en.get() ? en->minimizer() : nullptr; }
    Enumerator*  enumerator() const { return en.get(); }
    int          modelType() const { return en.get() ? en->modelType() : 0; }
    int          signal() const { return solving() ? active->signal() : static_cast<int>(qSig); }
    uint32_t     numBounds() const { return minimizer() ? minimizer()->numRules() : 0; }

    Wsum_t bound(BoundArray::Type type, uint32_t idx) const {
        if (const Model* m = lastModel(); m && m->hasCosts() && (m->opt || type == BoundArray::costs)) {
            POTASSCO_CHECK(idx < m->costs.size(), ERANGE);
            return m->costs[idx];
        }
        const Wsum_t b = type == BoundArray::costs ? minimizer()->sum(idx) : minimizer()->lower(idx);
        return b + (b != SharedMinimizeData::maxBound() ? minimizer()->adjust(idx) : 0);
    }

    EnumPtr        en;
    AlgoPtr        algo;
    SolveStrategy* active = nullptr;
    BoundArray     costs{this, BoundArray::costs};
    BoundArray     lower{this, BoundArray::lower};
    SigAtomic      qSig;
    bool           keepPrg       = false;
    bool           prepared      = false;
    bool           solved        = false;
    bool           interruptible = false;
};
void ClaspFacade::SolveData::init(AlgoPtr a, EnumPtr e) {
    en   = std::move(e);
    algo = std::move(a);
    if (interruptible) {
        algo->enableInterrupts();
    }
}
void ClaspFacade::SolveData::reset() {
    if (active) {
        active->interrupt(SolveStrategy::sig_cancel);
        active->release();
        active = nullptr;
    }
    if (algo.get()) {
        algo->resetSolve();
    }
    if (en.get()) {
        en->reset();
    }
    prepared = solved = false;
}

void ClaspFacade::SolveData::prepareEnum(SharedContext& actx, EnumMode mode, const EnumOptions& options) {
    POTASSCO_CHECK_PRE(not active, "Solve operation still active");
    if (actx.ok() && not actx.frozen() && not prepared) {
        if (mode == enum_volatile && actx.solveMode() == SharedContext::solve_multi) {
            actx.requestStepVar();
        }
        actx.output.setProjectMode(options.proMode);
        auto numM = options.numModels;
        int  lim  = en->init(actx, options.optMode, static_cast<int>(Clasp::clamp(numM, -1, INT_MAX)));
        if (lim == 0 || numM < 0) {
            numM = lim;
        }
        algo->setEnumLimit(numM ? static_cast<uint64_t>(numM) : UINT64_MAX);
        algo->setOptLimit(options.optStop);
        prepared = true;
    }
}
ClaspFacade::SolveHandle::SolveHandle(SolveStrategy* s) : strat_(s->share()) {}
ClaspFacade::SolveHandle::~SolveHandle() { strat_->release(); }
ClaspFacade::SolveHandle::SolveHandle(const SolveHandle& o) : strat_(o.strat_->share()) {}
int  ClaspFacade::SolveHandle::interrupted() const { return strat_->signal(); }
bool ClaspFacade::SolveHandle::error() const { return ready() && strat_->error(); }
bool ClaspFacade::SolveHandle::ready() const { return strat_->ready(); }
bool ClaspFacade::SolveHandle::running() const { return strat_->running(); }
void ClaspFacade::SolveHandle::cancel() const { strat_->interrupt(SolveStrategy::sig_cancel); }
void ClaspFacade::SolveHandle::wait() const { strat_->wait(-1.0); }
bool ClaspFacade::SolveHandle::waitFor(double s) const { return strat_->wait(s); }
void ClaspFacade::SolveHandle::resume() const { strat_->resume(); }
auto ClaspFacade::SolveHandle::get() const -> SolveResult { return strat_->result(); }
auto ClaspFacade::SolveHandle::model() const -> const Model* { return strat_->model(); }
auto ClaspFacade::SolveHandle::unsatCore() const -> LitView { return strat_->unsatCore(); }
bool ClaspFacade::SolveHandle::next() const { return strat_->next(); }
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspFacade::Statistics
/////////////////////////////////////////////////////////////////////////////////////////
namespace {
struct SummaryStats {
    struct Stat {
        const char* key;
        StatisticObject (*get)(const ClaspFacade::Summary*);
    };
    template <double ClaspFacade::Summary::*Time>
    static StatisticObject getT(const ClaspFacade::Summary* x) {
        return StatisticObject::value(&static_cast<const double&>((x->*Time)));
    }
    template <uint64_t ClaspFacade::Summary::*Model>
    static StatisticObject getM(const ClaspFacade::Summary* x) {
        return StatisticObject::value(&static_cast<const uint64_t&>((x->*Model)));
    }
    using StatRange = SpanView<Stat>;

    static constexpr Stat sum_keys[] = {
        {"total", getT<&ClaspFacade::Summary::totalTime>},    {"cpu", getT<&ClaspFacade::Summary::cpuTime>},
        {"solve", getT<&ClaspFacade::Summary::solveTime>},    {"unsat", getT<&ClaspFacade::Summary::unsatTime>},
        {"sat", getT<&ClaspFacade::Summary::satTime>},        {"enumerated", getM<&ClaspFacade::Summary::numEnum>},
        {"optimal", getM<&ClaspFacade::Summary::numOptimal>},
    };

    SummaryStats() = default;
    void bind(const ClaspFacade::Summary& x, StatRange r) {
        stats = &x;
        range = r;
    }
    [[nodiscard]] uint32_t    size() const { return size32(range); }
    [[nodiscard]] const char* key(uint32_t i) const {
        POTASSCO_CHECK(i < size(), ERANGE);
        return range[i].key;
    }
    StatisticObject at(const char* key) const {
        for (const auto& x : range) {
            if (std::strcmp(x.key, key) == 0) {
                return x.get(stats);
            }
        }
        POTASSCO_CHECK(false, ERANGE);
    }
    [[nodiscard]] StatisticObject toStats() const { return StatisticObject::map(this); }
    const ClaspFacade::Summary*   stats{nullptr};
    StatRange                     range;
};

} // namespace
constexpr auto c_get_concurrency = [](const SharedContext* ctx) -> double { return ctx->concurrency(); };
constexpr auto c_get_winner      = [](const SharedContext* ctx) -> double { return ctx->winner(); };
constexpr auto c_get_result      = [](const SolveResult* r) -> double {
    return static_cast<double>(r->operator SolveResult::Res());
};
constexpr auto c_get_signal    = [](const SolveResult* r) -> double { return static_cast<double>(r->signal); };
constexpr auto c_get_exhausted = [](const SolveResult* r) -> double { return static_cast<double>(r->exhausted()); };

struct ClaspFacade::Statistics {
    Statistics(ClaspFacade& f) : self_(&f) {}
    ~Statistics() { delete solvers_.multi; }
    void               start(uint32_t level);
    void               initLevel(uint32_t level);
    void               enableAsp() { lp_ = std::make_unique<Asp::LpStats>(); }
    void               end();
    void               addTo(StatsMap& solving, StatsMap* accu) const;
    void               accept(StatsVisitor& out, bool final) const;
    [[nodiscard]] bool incremental() const { return self_->incremental(); }

    // For clingo stats interface
    class ClingoView : public ClaspStatistics {
    public:
        explicit ClingoView(const ClaspFacade& f);
        void                update(const Statistics& s);
        [[nodiscard]] Key_t user(bool final) const;

    private:
        struct StepStats {
            SummaryStats times;
            SummaryStats models;
            void         bind(const Summary& x) {
                auto r = SummaryStats::StatRange(SummaryStats::sum_keys);
                times.bind(x, r.subspan(0, 5));
                models.bind(x, r.subspan(5));
            }
            void addTo(StatsMap& summary) const {
                summary.add("times", times.toStats());
                summary.add("models", models.toStats());
            }
        };
        StatsMap* keys_;
        StatsMap  problem_;
        StatsMap  solving_;
        struct Summary : StatsMap {
            StepStats step;
        } summary_;
        struct Accu : StatsMap {
            StepStats step;
            StatsMap  solving;
        };
        std::unique_ptr<Accu> accu_;
    };
    ClingoView*                 getClingo();
    [[nodiscard]] Asp::LpStats* lp() const { return lp_.get(); }

private:
    using SolverVec   = StatsVec<SolverStats>;
    using LpStatsPtr  = std::unique_ptr<Asp::LpStats>;
    using TesterStats = PrgDepGraph::NonHcfStats;
    std::unique_ptr<ClingoView> clingo_; // new clingo stats interface
    ClaspFacade*                self_;
    LpStatsPtr                  lp_;              // level 0 and asp
    SolverStats                 solvers_;         // level 0
    SolverVec                   solver_;          // level > 1
    SolverVec                   accu_;            // level > 1 and incremental
    TesterStats*                tester_{nullptr}; // level > 0 and nonhcfs
    uint32_t                    level_{0};        // active stats level
};
void ClaspFacade::Statistics::initLevel(uint32_t level) {
    if (level_ < level) {
        if (incremental() && not solvers_.multi) {
            solvers_.multi = new SolverStats();
        }
        level_ = level;
    }
    if (self_->ctx.sccGraph.get() && self_->ctx.sccGraph->numNonHcfs() && not tester_) {
        tester_ = self_->ctx.sccGraph->nonHcfStats();
    }
}

void ClaspFacade::Statistics::start(uint32_t level) {
    // cleanup previous state
    solvers_.reset();
    solver_.reset();
    if (tester_) {
        tester_->startStep(self_->config()->testerConfig() ? self_->config()->testerConfig()->context().stats : 0);
    }
    // init next step
    initLevel(level);
    if (lp_.get() && self_->step_.lpStep()) {
        lp_->accu(*self_->step_.lpStep());
    }
    if (level > 1 && solver_.size() < self_->ctx.concurrency()) {
        auto newIdx = irange(size32(solver_), self_->ctx.concurrency());
        solver_.growTo(self_->ctx.concurrency());
        if (incremental()) {
            accu_.growTo(size32(solver_));
            for (auto i : newIdx) {
                solver_[i]        = new SolverStats();
                accu_[i]          = new SolverStats();
                solver_[i]->multi = accu_[i];
            }
        }
        else {
            solver_.release();
            for (auto i : newIdx) { solver_[i] = &self_->ctx.solverStats(i); }
        }
    }
}
void ClaspFacade::Statistics::end() {
    self_->ctx.accuStats(solvers_); // compute solvers = sum(solver[1], ... , solver[n])
    solvers_.flush();
    for (uint32_t i = incremental() ? 0 : size32(solver_), end = size32(solver_); i != end && self_->ctx.hasSolver(i);
         ++i) {
        solver_[i]->accu(self_->ctx.solverStats(i), true);
        solver_[i]->flush();
    }
    if (tester_) {
        tester_->endStep();
    }
    if (clingo_) {
        clingo_->update(*this);
    }
}
void ClaspFacade::Statistics::addTo(StatsMap& solving, StatsMap* accu) const {
    solvers_.addTo("solvers", solving, accu);
    if (not solver_.empty()) {
        solving.add("solver", solver_.toStats());
    }
    if (accu && not accu_.empty()) {
        accu->add("solver", accu_.toStats());
    }
}
void ClaspFacade::Statistics::accept(StatsVisitor& out, bool final) const {
    final = final && solvers_.multi;
    if (out.visitGenerator(StatsVisitor::enter)) {
        out.visitSolverStats(final ? *solvers_.multi : solvers_);
        if (lp_.get()) {
            out.visitLogicProgramStats(*lp_);
        }
        out.visitProblemStats(self_->ctx.stats());
        const SolverVec& solver   = final ? accu_ : solver_;
        const uint32_t   nThreads = final ? size32(accu_) : self_->ctx.concurrency();
        const auto       nSolver  = size32(solver);
        if (const AbstractStatistics::Key_t userKey = clingo_ ? clingo_->user(final) : 0) {
            out.visitExternalStats(clingo_->getObject(userKey));
        }
        if (nThreads > 1 && nSolver > 1 && out.visitThreads(StatsVisitor::enter)) {
            for (auto i : irange(std::min(nSolver, nThreads))) { out.visitThread(i, *solver[i]); }
            out.visitThreads(StatsVisitor::leave);
        }
        out.visitGenerator(StatsVisitor::leave);
    }
    if (tester_ && out.visitTester(StatsVisitor::enter)) {
        tester_->accept(out, final);
        out.visitTester(StatsVisitor::leave);
    }
}
ClaspFacade::Statistics::ClingoView* ClaspFacade::Statistics::getClingo() {
    if (not clingo_) {
        clingo_ = std::make_unique<ClingoView>(*this->self_);
        clingo_->update(*this);
    }
    return clingo_.get();
}
ClaspFacade::Statistics::ClingoView::ClingoView(const ClaspFacade& f) {
    keys_ = makeRoot();
    summary_.add("call", StatisticObject::value(&f.step_.step));
    summary_.add("result", StatisticObject::value<SolveResult, c_get_result>(&f.step_.result));
    summary_.add("signal", StatisticObject::value<SolveResult, c_get_signal>(&f.step_.result));
    summary_.add("exhausted", StatisticObject::value<SolveResult, c_get_exhausted>(&f.step_.result));
    summary_.add("costs", StatisticObject::array(&f.solve_->costs));
    summary_.add("lower", StatisticObject::array(&f.solve_->lower));
    summary_.add("concurrency", StatisticObject::value<SharedContext, c_get_concurrency>(&f.ctx));
    summary_.add("winner", StatisticObject::value<SharedContext, c_get_winner>(&f.ctx));
    summary_.step.bind(f.step_);
    summary_.step.addTo(summary_);
    if (f.step_.lpStats()) {
        problem_.add("lp", StatisticObject::map(f.step_.lpStats()));
        if (f.incremental()) {
            problem_.add("lpStep", StatisticObject::map(f.step_.lpStep()));
        }
    }
    problem_.add("generator", StatisticObject::map(&f.ctx.stats()));
    keys_->add("problem", problem_.toStats());
    keys_->add("solving", solving_.toStats());
    keys_->add("summary", summary_.toStats());

    if (f.incremental()) {
        accu_ = std::make_unique<Accu>();
        accu_->step.bind(*f.accu_.get());
    }
}
Potassco::AbstractStatistics::Key_t ClaspFacade::Statistics::ClingoView::user(bool final) const {
    Key_t key = 0;
    find(root(), final ? "user_accu" : "user_step", &key);
    return key;
}
void ClaspFacade::Statistics::ClingoView::update(const ClaspFacade::Statistics& stats) {
    if (stats.level_ > 0 && accu_.get() && keys_->add("accu", accu_->toStats())) {
        accu_->step.addTo(*accu_);
        accu_->add("solving", accu_->solving.toStats());
    }
    stats.addTo(solving_, stats.level_ > 0 && accu_.get() ? &accu_->solving : nullptr);
    if (stats.tester_) {
        stats.tester_->addTo(problem_, solving_, stats.level_ > 0 && accu_.get() ? &accu_->solving : nullptr);
    }
}
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspFacade
/////////////////////////////////////////////////////////////////////////////////////////
ClaspFacade::ClaspFacade() { step_.init(*this); }
ClaspFacade::~ClaspFacade() {
    if (solve_) {
        solve_->reset(); // cancel any active solve operation before resetting our solve pointer
        solve_.reset();
    }
}
bool ClaspFacade::prepared() const { return solve_.get() && solve_->prepared; }
bool ClaspFacade::solving() const { return solve_.get() && solve_->solving() && not solve_->solved; }
bool ClaspFacade::solved() const { return solve_.get() && solve_->solved; }
bool ClaspFacade::interrupted() const { return result().interrupted(); }
bool ClaspFacade::incremental() const { return accu_.get() != nullptr; }
auto ClaspFacade::detectProblemType(std::istream& str) -> ProblemType { return Clasp::detectProblemType(str); }
auto ClaspFacade::summary(bool accu) const -> const Summary& { return accu && accu_.get() ? *accu_ : step_; }

void ClaspFacade::discardProblem() {
    config_  = nullptr;
    builder_ = nullptr;
    stats_   = nullptr;
    solve_   = nullptr;
    accu_    = nullptr;
    step_.init(*this);
    if (ctx.frozen() || ctx.numVars()) {
        ctx.reset();
    }
}
void ClaspFacade::init(ClaspConfig& config, bool discard) {
    if (discard) {
        discardProblem();
    }
    ctx.setConfiguration(nullptr); // force reload of configuration once done
    config_ = &config;
    if (config_->solve.enumMode == EnumOptions::enum_dom_record && config_->solver(0).heuId != HeuristicType::domain) {
        ctx.warn("Reasoning mode requires domain heuristic and is ignored.");
        config_->solve.enumMode = EnumOptions::enum_auto;
    }
    SolveData::EnumPtr e(config.solve.createEnumerator(config.solve));
    if (e.get() == nullptr) {
        e.reset(EnumOptions::nullEnumerator());
    }
    if (config.solve.numSolver() > 1 && not e->supportsParallel()) {
        ctx.warn("Selected reasoning mode implies #Threads=1.");
        config.solve.setSolvers(1);
    }
    ctx.setConfiguration(&config); // prepare and apply config
    if (auto* p = asp()) {
        p->setOptions(config.asp);
        p->setNonHcfConfiguration(config.testerConfig());
    }
    if (not solve_.get()) {
        solve_ = std::make_unique<SolveData>();
    }
    SolveData::AlgoPtr a(config.solve.createSolveObject());
    solve_->init(std::move(a), std::move(e));
    if (discard) {
        startStep(0);
    }
}

void ClaspFacade::initBuilder(ProgramBuilder* in) {
    builder_.reset(in);
    assume_.clear();
    builder_->startProgram(ctx);
}
ProgramBuilder& ClaspFacade::start(ClaspConfig& config, ProblemType t) {
    if (t == ProblemType::sat) {
        return startSat(config);
    }
    if (t == ProblemType::pb) {
        return startPB(config);
    }
    POTASSCO_CHECK(t == ProblemType::asp, EDOM, "Unknown problem type (%u)!", static_cast<uint32_t>(t));
    return startAsp(config);
}

ProgramBuilder& ClaspFacade::start(ClaspConfig& config, std::istream& str) {
    ProgramParser& p = start(config, detectProblemType(str)).parser();
    POTASSCO_CHECK_PRE(p.accept(str, config_->parse), "Auto detection failed!");
    if (p.incremental()) {
        enableProgramUpdates();
    }
    return *program();
}

SatBuilder& ClaspFacade::startSat(ClaspConfig& config) {
    init(config, true);
    initBuilder(new SatBuilder());
    type_ = ProblemType::sat;
    return static_cast<SatBuilder&>(*builder_.get());
}

PBBuilder& ClaspFacade::startPB(ClaspConfig& config) {
    init(config, true);
    initBuilder(new PBBuilder());
    type_ = ProblemType::sat;
    return static_cast<PBBuilder&>(*builder_.get());
}

Asp::LogicProgram& ClaspFacade::startAsp(ClaspConfig& config, bool enableUpdates) {
    init(config, true);
    auto* p = new Asp::LogicProgram();
    initBuilder(p);
    p->setOptions(config.asp);
    p->setNonHcfConfiguration(config.testerConfig());
    type_ = ProblemType::asp;
    stats_->enableAsp();
    if (enableUpdates) {
        enableProgramUpdates();
    }
    return *p;
}
Asp::LogicProgram* ClaspFacade::asp() const {
    return builder_ != nullptr && type_ == ProblemType::asp ? static_cast<Asp::LogicProgram*>(builder_.get()) : nullptr;
}

bool ClaspFacade::enableProgramUpdates() {
    POTASSCO_CHECK_PRE(program(), "Program was already released!");
    POTASSCO_CHECK_PRE(not solving() && not program()->frozen());
    if (not accu_) {
        keepProgram();
        builder_->updateProgram();
        ctx.setSolveMode(SharedContext::solve_multi);
        enableSolveInterrupts();
        accu_ = std::make_unique<Summary>();
        accu_->init(*this);
        accu_->step = UINT32_MAX;
    }
    return asp() != nullptr; // currently only ASP supports program updates
}
void ClaspFacade::enableSolveInterrupts() {
    POTASSCO_CHECK_PRE(not solving(), "Solving is already active!");
    POTASSCO_ASSERT(solve_.get(), "Active program required!");
    if (not solve_->interruptible) {
        solve_->interruptible = true;
        solve_->algo->enableInterrupts();
    }
}

void ClaspFacade::keepProgram() {
    POTASSCO_CHECK_PRE(program(), "Program was already released!");
    POTASSCO_ASSERT(solve_.get(), "Active program required!");
    solve_->keepPrg = true;
    if (auto* p = asp()) {
        p->enableOutputState();
    }
}

void ClaspFacade::startStep(uint32_t n) {
    step_.init(*this);
    step_.totalTime = RealTime::getTime();
    step_.cpuTime   = ProcessTime::getTime();
    step_.step      = n;
    solve_->solved  = false;
    lower_.clear();
    if (not stats_.get()) {
        stats_ = std::make_unique<Statistics>(*this);
    }
    ctx.report(StepStart(*this));
}

ClaspFacade::Result ClaspFacade::stopStep(int signal, bool complete) {
    if (not solved()) {
        double t        = RealTime::getTime();
        solve_->solved  = true;
        step_.totalTime = diffTime(t, step_.totalTime);
        step_.cpuTime   = diffTime(ProcessTime::getTime(), step_.cpuTime);
        if (step_.solveTime != 0.0) {
            step_.solveTime = diffTime(t, step_.solveTime);
            step_.unsatTime = complete ? diffTime(t, step_.unsatTime) : 0;
        }
        Result res = {static_cast<uint8_t>(0), static_cast<uint8_t>(signal)};
        if (complete) {
            res.flags = static_cast<uint8_t>(step_.numEnum ? Result::res_sat : Result::res_unsat) | Result::ext_exhaust;
        }
        else {
            res.flags = static_cast<uint8_t>(step_.numEnum ? Result::res_sat : Result::res_unknown);
        }
        if (signal) {
            res.flags |= static_cast<uint8_t>(Result::ext_interrupt);
        }
        lower_.clear();
        if (const auto* min = enumerator()->minimizer(); min && min->lower(0) != 0) {
            lower_.reserve(min->numRules());
            for (auto i : irange(min->numRules())) { lower_.push_back(min->lower(i) + min->adjust(i)); }
        }
        step_.result = res;
        if (res.sat() && step_.model()->opt && not step_.numOptimal) {
            step_.numOptimal = 1;
        }
        updateStats();
        ctx.report(StepReady(step_));
        ctx.report(Event::subsystem_facade);
    }
    return result();
}

void ClaspFacade::updateStats() {
    if (stats_.get()) {
        stats_->end();
    }
    if (accu_.get() && accu_->step != step_.step) {
        accu_->totalTime  += step_.totalTime;
        accu_->cpuTime    += step_.cpuTime;
        accu_->solveTime  += step_.solveTime;
        accu_->unsatTime  += step_.unsatTime;
        accu_->satTime    += step_.satTime;
        accu_->numEnum    += step_.numEnum;
        accu_->numOptimal += step_.numOptimal;
        // no aggregation
        accu_->step   = step_.step;
        accu_->result = step_.result;
    }
}

bool ClaspFacade::interrupt(int signal) {
    return solve_.get() && (signal || (signal = solve_->qSig.exchange(0)) != 0) && solve_->interrupt(signal);
}

const ClaspFacade::Summary& ClaspFacade::shutdown() {
    if (solve_.get()) {
        solve_->interrupt(SolveStrategy::sig_cancel);
        stopStep(solve_->signal(), not ok());
    }
    return summary(true);
}

bool ClaspFacade::read() {
    POTASSCO_CHECK_PRE(solve_.get());
    if (not program() || interrupted()) {
        return false;
    }
    ProgramParser& p = program()->parser();
    if (not p.isOpen() || (solved() && not update().ok())) {
        return false;
    }
    POTASSCO_CHECK(p.parse(), std::errc::not_supported, "Invalid input stream!");
    if (not p.more()) {
        p.reset();
    }
    return true;
}

void ClaspFacade::prepare(EnumMode enumMode) {
    POTASSCO_CHECK_PRE(solve_.get() && not solving());
    POTASSCO_CHECK_PRE(not solved() || ctx.solveMode() == SharedContext::solve_multi);
    EnumOptions& en = config_->solve;
    if (solved()) {
        doUpdate(nullptr, false, SIG_DFL);
        solve_->prepareEnum(ctx, enumMode, en);
        ctx.endInit();
    }
    if (prepared()) {
        return;
    }
    if (ProgramBuilder* prg = program(); prg && prg->endProgram()) {
        assume_.clear();
        prg->getAssumptions(assume_);
        prg->getWeakBounds(en.optBound);
    }
    stats_->start(config_->context().stats);
    if (ctx.ok() && en.optMode != MinimizeMode::ignore && ctx.hasMinimize()) {
        if (not ctx.minimize()->setMode(en.optMode, en.optBound)) {
            assume_.push_back(lit_false);
        }
        if (en.optMode == MinimizeMode::enumerate && en.optBound.empty()) {
            ctx.warn("opt-mode=enum: No bound given, optimize statement ignored.");
        }
    }
    if (incremental() || config_->solver(0).heuId == HeuristicType::domain) {
        ctx.setPreserveHeuristic(true);
    }
    POTASSCO_CHECK_PRE(not ctx.ok() || not ctx.frozen());
    solve_->prepareEnum(ctx, enumMode, en);
    if (not solve_->keepPrg) {
        builder_ = nullptr;
    }
    else if (auto* p = asp(); p) {
        p->dispose();
    }
    if (not builder_.get() && not ctx.heuristic.empty() &&
        std::ranges::none_of(irange(config_->solve.numSolver()),
                             [&](uint32_t sId) { return config_->solver(sId).heuId == HeuristicType::domain; })) {
        ctx.heuristic.reset();
    }
    if (ctx.ok()) {
        ctx.endInit();
    }
}

ClaspFacade::SolveHandle ClaspFacade::solve(SolveMode p, LitView a, EventHandler* eh) {
    prepare();
    solve_->active = SolveStrategy::create(p, *this, *solve_->algo.get());
    solve_->active->start(eh, a);
    return SolveHandle(solve_->active);
}
ClaspFacade::Result ClaspFacade::solve(LitView a, EventHandler* handler) {
    return solve(SolveMode::def, a, handler).get();
}

ProgramBuilder& ClaspFacade::update(bool updateConfig, void (*sigAct)(int)) {
    POTASSCO_CHECK_PRE(config_ && program() && not solving(), "Program updates not supported!");
    POTASSCO_CHECK_PRE(not program()->frozen() || incremental(), "Program updates not supported!");
    doUpdate(program(), updateConfig, sigAct);
    return *program();
}

void ClaspFacade::doUpdate(ProgramBuilder* p, bool updateConfig, void (*sigAct)(int)) {
    if (updateConfig) {
        init(*config_, false);
    }
    if (solved()) {
        startStep(static_cast<uint32_t>(step()) + 1u);
    }
    if (p && p->frozen()) {
        p->updateProgram();
    }
    if (ctx.frozen()) {
        ctx.unfreeze();
    }
    solve_->reset();
    config_->unfreeze(ctx);
    int sig = sigAct == SIG_DFL ? 0 : solve_->qSig.exchange(0);
    if (sig && sigAct != SIG_IGN) {
        sigAct(sig);
    }
}

bool ClaspFacade::onModel(const Solver& s, const Model& m) {
    step_.unsatTime = RealTime::getTime();
    if (++step_.numEnum == 1) {
        step_.satTime = diffTime(step_.unsatTime, step_.solveTime);
    }
    if (m.opt) {
        ++step_.numOptimal;
    }
    return solve_->onModel(s, m);
}
Enumerator*                   ClaspFacade::enumerator() const { return solve_.get() ? solve_->enumerator() : nullptr; }
Potassco::AbstractStatistics* ClaspFacade::getStats() const {
    POTASSCO_CHECK_PRE(stats_.get() && not solving(), "statistics not (yet) available");
    return stats_->getClingo();
}
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspFacade::Summary
/////////////////////////////////////////////////////////////////////////////////////////
void ClaspFacade::Summary::init(ClaspFacade& f) {
    std::memset(this, 0, sizeof(Summary));
    facade = &f;
}
const Model* ClaspFacade::Summary::model() const {
    return facade->solve_.get() ? facade->solve_->lastModel() : nullptr;
}
auto ClaspFacade::Summary::costs() const -> SumView { return model() ? model()->costs : SumView{}; }
auto ClaspFacade::Summary::optimal() const -> uint64_t { return facade->step_.numOptimal; }
bool ClaspFacade::Summary::optimize() const {
    if (const Enumerator* e = facade->enumerator()) {
        return e->optimize() || e->lastModel().opt;
    }
    return false;
}
LitView ClaspFacade::Summary::unsatCore() const { return facade->solve_ ? facade->solve_->unsatCore() : LitView{}; }
const Asp::LpStats* ClaspFacade::Summary::lpStep() const {
    auto* p = facade->asp();
    return p ? &p->stats : nullptr;
}
const Asp::LpStats* ClaspFacade::Summary::lpStats() const {
    return facade->stats_.get() ? facade->stats_->lp() : lpStep();
}
const char* ClaspFacade::Summary::consequences() const {
    const auto* m = model();
    return m && m->consequences() ? modelType(*m) : nullptr;
}

bool    ClaspFacade::Summary::hasCosts() const { return model() && model()->hasCosts(); }
bool    ClaspFacade::Summary::hasLower() const { return not facade->lower_.empty(); }
SumView ClaspFacade::Summary::lower() const { return facade->lower_; }
void    ClaspFacade::Summary::accept(StatsVisitor& out) const {
    if (facade->solved()) {
        facade->stats_->accept(out, this == facade->accu_.get());
    }
}

} // namespace Clasp
