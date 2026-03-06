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

#include <clasp/clingo.h>
#include <clasp/dependency_graph.h>
#include <clasp/lookahead.h>
#include <clasp/minimize_constraint.h>
#include <clasp/parser.h>
#include <clasp/unfounded_check.h>
#include <clasp/util/timer.h>

#include <potassco/format.h>

#include <climits>
#include <cmath>
#if CLASP_HAS_THREADS
#include <clasp/mt/thread.h>
#endif
namespace Clasp {
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspConfig
/////////////////////////////////////////////////////////////////////////////////////////
ClaspConfig::Configurator::~Configurator() = default;
void ClaspConfig::Configurator::detach(const ClaspConfig&) {}
ClaspConfig::~ClaspConfig() { setConfigurator(nullptr, false); }

void ClaspConfig::reset() {
    if (tester_) {
        tester_->reset();
    }
    BasicSatConfig::reset();
    solve    = SolveOptions();
    asp      = AspOptions();
    prepared = false;
}

auto ClaspConfig::addTesterConfig() -> BasicSatConfig* {
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
        ctx.warn(Potassco::BasicCharBuffer{}
                     .appendSep("", "Oversubscription: #Threads=", numS,
                                " exceeds logical CPUs=", SolveOptions::recommendedSolvers(), '.')
                     .c_str());
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
    prepared = true;
}

auto ClaspConfig::config(const char* n) -> Configuration* {
    return (n && std::strcmp(n, "tester") == 0) ? testerConfig() : BasicSatConfig::config(n);
}
bool ClaspConfig::addPost(Solver& s) const {
    if (s.sharedContext()->sccGraph.get()) {
        const auto& opts = solver(s.id());
        if (auto* ufs = s.getPost<DefaultUnfoundedCheck>()) {
            ufs->setReasonStrategy(static_cast<DefaultUnfoundedCheck::ReasonStrategy>(opts.loopRep));
        }
        else if (not s.addPost(new DefaultUnfoundedCheck(
                     *s.sharedContext()->sccGraph, static_cast<DefaultUnfoundedCheck::ReasonStrategy>(opts.loopRep)))) {
            return false;
        }
    }
    if (s.sharedContext()->extGraph.get()) {
        if (not s.getPost<AcyclicityCheck>() && not s.addPost(new AcyclicityCheck(s.sharedContext()->extGraph.get()))) {
            return false;
        }
    }
    return BasicSatConfig::addPost(s) && (not configurator_ || configurator_->addPropagators(s));
}
void ClaspConfig::setHeuristic(Solver& s) const {
    return configurator_ ? configurator_->setHeuristic(s) : BasicSatConfig::setHeuristic(s);
}
void ClaspConfig::setConfigurator(Configurator* configurator, bool notifyDetach) {
    if (configurator_.get() != configurator) {
        if (configurator_ && configurator_.test<0>()) {
            configurator_->detach(*this);
        }
        configurator_ = TaggedPtr{configurator};
    }
    if (configurator_ && configurator_.test<0>() != notifyDetach) {
        configurator_.toggle<0>();
    }
}
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspFacade::SolveStrategy
/////////////////////////////////////////////////////////////////////////////////////////
struct ClaspFacade::SolveStrategy {
    static constexpr int sig_cancel = 9;
    static constexpr int sig_error  = 128;
    enum State : uint32_t { state_run = 1u, state_model = 2u, state_done = 4u };
    enum Event { event_attach, event_model, event_resume, event_detach };
    virtual ~SolveStrategy() = default;
    static auto        create(SolveMode m, ClaspFacade& f, SolveAlgorithm& algo) -> SolveStrategy*;
    void               start(EventHandler* h, LitView a);
    [[nodiscard]] bool running() const noexcept { return (state_ & (state_done - 1u)) != 0u; }
    [[nodiscard]] bool error() const noexcept { return signal_ == sig_error; }
    [[nodiscard]] bool ready() const noexcept { return state_ != state_run; }
    [[nodiscard]] int  signal() const noexcept { return signal_; }
    bool               interrupt(int sig) {
        bool stopped = running() && signal_.set_if_unset(sig) && algo_->interrupt();
        if (stopped) {
            facade_->step_.killTime = RealTime::getTime();
        }
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
    bool setUnsat(const Solver& s, const Model& m) {
        auto* globalHandler = s.sharedContext()->eventHandler();
        return (not handler_ || handler_->onUnsat(s, m)) && (not globalHandler || globalHandler->onUnsat(s, m));
    }
    auto result() -> Result {
        wait(-1.0);
        POTASSCO_CHECK(not error(), std::errc::operation_canceled, "%s", error_.c_str());
        return result_;
    }
    auto model() -> const Model* {
        return state_ == state_model || (result().sat() && state_ == state_model) ? &algo_->model() : nullptr;
    }
    auto unsatCore() -> LitView { return result().unsat() ? algo_->unsatCore() : LitView{}; }
    bool next() { return running() && (state_ != state_model || (resume(), true)) && model() != nullptr; }
    void release() {
        if (auto n = nrefs_.release_fetch(); n == 1u) {
            interrupt(sig_cancel);
        }
        else if (n == 0) {
            delete this;
        }
    }
    auto share() -> SolveStrategy* {
        nrefs_.add();
        return this;
    }

protected:
    SolveStrategy(SolveMode m, ClaspFacade& f, SolveAlgorithm* algo);
    void            startAlgo(SolveMode m);
    void            continueAlgo();
    ClaspFacade*    facade_;
    SolveAlgorithm* algo_;

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
            POTASSCO_CHECK_PRE(en, "Enumerator expected!");
            facade_->step_.solveTime = facade_->step_.unsatTime = RealTime::getTime();
            facade_->ctx.enter(Clasp::Event::subsystem_solve);
            if (not Potassco::test(m, SolveMode::yield)) {
                detacher.more = algo_->solve(*en, facade_->ctx, facade_->assume_, facade_);
            }
            else {
                algo_->start(*en, facade_->ctx, facade_->assume_, facade_);
                detacher.self = nullptr;
            }
        }
        else {
            facade_->ctx.enter(Clasp::Event::subsystem_solve);
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
        // acknowledge the current model or join if first to see done
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
        lock.unlock(); // synchronize with other threads but no need to notify under lock
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
auto ClaspFacade::SolveStrategy::create(SolveMode m, ClaspFacade& f, SolveAlgorithm& algo) -> SolveStrategy* {
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
    [[nodiscard]] bool onModel(const Solver& s, const Model& m) const { return not active || active->setModel(s, m); }
    [[nodiscard]] bool onUnsat(const Solver& s, const Model& m) const { return not active || active->setUnsat(s, m); }
    [[nodiscard]] bool solving() const { return active && active->running(); }
    [[nodiscard]] auto lastModel() const -> const Model* { return en.get() ? &en->lastModel() : nullptr; }
    [[nodiscard]] auto unsatCore() const -> LitView { return active ? active->unsatCore() : LitView{}; }
    [[nodiscard]] auto minimizer() const -> MinPtr { return en.get() ? en->minimizer() : nullptr; }
    [[nodiscard]] auto enumerator() const -> Enumerator* { return en.get(); }
    [[nodiscard]] auto modelType() const -> int { return en.get() ? en->modelType() : 0; }
    [[nodiscard]] auto signal() const -> int { return solving() ? active->signal() : static_cast<int>(qSig); }

    EnumPtr        en;
    AlgoPtr        algo;
    SolveStrategy* active = nullptr;
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
    }
    prepared = true;
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
using namespace std::literals;

struct ClaspFacade::Statistics {
    Statistics(ClaspFacade& f) : self_(&f) {}
    ~Statistics() { DeleteObject{}(solvers_.multi); }
    void               start(uint32_t level);
    void               freeze();
    void               initLevel(uint32_t level);
    void               enableAsp() { lp_ = std::make_unique<Asp::LpStats>(); }
    void               end();
    void               accept(StatsVisitor& out, bool final) const;
    [[nodiscard]] bool incremental() const { return self_->incremental(); }

    class SolverStatsVec {
    public:
        using value_type = PodVector_t<SolverStats*>::value_type;
        static auto getStats(const value_type& x) -> StatisticObject { return StatisticObject::map(x); }
        ~SolverStatsVec() { std::ranges::for_each(stats_, DeleteObject{}); }

        void update(const SharedContext& sc, uint32_t newActive, bool accu) {
            std::ranges::for_each(std::span{stats_}.first(accu ? 0u : active_), [](SolverStats* s) { s->reset(); });
            if (auto os = size32(stats_); newActive > os) {
                stats_.resize(newActive);
                std::ranges::generate_n(stats_.data() + os, newActive - os, [] { return new SolverStats{}; });
            }
            for (auto i : irange(std::min(newActive, sc.concurrency()))) { stats_[i]->accu(sc.solverStats(i), true); }
            active_ = newActive;
        }
        [[nodiscard]] auto size() const -> uint32_t { return active_; }
        [[nodiscard]] auto at(uint32_t idx) const -> const value_type& { return stats_.at(idx); }
        [[nodiscard]] auto exported() const -> bool { return exported_ != 0u; }
        [[nodiscard]] auto setExported(bool b) { exported_ = static_cast<uint32_t>(b); }

    private:
        PodVector_t<SolverStats*> stats_;
        uint32_t                  active_   : 31 {0};
        uint32_t                  exported_ : 1 {0};
    };

    // For clingo stats interface
    class ClingoView : public ClaspStatistics {
    public:
        explicit ClingoView(const ClaspFacade& f);
        void visitUser(bool final, StatsVisitor& out) const;
        void update(const ClaspFacade& f);

    private:
        struct Item {
            std::string_view key;
            StatisticObject (*get)(const Summary*);
        };
        static auto           getConcurrency(const SharedContext* ctx) -> double { return ctx->concurrency(); }
        static auto           getWinner(const SharedContext* ctx) -> double { return ctx->winner(); }
        static constexpr auto getResult(const SolveResult* r) -> double {
            return static_cast<double>(r->operator SolveResult::Res());
        }
        static constexpr auto getSignal(const SolveResult* r) -> double { return static_cast<double>(r->signal); }
        static constexpr auto getExhausted(const SolveResult* r) -> double {
            return static_cast<double>(r->exhausted());
        }

        using StatRange = SpanView<Item>;
#define LIFT(X) +[](const Summary* s) { return X; }
        static constexpr Item time_stats[] = {
            {"total"sv, LIFT(StatisticObject::value(&s->totalTime))},
            {"cpu"sv, LIFT(StatisticObject::value(&s->cpuTime))},
            {"solve"sv, LIFT(StatisticObject::value(&s->solveTime))},
            {"unsat"sv, LIFT(StatisticObject::value(&s->unsatTime))},
            {"sat"sv, LIFT(StatisticObject::value(&s->satTime))},
        };
        static constexpr Item model_stats[] = {
            {"enumerated"sv, LIFT(StatisticObject::value(&s->numEnum))},
            {"optimal"sv, LIFT(StatisticObject::value(&s->numOptimal))},
        };
        static constexpr Item result_stats[] = {
            {"call"sv, LIFT(StatisticObject::value(&s->step))},
            {"result"sv, LIFT(StatisticObject::value<getResult>(&s->result))},
            {"signal"sv, LIFT(StatisticObject::value<getSignal>(&s->result))},
            {"exhausted"sv, LIFT(StatisticObject::value<getExhausted>(&s->result))},
            {"concurrency"sv, LIFT(StatisticObject::value<getConcurrency>(&s->facade->ctx))},
            {"winner"sv, LIFT(StatisticObject::value<getWinner>(&s->facade->ctx))},
        };
#undef LIFT
        struct StatsObject {
            explicit StatsObject(const Summary* s = nullptr, StatRange r = {}) : stats(s), range(r) {}
            [[nodiscard]] constexpr auto size() const -> uint32_t { return size32(range); }
            [[nodiscard]] constexpr auto key(uint32_t i) const -> std::string_view {
                POTASSCO_CHECK(i < size(), ERANGE);
                return range[i].key;
            }
            [[nodiscard]] constexpr auto at(std::string_view key) const -> StatisticObject {
                auto it = std::ranges::find_if(range, [&](const Item& s) { return s.key == key; });
                POTASSCO_CHECK(it != range.end(), ERANGE);
                return it->get(stats);
            }
            const Summary* stats{nullptr};
            StatRange      range;
        };
        struct SummaryStats {
            static constexpr std::string_view extra_keys[] = {"times"sv, "models"sv, "costs"sv, "lower"sv};
            //
            void bind(const Summary& s) {
                times  = StatsObject(&s, time_stats);
                models = StatsObject(&s, model_stats);
                result = StatsObject(&s, result_stats);
            }
            [[nodiscard]] constexpr auto size() const -> uint32_t { return result.size() + size32(extra_keys); }
            [[nodiscard]] constexpr auto key(uint32_t i) const -> std::string_view {
                POTASSCO_CHECK(i < size(), ERANGE);
                return i < size32(result) ? result.key(i) : extra_keys[i - size32(result)];
            }
            [[nodiscard]] constexpr auto at(std::string_view key) const -> StatisticObject {
                if (auto it = std::ranges::find(extra_keys, key); it != std::end(extra_keys)) {
                    switch (key[0]) {
                        case 't': return StatisticObject::map(&times);
                        case 'm': return StatisticObject::map(&models);
                        case 'c': return StatisticObject::array<&BoundsArray::getUpper>(&bounds);
                        default : return StatisticObject::array<&BoundsArray::getLower>(&bounds);
                    }
                }
                return result.at(key);
            }
            // NOTE: In Clingo issue #242, we decided to always expose the bounds of any minimize statement even if
            //       they are not relevant. This is deliberately different from the costs()/lower() view provided by
            //       ClaspFacade::Summary.
            void updateBounds(const SolveData* data) {
                const auto* minimizer = data ? data->minimizer() : nullptr;
                const auto  numBounds = minimizer ? minimizer->numRules() : 0u;
                auto&       values    = bounds.data;
                values.resize(std::max(numBounds, size32(values)));
                static constexpr auto no_bound  = std::numeric_limits<double>::quiet_NaN();
                static constexpr auto max_bound = SharedMinimizeData::maxBound();
                static constexpr auto toDouble  = [](Wsum_t b) {
                    return b != max_bound ? static_cast<double>(b) : std::numeric_limits<double>::infinity();
                };
                for (auto level : irange(size32(values))) {
                    if (level < numBounds) {
                        assert(minimizer);
                        if (not values[level]) {
                            values[level] = new BoundsArray::Bound;
                        }
                        auto u               = minimizer->sum(level);
                        auto l               = minimizer->lower(level);
                        auto a               = minimizer->adjust(level);
                        values[level]->lower = toDouble(l + a * (l != max_bound));
                        values[level]->upper = toDouble(u + a * (u != max_bound));
                    }
                    else {
                        assert(values[level]);
                        *values[level] = BoundsArray::Bound{no_bound, no_bound};
                    }
                }
                bounds.active = numBounds;
            }
            StatsObject times;
            StatsObject models;
            StatsObject result;
            // Array for upper/lower bounds
            struct BoundsArray {
                struct Bound {
                    double lower{};
                    double upper{};
                };
                using value_type = Bound*;
                static double get(const double* val) {
                    POTASSCO_CHECK(not std::isnan(*val), ERANGE, "Expired key");
                    return *val;
                }
                static auto getUpper(const value_type& val) -> StatisticObject {
                    return StatisticObject::value<&get>(&val->upper);
                }
                static auto getLower(const value_type& val) -> StatisticObject {
                    return StatisticObject::value<&get>(&val->lower);
                }
                explicit BoundsArray() = default;
                ~BoundsArray() { std::ranges::for_each(data, DeleteObject{}); }
                [[nodiscard]] auto size() const -> uint32_t { return active; }
                [[nodiscard]] auto at(uint32_t i) const -> const value_type& {
                    POTASSCO_CHECK(i < size(), ERANGE, "Invalid key");
                    return data[i];
                }
                PodVector_t<value_type> data;
                uint32_t                active{0};
            };
            BoundsArray bounds;
        } summary_;
        SolverStatsVec solver_;
        struct Accu {
            void bind(const Summary& s) {
                times  = StatsObject(&s, time_stats);
                models = StatsObject(&s, model_stats);
            }
            StatsObject times;
            StatsObject models;
            Key_t       root{0};
            Key_t       solving{0};
        } accu_;
        Key_t problem_{0};
        Key_t solving_{0};
    };
    ClingoView*                 getClingo();
    [[nodiscard]] Asp::LpStats* lp() const { return lp_.get(); }

private:
    using LpStatsPtr = std::unique_ptr<Asp::LpStats>;
    std::unique_ptr<ClingoView> clingo_; // new clingo stats interface
    ClaspFacade*                self_;
    LpStatsPtr                  lp_;       // level 0 and asp
    SolverStats                 solvers_;  // level 0
    SolverStatsVec              accu_;     // level > 1
    uint32_t                    level_{0}; // active stats level
};
void ClaspFacade::Statistics::initLevel(uint32_t level) {
    if (level_ < level) {
        if (incremental() && not solvers_.multi) {
            solvers_.multi = new SolverStats();
        }
        level_ = level;
    }
}

void ClaspFacade::Statistics::start(uint32_t level) {
    // cleanup previous state
    solvers_.reset();
    if (self_->ctx.sccGraph) {
        self_->ctx.sccGraph->resetStats();
    }
    // init next step
    initLevel(level);
    if (lp_.get() && self_->step_.lpStep()) {
        lp_->accu(*self_->step_.lpStep());
    }
}
void ClaspFacade::Statistics::freeze() {
    if (clingo_) {
        clingo_->freeze(true);
    }
}
void ClaspFacade::Statistics::end() {
    self_->ctx.accuStats(solvers_); // compute solvers = sum(solver[1], ... , solver[n])
    solvers_.flush();
    if (level_ > 1 && incremental()) {
        accu_.update(self_->ctx, std::max(self_->ctx.concurrency(), accu_.size()), true);
    }
    if (self_->ctx.sccGraph) {
        self_->ctx.sccGraph->accuStats();
    }
    if (clingo_) {
        clingo_->freeze(false);
        clingo_->update(*self_);
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
        if (clingo_) {
            clingo_->visitUser(final, out);
        }
        const auto nThreads = final ? size32(accu_) : self_->ctx.concurrency();
        if (nThreads > 1 && out.visitThreads(StatsVisitor::enter)) {
            for (auto i : irange(nThreads)) {
                auto& stats = not final ? self_->ctx.solverStats(i) : *accu_.at(i);
                out.visitThread(i, stats);
            }
            out.visitThreads(StatsVisitor::leave);
        }
        out.visitGenerator(StatsVisitor::leave);
    }
    if (self_->ctx.sccGraph) {
        self_->ctx.sccGraph->accept(out, final);
    }
}
auto ClaspFacade::Statistics::getClingo() -> ClingoView* {
    if (not clingo_) {
        clingo_ = std::make_unique<ClingoView>(*self_);
    }
    return clingo_.get();
}
ClaspFacade::Statistics::ClingoView::ClingoView(const ClaspFacade& f) {
    summary_.bind(f.step_);
    problem_ = ClaspStatistics::add(ClaspStatistics::root(), "problem", Type::map);
    solving_ = ClaspStatistics::add(ClaspStatistics::root(), "solving", Type::map);
    addObject(ClaspStatistics::root(), "summary", StatisticObject::map(&summary_), true);
    addObject(problem_, "generator", StatisticObject::map(&f.ctx.stats()), true);
    if (f.step_.lpStats()) {
        addObject(problem_, "lp", StatisticObject::map(f.step_.lpStats()), true);
        if (auto step = f.step_.lpStep(); step && step != f.step_.lpStats()) {
            addObject(problem_, "lpStep", StatisticObject::map(step), true);
        }
    }
    addObject(solving_, "solvers", StatisticObject::map(&f.stats_->solvers_), true);
    update(f);
}
void ClaspFacade::Statistics::ClingoView::visitUser(bool final, StatsVisitor& out) const {
    visitExternal(final ? user_accu_stats : user_step_stats, out);
}
void ClaspFacade::Statistics::ClingoView::update(const ClaspFacade& f) {
    auto& stats = *f.stats_;
    summary_.updateBounds(f.solve_.get());
    solver_.update(f.ctx, stats.level_ > 1 ? f.ctx.concurrency() : 0u, false);
    if (stats.level_ > 0 && stats.incremental()) {
        if (not accu_.root) {
            accu_.bind(*f.accu_.get());
            accu_.root = ClaspStatistics::add(ClaspStatistics::root(), "accu", Type::map);
            addObject(accu_.root, "times", StatisticObject::map(&accu_.times), true);
            addObject(accu_.root, "models", StatisticObject::map(&accu_.models), true);
        }
        if (stats.solvers_.multi && not accu_.solving) {
            accu_.solving = ClaspStatistics::add(accu_.root, "solving", Type::map);
            addObject(accu_.solving, "solvers", StatisticObject::map(stats.solvers_.multi), true);
        }
    }
    if (stats.level_ > 1 && not solver_.exported()) {
        addObject(solving_, "solver", StatisticObject::array<&SolverStatsVec::getStats>(&solver_), true);
        if (accu_.solving) {
            addObject(accu_.solving, "solver", StatisticObject::array<&SolverStatsVec::getStats>(&stats.accu_), true);
        }
        solver_.setExported(true);
    }
    if (stats.self_->ctx.sccGraph) {
        stats.self_->ctx.sccGraph->accept(*this, problem_, solving_, accu_.solving ? &accu_.solving : nullptr);
    }
}
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspFacade
/////////////////////////////////////////////////////////////////////////////////////////
static constexpr auto cast(Potassco::AbstractPropagator::Init* init) -> ClingoPropagatorInit* {
    return static_cast<ClingoPropagatorInit*>(init); // NOLINT(cppcoreguidelines-pro-type-static-cast-downcast)
}
ClaspFacade::ClaspFacade() { step_.init(*this); }
ClaspFacade::~ClaspFacade() {
    if (solve_) {
        solve_->reset(); // cancel any active solve operation before resetting our solve-pointer
        solve_.reset();
    }
    discardProblem();
}
bool ClaspFacade::prepared() const { return solve_.get() && solve_->prepared; }
bool ClaspFacade::solving() const { return solve_.get() && solve_->solving() && not solve_->solved; }
bool ClaspFacade::solved() const { return solve_.get() && solve_->solved; }
bool ClaspFacade::interrupted() const { return result().interrupted(); }
bool ClaspFacade::incremental() const { return accu_.get() != nullptr; }
auto ClaspFacade::detectProblemType(std::istream& str) -> ProblemType { return Clasp::detectProblemType(str); }
auto ClaspFacade::summary(bool accu) const -> const Summary& { return accu && accu_.get() ? *accu_ : step_; }

void ClaspFacade::discardProblem() {
    if (auto* c = std::exchange(config_, nullptr); c) {
        c->setConfigurator(nullptr, false);
    }
    builder_ = nullptr;
    stats_   = nullptr;
    solve_   = nullptr;
    accu_    = nullptr;
    std::ranges::for_each(std::exchange(propagators_, {}), DeleteObject{});
    heuristic_.reset();
}
void ClaspFacade::init(ClaspConfig& config) {
    ctx.setConfiguration(nullptr); // force reload of configuration once done
    config_ = &config;
    config_->setConfigurator(this, true);
    if (config_->solve.enumMode == EnumOptions::enum_dom_record && config_->solver(0).heuId != HeuristicType::domain) {
        ctx.warn("Reasoning mode requires domain heuristic and is ignored.");
        config_->solve.enumMode = EnumOptions::enum_auto;
    }
    auto e = config.solve.createEnumerator(config.solve);
    if (e == nullptr) {
        e = EnumOptions::nullEnumerator();
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
    solve_->init(config.solve.createSolveObject(), std::move(e));
}
void ClaspFacade::detach(const ClaspConfig& cfg) {
    if (config_ == &cfg) {
        config_ = nullptr;
    }
}
auto ClaspFacade::initBuilder(ClaspConfig& cfg, std::unique_ptr<ProgramBuilder> in, ProblemType t) -> ProgramBuilder& {
    discardProblem();
    step_.init(*this);
    if (ctx.frozen() || ctx.numVars()) {
        ctx.reset();
    }
    init(cfg);
    builder_ = std::move(in);
    type_    = t;
    assume_.clear();
    startStep(0);
    ctx.enter(Event::subsystem_load);
    builder_->startProgram(ctx);
    return *builder_;
}
auto ClaspFacade::start(ClaspConfig& config, ProblemType t) -> ProgramBuilder& {
    if (t == ProblemType::sat) {
        return startSat(config);
    }
    if (t == ProblemType::pb) {
        return startPB(config);
    }
    POTASSCO_CHECK(t == ProblemType::asp, EDOM, "Unknown problem type (%u)!", static_cast<uint32_t>(t));
    return startAsp(config);
}

auto ClaspFacade::start(ClaspConfig& config, std::istream& str) -> ProgramBuilder& {
    ProgramParser& p = start(config, detectProblemType(str)).parser();
    POTASSCO_CHECK(p.accept(str, config_->parse), std::errc::not_supported, "Unexpected input");
    if (p.incremental()) {
        enableProgramUpdates();
    }
    return *program();
}

auto ClaspFacade::startSat(ClaspConfig& config) -> SatBuilder& {
    return static_cast<SatBuilder&>(initBuilder(config, std::make_unique<SatBuilder>(), ProblemType::sat));
}

auto ClaspFacade::startPB(ClaspConfig& config) -> PBBuilder& {
    return static_cast<PBBuilder&>(initBuilder(config, std::make_unique<PBBuilder>(), ProblemType::pb));
}

auto ClaspFacade::startAsp(ClaspConfig& config, bool enableUpdates) -> Asp::LogicProgram& {
    auto& p =
        static_cast<Asp::LogicProgram&>(initBuilder(config, std::make_unique<Asp::LogicProgram>(), ProblemType::asp));
    p.setOptions(config.asp);
    p.setNonHcfConfiguration(config.testerConfig());
    stats_->enableAsp();
    if (enableUpdates) {
        enableProgramUpdates();
    }
    return p;
}
auto ClaspFacade::asp() const -> Asp::LogicProgram* {
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
}
void ClaspFacade::registerPropagator(Potassco::AbstractPropagator& prop, bool distinctTrue) {
    POTASSCO_CHECK_PRE(not prepared(), "Propagator must be added before program is prepared");
    if (distinctTrue && incremental()) {
        POTASSCO_CHECK_PRE(asp(), "Distinct true literal only supported for ASP programs");
        asp()->enableDistinctTrue();
    }
    ClingoPropagatorInit::MapLitCb mapper;
    if (asp()) {
        keepProgram();
        mapper = [asp = asp()](Potassco::Lit_t lit) {
            return encodeLit(asp->getLiteral(Asp::id(lit), Asp::MapLit::refined));
        };
    }
    auto ppInit = std::make_unique<ClingoPropagatorInit>(ctx, prop, std::move(mapper));
    propagators_.push_back(nullptr);
    propagators_.back() = ppInit.release();
}
void ClaspFacade::registerHeuristic(Potassco::AbstractHeuristic& heuristic) {
    POTASSCO_CHECK_PRE(config_, "Program not started");
    POTASSCO_CHECK_PRE(not prepared(), "Heuristic must be added before program is prepared");
    struct Self : Potassco::AbstractHeuristic {
        auto decide(const Potassco::AbstractAssignment& assignment,
                    Potassco::Lit_t                     fallback) -> Potassco::Lit_t override {
            for (auto* h : heuristics) {
                if (auto ret = h->decide(assignment, fallback); ret != 0) {
                    return ret;
                }
            }
            return fallback;
        }
        PodVector_t<Potassco::AbstractHeuristic*> heuristics;
    };
    if (not heuristic_) {
        heuristic_ = std::make_unique<Self>();
    }
    static_cast<Self*>(heuristic_.get())->heuristics.push_back(&heuristic);
}
void ClaspFacade::setHeuristic(Solver& s) {
    HeuristicFactory factory;
    if (heuristic_) {
        factory = [&](HeuristicType type, const HeuParams& p) {
            return std::make_unique<ClingoHeuristic>(*heuristic_, Clasp::createHeuristic(type, p).release());
        };
    }
    s.setHeuristic(config_->solver(s.id()).createHeuristic(factory).release());
}
bool ClaspFacade::addPropagators(Solver& s) {
    for (auto* init : propagators_) {
        if (not cast(init)->addPropagator(s)) {
            return false;
        }
    }
    return true;
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

auto ClaspFacade::stopStep(int signal, bool complete) -> Result {
    if (not solved()) {
        double t        = RealTime::getTime();
        solve_->solved  = true;
        step_.totalTime = RealTime::diffTime(t, step_.totalTime);
        step_.cpuTime   = ProcessTime::diffTime(step_.cpuTime);
        if (step_.solveTime != 0.0) {
            step_.solveTime = RealTime::diffTime(t, step_.solveTime);
            step_.unsatTime = complete ? RealTime::diffTime(t, step_.unsatTime) : 0;
        }
        if (step_.killTime != 0.0) {
            step_.killTime = RealTime::diffTime(t, step_.killTime);
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
        ctx.enter(Event::subsystem_facade);
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

auto ClaspFacade::shutdown() -> const Summary& {
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
    if (not p.isOpen() || (solved() && not update())) {
        return false;
    }
    POTASSCO_CHECK(p.parse(), std::errc::not_supported, "Invalid input stream!");
    if (not p.more()) {
        p.reset();
    }
    return true;
}

bool ClaspFacade::prepare(EnumMode enumMode) {
    POTASSCO_CHECK_PRE(solve_.get() && not solving());
    EnumOptions& en = config_->solve;
    if (solved()) {
        doUpdate(nullptr, SIG_DFL);
        ctx.enter(Event::subsystem_prepare);
        stats_->start(config_->context().stats);
        solve_->prepareEnum(ctx, enumMode, en);
        ctx.endInit();
    }
    if (prepared()) {
        return true;
    }
    ctx.report(Prepare{*this});
    ctx.enter(Event::subsystem_prepare);
    if (not config_->prepared) {
        init(*config_);
    }
    if (auto* prg = program(); prg && prg->endProgram()) {
        assume_.clear();
        prg->getAssumptions(assume_);
        prg->getWeakBounds(en.optBound);
    }
    if (config_->onlyPre) {
        return false;
    }
    stats_->start(config_->context().stats);
    for (auto* init : propagators_) { cast(init)->init(); }
    if (auto mini = ctx.ok() && en.optMode != MinimizeMode::ignore ? ctx.minimize() : nullptr; mini) {
        if (not mini->setMode(en.optMode, en.optBound)) {
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
    return true;
}

auto ClaspFacade::solve(SolveMode p, LitView a, EventHandler* eh) -> SolveHandle {
    POTASSCO_CHECK_PRE(prepare(), "Solving is not enabled");
    if (stats_) {
        stats_->freeze();
    }
    solve_->active = SolveStrategy::create(p, *this, *solve_->algo.get());
    solve_->active->start(eh, a);
    return SolveHandle(solve_->active);
}
auto ClaspFacade::solve(LitView a, EventHandler* handler) -> Result { return solve(SolveMode::def, a, handler).get(); }

bool ClaspFacade::update(void (*sigAct)(int)) {
    doUpdate(program(), sigAct);
    return ok();
}

void ClaspFacade::doUpdate(ProgramBuilder* p, void (*sigAct)(int)) {
    POTASSCO_CHECK_PRE(config_ && not solving(), "Program updates not supported!");
    POTASSCO_CHECK_PRE(not prepared() || ctx.solveMode() == SharedContext::solve_multi,
                       "Program updates not supported: context is frozen!");
    POTASSCO_CHECK_PRE(not p || not p->frozen() || incremental(), "Program updates not supported: not incremental!");
    if (not config_->prepared) {
        init(*config_);
    }
    if (solved()) {
        startStep(static_cast<uint32_t>(step()) + 1u);
    }
    if (p && p->frozen()) {
        p->updateProgram();
        if (not p->frozen()) {
            ctx.enter(Event::subsystem_load);
        }
    }
    if (ctx.frozen()) {
        ctx.unfreeze();
    }
    if (prepared()) {
        solve_->reset();
        for (auto* init : propagators_) { cast(init)->unfreeze(); }
    }
    int sig = sigAct == SIG_DFL ? 0 : solve_->qSig.exchange(0);
    if (sig && sigAct != SIG_IGN) {
        sigAct(sig);
    }
}
bool ClaspFacade::onUnsat(const Solver& s, const Model& m) { return solve_->onUnsat(s, m); }
bool ClaspFacade::onModel(const Solver& s, const Model& m) {
    step_.unsatTime = RealTime::getTime();
    if (++step_.numEnum == 1) {
        step_.satTime = RealTime::diffTime(step_.unsatTime, step_.solveTime);
    }
    if (m.opt) {
        ++step_.numOptimal;
    }
    return solve_->onModel(s, m);
}
auto ClaspFacade::enumerator() const -> Enumerator* { return solve_.get() ? solve_->enumerator() : nullptr; }
auto ClaspFacade::getStats() const -> Potassco::AbstractStatistics* {
    POTASSCO_CHECK_PRE(stats_.get() && not solving(), "Statistics not (yet) available");
    return stats_->getClingo();
}
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspFacade::Summary
/////////////////////////////////////////////////////////////////////////////////////////
void ClaspFacade::Summary::init(const ClaspFacade& f) {
    std::memset(this, 0, sizeof(Summary));
    facade = &f;
}
auto ClaspFacade::Summary::model() const -> const Model* {
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
auto ClaspFacade::Summary::unsatCore() const -> LitView {
    return facade->solve_ ? facade->solve_->unsatCore() : LitView{};
}
auto ClaspFacade::Summary::lpStep() const -> const Asp::LpStats* {
    auto* p = facade->asp();
    return p ? &p->stats : nullptr;
}
auto ClaspFacade::Summary::lpStats() const -> const Asp::LpStats* {
    return facade->stats_.get() ? facade->stats_->lp() : lpStep();
}
auto ClaspFacade::Summary::consequences() const -> const char* {
    const auto* m = model();
    return m && m->consequences() ? modelType(*m) : nullptr;
}

bool ClaspFacade::Summary::hasCosts() const { return model() && model()->hasCosts(); }
bool ClaspFacade::Summary::hasLower() const { return not facade->lower_.empty(); }
auto ClaspFacade::Summary::lower() const -> SumView { return facade->lower_; }
void ClaspFacade::Summary::accept(StatsVisitor& out) const {
    if (facade->solved()) {
        facade->stats_->accept(out, this == facade->accu_.get());
    }
}

} // namespace Clasp
