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
#include <clasp/solve_algorithms.h>

#include <clasp/enumerator.h>
#include <clasp/solver.h>
#include <clasp/util/timer.h>

#include <potassco/error.h>

#include <memory>

namespace Clasp {
/////////////////////////////////////////////////////////////////////////////////////////
// Basic solve
/////////////////////////////////////////////////////////////////////////////////////////
struct BasicSolve::State {
    using EventType = BasicSolveEvent;
    using BlockPtr  = std::unique_ptr<BlockLimit>;
    using DynPtr    = std::unique_ptr<DynamicLimit>;
    State(Solver& s, const SolveParams& p);
    Val_t            solve(Solver& s, const SolveParams& p, SolveLimits& lim);
    uint64_t         dbGrowNext;
    double           dbMax;
    double           dbHigh;
    ScheduleStrategy dbRed;
    BlockPtr         rsBlock;
    DynPtr           dynRestart;
    uint32_t         nRestart{0};
    uint32_t         nGrow{0};
    uint32_t         dbRedInit;
    uint32_t         dbPinned{0};
    uint32_t         rsShuffle;
    bool             resetState{false};
};

BasicSolve::BasicSolve(Solver& s, const SolveLimits& lim) : BasicSolve(s, s.searchConfig(), lim) {}
BasicSolve::BasicSolve(Solver& s, const SolveParams& p, const SolveLimits& lim)
    : solver_(&s)
    , params_(&p)
    , limits_(lim) {}

BasicSolve::~BasicSolve() = default;
void BasicSolve::reset() { state_.reset(); }
void BasicSolve::reset(Solver& s, const SolveParams& p, const SolveLimits& lim) {
    solver_ = &s;
    params_ = &p;
    limits_ = lim;
    reset();
}

Val_t BasicSolve::solve() {
    if (limits_.reached()) {
        return value_free;
    }
    if (not state_ && not params_->randomize(*solver_)) {
        return value_false;
    }
    if (not state_) {
        state_ = std::make_unique<State>(*solver_, *params_);
    }
    return state_->solve(*solver_, *params_, limits_);
}

bool BasicSolve::satisfiable(LitView path, bool init) const {
    if (not solver_->clearAssumptions() || not solver_->pushRoot(path)) {
        return false;
    }
    if (init && not params_->randomize(*solver_)) {
        return false;
    }
    State       temp(*solver_, *params_);
    SolveLimits limits;
    return temp.solve(*solver_, *params_, limits) == value_true;
}

bool BasicSolve::assume(LitView assumptions) { return solver_->pushRoot(assumptions); }

BasicSolve::State::State(Solver& s, const SolveParams& p)
    : dbGrowNext(p.reduce.growSched.current())
    , dbRed(p.reduce.cflSched)
    , dbRedInit(p.reduce.cflInit(*s.sharedContext()))
    , rsShuffle(p.restart.shuffle) {
    auto dbLim = p.reduce.sizeInit(*s.sharedContext());
    dbMax      = dbLim.lo;
    dbHigh     = dbLim.hi;
    if (dbLim.lo < s.numLearntConstraints()) {
        dbMax = std::min(dbHigh, static_cast<double>(s.numLearntConstraints() + p.reduce.initRange.lo));
    }
    if (dbRedInit && dbRed.type != ScheduleStrategy::sched_luby) {
        if (dbRedInit < dbRed.base) {
            dbRedInit = std::min(dbRed.base, std::max(dbRedInit, 5000u));
            if (dbRedInit != dbRed.base) {
                dbRed.grow = std::min(dbRed.grow, static_cast<float>(dbRedInit) / 2.0f);
                dbRed.base = dbRedInit;
            }
        }
        dbRedInit = 0;
    }
    if (p.restart.rsSched.isDynamic()) {
        const RestartSchedule& r = p.restart.rsSched;
        dynRestart = std::make_unique<DynamicLimit>(r.k(), r.base, r.fastAvg(), r.keepAvg(), r.slowAvg(), r.slowWin(),
                                                    r.adjustLim());
    }
    if (p.restart.block.fscale > 0 && p.restart.block.window > 0) {
        const RestartParams::Block& block = p.restart.block;
        rsBlock = std::make_unique<BlockLimit>(block.window, block.scale(), static_cast<MovingAvg::Type>(block.avg));
        rsBlock->inc  = std::max(p.restart.base(), 50u);
        rsBlock->next = std::max(block.window, block.first);
    }
    s.stats.lastRestart = s.stats.analyzed;
}

Val_t BasicSolve::State::solve(Solver& s, const SolveParams& p, SolveLimits& lim) {
    assert(not lim.reached());
    const uint32_t resetMode = value_false | (s.strategies().resetOnModel ? value_true : 0u);
    if (s.hasConflict() && s.decisionLevel() == s.rootLevel()) {
        resetState = resetState || Potassco::test_any(resetMode, value_false);
        return value_false;
    }
    struct ConflictLimits {
        [[nodiscard]] uint64_t min() const { return std::min({reduce, grow, restart, global}); }
        void                   update(uint64_t x) {
            reduce  -= x;
            grow    -= x;
            restart -= x;
            global  -= x;
        }
        uint64_t reduce;  // current reduce limit
        uint64_t grow;    // current limit for next growth operation
        uint64_t restart; // current restart limit
        uint64_t global;  // current global limit
    };
    if (resetState) {
        this->~State();
        new (this) State(s, p);
    }
    SearchLimits     sLimit;
    RestartSchedule  rs          = p.restart.rsSched;
    ScheduleStrategy dbGrow      = p.reduce.growSched;
    Solver::DBInfo   db          = {0, 0, dbPinned};
    auto             result      = value_free;
    ConflictLimits   cLimit      = {dbRed.current() + dbRedInit, dbGrowNext, UINT64_MAX, lim.conflicts};
    uint64_t         limRestarts = lim.restarts;
    if (not dbGrow.disabled()) {
        dbGrow.advanceTo(nGrow);
    }
    if (nRestart == UINT32_MAX && p.restart.update() == RestartParams::seq_disable) {
        sLimit = SearchLimits();
    }
    else if (rs.isDynamic() && dynRestart.get()) {
        if (not nRestart) {
            dynRestart->resetAdjust(rs.k(), DynamicLimit::lbd_limit, rs.adjustLim(), true);
        }
        sLimit.restart.dynamic = dynRestart.get();
        sLimit.restart.conflicts =
            dynRestart->adjust.limit - std::min(dynRestart->adjust.samples, dynRestart->adjust.limit - 1);
    }
    else {
        rs.advanceTo(not rs.disabled() ? nRestart : 0);
        sLimit.restart.conflicts = rs.current();
    }
    sLimit.restart.local = p.restart.local();
    sLimit.restart.block = rsBlock.get();
    if (p.reduce.memMax) {
        sLimit.memory = static_cast<uint64_t>(p.reduce.memMax) << 20;
    }
    for (EventType progress(s, EventType::event_restart, 0, 0); cLimit.global;) {
        cLimit.restart   = not p.restart.local() ? sLimit.restart.conflicts : UINT64_MAX;
        sLimit.used      = 0;
        sLimit.learnts   = static_cast<uint32_t>(std::min(dbMax + (db.pinned * p.reduce.strategy.noGlue), dbHigh));
        sLimit.conflicts = cLimit.min();
        assert(sLimit.conflicts);
        progress.cLimit = sLimit.conflicts;
        progress.lLimit = sLimit.learnts;
        if (progress.op) {
            s.sharedContext()->report(progress);
            progress.op = EventType::event_none;
        }
        result = s.search(sLimit, p.randProb);
        auto n = std::min(sLimit.used, sLimit.conflicts); // number of conflicts in this iteration
        cLimit.update(n);
        if (result != value_free) {
            progress.op = EventType::event_exit;
            if (result == value_true && p.restart.update() != RestartParams::seq_continue) {
                if (p.restart.update() == RestartParams::seq_repeat) {
                    nRestart = 0;
                }
                else if (p.restart.update() == RestartParams::seq_disable) {
                    nRestart = UINT32_MAX;
                }
            }
            if (not dbGrow.disabled()) {
                dbGrowNext = std::max(cLimit.grow, static_cast<uint64_t>(1));
            }
            s.sharedContext()->report(progress);
            break;
        }
        if (s.restartReached(sLimit)) {
            // restart reached - do restart
            ++nRestart;
            if (p.restart.counterRestart && (nRestart % p.restart.counterRestart) == 0) {
                s.counterBumpVars(p.restart.counterBump);
            }
            if (sLimit.restart.dynamic) {
                n                        = sLimit.restart.dynamic->runLen();
                sLimit.restart.conflicts = sLimit.restart.dynamic->restart(rs.lbdLim(), rs.k());
            }
            else {
                sLimit.restart.conflicts = n = rs.next();
            }
            s.restart();
            if (p.reduce.strategy.fRestart) {
                db = s.reduceLearnts(p.reduce.fRestart(), p.reduce.strategy);
            }
            if (nRestart == rsShuffle) {
                rsShuffle += p.restart.shuffleNext;
                s.shuffleOnNextSimplify();
            }
            if (--limRestarts == 0) {
                break;
            }
            s.stats.lastRestart = s.stats.analyzed;
            progress.op         = EventType::event_restart;
        }
        else if (not p.restart.local()) {
            sLimit.restart.conflicts -= std::min(n, sLimit.restart.conflicts);
        }
        if (cLimit.reduce == 0 || s.reduceReached(sLimit)) {
            // reduction reached - remove learnt constraints
            db            = s.reduceLearnts(p.reduce.fReduce(), p.reduce.strategy);
            cLimit.reduce = dbRedInit + (cLimit.reduce == 0 ? dbRed.next() : dbRed.current());
            progress.op   = std::max(progress.op, static_cast<uint32_t>(EventType::event_deletion));
            if (s.reduceReached(sLimit) || db.pinned >= dbMax) {
                ReduceStrategy t;
                t.algo     = 2;
                t.score    = 2;
                t.glue     = 0;
                db.pinned /= 2;
                db.size    = s.reduceLearnts(0.5f, t).size;
                if (db.size >= sLimit.learnts) {
                    dbMax = std::min(dbMax + std::max(100.0, s.numLearntConstraints() / 10.0), dbHigh);
                }
            }
        }
        if (cLimit.grow == 0 || (dbGrow.defaulted() && progress.op == EventType::event_restart)) {
            // grow sched reached - increase max db size
            if (cLimit.grow == 0) {
                cLimit.grow = n = dbGrow.next();
                ++nGrow;
            }
            if ((s.numLearntConstraints() + n) > static_cast<uint64_t>(dbMax)) {
                dbMax       *= p.reduce.fGrow;
                progress.op  = std::max(progress.op, static_cast<uint32_t>(EventType::event_grow));
            }
            if (dbMax > dbHigh) {
                dbMax       = dbHigh;
                cLimit.grow = UINT64_MAX;
                dbGrow      = ScheduleStrategy::none();
            }
        }
    }
    dbPinned            = db.pinned;
    resetState          = Potassco::test_any(resetMode, result);
    s.stats.lastRestart = s.stats.analyzed - s.stats.lastRestart;
    if (lim.enabled()) {
        if (lim.conflicts != UINT64_MAX) {
            lim.conflicts = cLimit.global;
        }
        if (lim.restarts != UINT64_MAX) {
            lim.restarts = limRestarts;
        }
    }
    return result;
}
/////////////////////////////////////////////////////////////////////////////////////////
// Path
/////////////////////////////////////////////////////////////////////////////////////////
SolveAlgorithm::Path SolveAlgorithm::Path::acquire(LitView path) {
    auto p = std::make_unique<Literal[]>(path.size());
    std::ranges::copy(path, p.get());
    Ptr fp(p.release());
    fp.set<0>();
    return {fp, path.size()};
}
SolveAlgorithm::Path SolveAlgorithm::Path::borrow(LitView path) { return {Ptr(path.data()), path.size()}; }
SolveAlgorithm::Path::~Path() {
    if (owner()) {
        delete[] lits_.get();
    }
}
SolveAlgorithm::Path::Path(Path&& other) noexcept
    : lits_(std::exchange(other.lits_, {}))
    , size_(std::exchange(other.size_, 0)) {}
SolveAlgorithm::Path& SolveAlgorithm::Path::operator=(Path&& other) noexcept {
    if (this != &other) {
        Path t(std::move(*this));
        lits_ = std::exchange(other.lits_, {});
        size_ = std::exchange(other.size_, 0);
    }
    return *this;
}
/////////////////////////////////////////////////////////////////////////////////////////
// SolveAlgorithm
/////////////////////////////////////////////////////////////////////////////////////////
static constexpr auto value_stop = static_cast<Val_t>(value_false | value_true);
SolveAlgorithm::SolveAlgorithm(const SolveLimits& limit)
    : limits_(limit)
    , ctx_(nullptr)
    , enum_(nullptr)
    , onModel_(nullptr)
    , enumLimit_(UINT64_MAX)
    , time_(0.0)
    , last_(value_free)
    , reportM_(true) {}
SolveAlgorithm::~SolveAlgorithm() = default;
void SolveAlgorithm::setOptLimit(SumView bound) { optLimit_.assign(bound.data(), bound.data() + bound.size()); }
auto SolveAlgorithm::model() const -> const Model& {
    POTASSCO_CHECK_PRE(enum_, "SolveAlgorithm is not active!");
    return enum_->lastModel();
}
auto SolveAlgorithm::unsatCore() const -> LitView { return core_; }
bool SolveAlgorithm::interrupt() { return doInterrupt(); }
bool SolveAlgorithm::attach(Enumerator& en, SharedContext& ctx, ModelHandler* onModel) {
    POTASSCO_CHECK_PRE(not ctx_, "SolveAlgorithm is already running!");
    if (not ctx.frozen()) {
        ctx.endInit();
    }
    ctx.report(Event::subsystem_solve);
    if (ctx.master()->hasConflict() || not limits_.conflicts || interrupted()) {
        last_ = not ctx.ok() ? value_false : value_free;
        return false;
    }
    ctx_     = &ctx;
    enum_    = &en;
    time_    = ThreadTime::getTime();
    onModel_ = onModel;
    last_    = value_free;
    path_    = {};
    discardVec(core_);
    return true;
}
void SolveAlgorithm::detach() {
    if (ctx_) {
        if (enum_->enumerated() == 0 && not interrupted()) {
            Solver* s    = ctx_->master();
            Literal step = ctx_->stepLiteral();
            s->popRootLevel(s->rootLevel());
            core_.clear();
            for (auto lit : path_) {
                if (s->isTrue(lit) || lit == step) {
                    continue;
                }
                if (not s->isTrue(step) && not s->pushRoot(step)) {
                    break;
                }
                core_.push_back(lit);
                if (not s->pushRoot(lit)) {
                    if (not s->isFalse(lit)) {
                        core_.clear();
                        s->resolveToCore(core_);
                        if (not core_.empty() && core_.front() == step) {
                            core_.front() = core_.back();
                            core_.pop_back();
                        }
                    }
                    break;
                }
            }
            s->popRootLevel(s->rootLevel());
        }
        doDetach();
        ctx_->master()->stats.addCpuTime(ThreadTime::getTime() - time_);
        onModel_ = nullptr;
        ctx_     = nullptr;
        path_    = {};
    }
}
bool SolveAlgorithm::hasLimit(const Model& m) const {
    if (not enum_->tentative() && m.num >= enumLimit_) {
        return true;
    }
    if (enum_->optimize() && m.hasCosts() && not optLimit_.empty()) {
        for (auto i : irange(std::min(size32(optLimit_), size32(m.costs)))) {
            if (optLimit_[i] != m.costs[i]) {
                return m.costs[i] < optLimit_[i];
            }
        }
        return true;
    }
    return false;
}
bool SolveAlgorithm::solve(Enumerator& en, SharedContext& ctx, LitView assume, ModelHandler* onModel) {
    POTASSCO_SCOPE_EXIT({ detach(); });
    if (not attach(en, ctx, onModel)) {
        return last_ != value_false;
    }
    if (maxModels() != UINT64_MAX) {
        if (en.optimize() && not en.tentative()) {
            ctx.warn("#models not 0: optimality of last model not guaranteed.");
        }
        if (en.lastModel().consequences()) {
            ctx.warn("#models not 0: last model may not cover consequences.");
        }
    }
    return doSolve(ctx, path_ = Path::borrow(assume));
}

void SolveAlgorithm::start(Enumerator& en, SharedContext& ctx, LitView assume, ModelHandler* onModel) {
    if (attach(en, ctx, onModel)) {
        doStart(ctx, path_ = Path::acquire(assume));
    }
}
bool SolveAlgorithm::next() {
    if (not ctx_) {
        return false;
    }
    if (last_ != value_stop && (last_ != value_true || not enum_->commitSymmetric(*ctx_->solver(model().sId)))) {
        last_ = doNext(last_);
    }
    if (last_ == value_true) {
        if (not reportModel(*ctx_->solver(model().sId), false)) {
            last_ = value_stop;
        }
        return true;
    }
    stop();
    return false;
}
bool SolveAlgorithm::more() const { return last_ != value_false; }
void SolveAlgorithm::stop() {
    if (ctx_) {
        doStop();
        detach();
    }
}
bool SolveAlgorithm::reportModel(Solver& s, bool sym) const {
    for (const auto& m = model();;) {
        bool r1 = not onModel_ || onModel_->onModel(s, m);
        bool r2 = not reportM_ || s.sharedContext()->report(s, m);
        if (not r1 || not r2 || hasLimit(m) || interrupted()) {
            return false;
        }
        if (not sym || not enum_->commitSymmetric(s)) {
            return true;
        }
    }
}

bool SolveAlgorithm::reportModel(Solver& s) const { return reportModel(s, true); }
bool SolveAlgorithm::reportUnsat(Solver& s) const {
    const auto& m  = model();
    auto*       h  = s.sharedContext()->eventHandler();
    bool        r1 = not onModel_ || onModel_->onUnsat(s, m);
    bool        r2 = not h || h->onUnsat(s, m);
    enum_->clearUpdate();
    return r1 && r2;
}
bool SolveAlgorithm::moreModels(const Solver& s) const {
    return s.decisionLevel() > 0 ||
           (not s.sharedContext()->preserveModels() && s.sharedContext()->numEliminatedVars()) ||
           (enum_ && enum_->hasSymmetric(s));
}
void SolveAlgorithm::doStart(SharedContext&, LitView) {
    POTASSCO_CHECK_PRE(false, "Iterative model generation not supported by this algorithm!");
}
Val_t SolveAlgorithm::doNext(Val_t) {
    POTASSCO_CHECK_PRE(false, "Iterative model generation not supported by this algorithm!");
}
void SolveAlgorithm::doStop() {}
/////////////////////////////////////////////////////////////////////////////////////////
// SequentialSolve
/////////////////////////////////////////////////////////////////////////////////////////
namespace {
struct InterruptHandler final : MessageHandler {
    InterruptHandler(Solver* s, volatile int* t) : solver(s), term(t) {
        if (s && t) {
            s->addPost(this);
        }
    }
    ~InterruptHandler() override {
        if (solver) {
            solver->removePost(this);
            solver = nullptr;
        }
    }
    bool          handleMessages() override { return !*term || (solver->setStopConflict(), false); }
    bool          propagateFixpoint(Solver&, PostPropagator*) override { return InterruptHandler::handleMessages(); }
    Solver*       solver;
    volatile int* term;
};
} // namespace
SequentialSolve::SequentialSolve(const SolveLimits& limit) : SolveAlgorithm(limit), solve_(nullptr), term_(-1) {}
void SequentialSolve::resetSolve() {
    if (term_ > 0) {
        term_ = 0;
    }
}
bool SequentialSolve::doInterrupt() {
    if (term_ >= 0) {
        term_ |= 1;
        return true;
    }
    return false;
}
void SequentialSolve::enableInterrupts() {
    if (term_ < 0) {
        term_ = 0;
    }
}
bool SequentialSolve::interrupted() const { return term_ > 0; }
void SequentialSolve::doStart(SharedContext& ctx, LitView assume) {
    solve_ = std::make_unique<BasicSolve>(*ctx.master(), ctx.configuration()->search(0), limits());
    if (not enumerator().start(solve_->solver(), assume)) {
        SequentialSolve::doStop();
    }
}
Val_t SequentialSolve::doNext(Val_t last) {
    if (interrupted() || not solve_.get()) {
        return solve_.get() ? value_free : value_false;
    }
    Solver& s = solve_->solver();
    for (InterruptHandler term(term_ >= 0 ? &s : static_cast<Solver*>(nullptr), &term_);;) {
        if (last != value_free) {
            enumerator().update(s);
        }
        last = solve_->solve();
        if (last != value_true) {
            if (last == value_free || term_ > 0) {
                return value_free;
            }
            if (enumerator().commitUnsat(s)) {
                reportUnsat(s);
            }
            else if (enumerator().commitComplete() || not restart(s, path())) {
                break;
            }
            else {
                last = value_free;
            }
        }
        else if (enumerator().commitModel(s)) {
            break;
        }
    }
    return last;
}
void SequentialSolve::doStop() {
    if (solve_.get()) {
        enumerator().end(solve_->solver());
        solve_.reset();
    }
}
void SequentialSolve::doDetach() { ctx().detach(*ctx().master()); }

bool SequentialSolve::doSolve(SharedContext& ctx, LitView assume) {
    // Add assumptions - if this fails, the problem is unsat
    // under the current assumptions but not necessarily unsat.
    Solver&          s    = *ctx.master();
    bool             more = not interrupted() && ctx.attach(s) && enumerator().start(s, assume);
    InterruptHandler term(term_ >= 0 ? &s : static_cast<Solver*>(nullptr), &term_);
    for (BasicSolve solve(s, ctx.configuration()->search(0), limits()); more;) {
        Val_t res;
        while ((res = solve.solve()) == value_true && (not enumerator().commitModel(s) || reportModel(s))) {
            enumerator().update(s);
        }
        if (res != value_false) {
            more = res == value_free || moreModels(s);
            break;
        }
        if (interrupted()) {
            more = true;
            break;
        }
        if (enumerator().commitUnsat(s)) {
            reportUnsat(s);
            enumerator().update(s);
        }
        else if (enumerator().commitComplete()) {
            more = false;
            break;
        }
        else {
            more = restart(s, assume);
        }
    }
    enumerator().end(s);
    return more;
}
bool SequentialSolve::restart(Solver& s, LitView assume) {
    enumerator().end(s);
    return enumerator().start(s, assume);
}

} // namespace Clasp
