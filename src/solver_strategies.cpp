//
// Copyright (c) 2014-present Benjamin Kaufmann
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
#include <clasp/solver_strategies.h>

#include <clasp/heuristics.h>
#include <clasp/lookahead.h>
#include <clasp/solver.h>

#include <potassco/error.h>

#include <cmath>

namespace Clasp {
static_assert(sizeof(ReduceStrategy) == sizeof(uint32_t), "invalid bitset");
/////////////////////////////////////////////////////////////////////////////////////////
// SolverStrategies / SolverParams
/////////////////////////////////////////////////////////////////////////////////////////
void SolverStrategies::prepare() {
    static_assert(sizeof(SolverStrategies) == sizeof(uint64_t), "Unsupported Padding");
    if (search == no_learning) {
        compress     = 0;
        saveProgress = 0;
        reverseArcs  = 0;
        otfs         = 0;
        updateLbd    = 0;
        ccMinAntes   = no_antes;
        bumpVarAct   = 0;
    }
}

uint32_t SolverParams::prepare() {
    struct X {
        uint32_t strat[2];
        uint32_t self[5];
    };
    static_assert(sizeof(SolverParams) == sizeof(X), "Unsupported Padding");
    uint32_t res = 0;
    if (search == no_learning && isLookbackHeuristic(heuId)) {
        heuId  = +HeuristicType::none;
        res   |= 1;
    }
    if (heuId == HeuristicType::unit) {
        if (not Lookahead::isType(lookType)) {
            res      |= 2;
            lookType  = +VarType::atom;
        }
        lookOps = 0;
    }
    if (heuId != HeuristicType::domain && (heuristic.domPref || heuristic.domMod)) {
        res               |= 4;
        heuristic.domPref  = 0;
        heuristic.domMod   = 0;
    }
    SolverStrategies::prepare();
    return res;
}
bool SolverParams::addPropagator(Solver& s) const {
    if (Lookahead::isType(lookType)) {
        if (auto* pp = s.getPost<Lookahead>()) {
            pp->destroy(&s, true);
        }
        Lookahead::Params p(static_cast<VarType>(lookType));
        p.nant(heuristic.nant != 0);
        p.limit(lookOps);
        if (not s.addPost(new Lookahead(p))) {
            return false;
        }
    }
    return true;
}
auto SolverParams::createHeuristic(const HeuristicFactory& creator) const -> std::unique_ptr<DecisionHeuristic> {
    auto hId = static_cast<HeuristicType>(heuId);
    if (hId == HeuristicType::def && search == SolverStrategies::use_learning) {
        hId = HeuristicType::berkmin;
    }
    POTASSCO_CHECK_PRE(search == SolverStrategies::use_learning || not isLookbackHeuristic(hId),
                       "Selected heuristic requires lookback!");
    auto h = creator ? creator(hId, heuristic) : Clasp::createHeuristic(hId, heuristic);
    if (Lookahead::isType(lookType) && lookOps > 0 && hId != HeuristicType::unit) {
        h = UnitHeuristic::restricted(h.release());
    }
    return h;
}

/////////////////////////////////////////////////////////////////////////////////////////
// ScheduleStrategy
/////////////////////////////////////////////////////////////////////////////////////////
double   growR(uint32_t idx, double g) { return pow(g, (double) idx); }
double   addR(uint32_t idx, double a) { return a * idx; }
uint32_t lubyR(uint32_t idx) {
    uint32_t i = idx + 1;
    while ((i & (i + 1)) != 0) { i -= ((1u << Potassco::log2(i)) - 1); }
    return (i + 1) >> 1;
}
ScheduleStrategy::ScheduleStrategy(Type t, uint32_t b, double up, uint32_t lim)
    : base(b)
    , type(t)
    , idx(0)
    , len(lim)
    , grow(0.0) {
    if (t == sched_geom) {
        grow = static_cast<float>(std::max(1.0, up));
    }
    else if (t == sched_arith) {
        grow = static_cast<float>(std::max(0.0, up));
    }
    else if (t == sched_luby && lim) {
        len = std::max(2u, (static_cast<uint32_t>(std::pow(2.0, std::ceil(std::log2(lim)))) - 1) * 2);
    }
}

static uint64_t saturate(double d) {
    return d < static_cast<double>(UINT64_MAX) ? static_cast<uint64_t>(d) : UINT64_MAX;
}

uint64_t ScheduleStrategy::current() const {
    if (base == 0) {
        return UINT64_MAX;
    }
    switch (type) {
        case sched_geom : return saturate(growR(idx, grow) * base);
        case sched_arith: return static_cast<uint64_t>(addR(idx, grow) + base);
        case sched_luby : return static_cast<uint64_t>(lubyR(idx)) * base;
        default         : return base;
    }
}
uint64_t ScheduleStrategy::next() {
    if (++idx != len) {
        return current();
    }
    // length reached or overflow
    len = (len + !!idx) << static_cast<uint32_t>(type == sched_luby);
    idx = 0;
    return current();
}
void ScheduleStrategy::advanceTo(uint32_t n) {
    if (not len || n < len) {
        idx = n;
        return;
    }
    if (type != sched_luby) {
        double   dLen  = len;
        uint32_t x     = static_cast<uint32_t>(sqrt(dLen * (4.0 * dLen - 4.0) + 8.0 * (n + 1.0)) - 2 * dLen + 1) / 2;
        idx            = n - static_cast<uint32_t>(x * dLen + (x - 1.0) * x / 2.0);
        len           += x;
        return;
    }
    while (n >= len) {
        n   -= len++;
        len *= 2;
    }
    idx = n;
}
RestartSchedule RestartSchedule::dynamic(uint32_t base, float k, uint32_t lim, AvgType fast, Keep keep, AvgType slow,
                                         uint32_t slowW) {
    RestartSchedule sched;
    sched.base = base;
    sched.type = 3u;
    sched.grow = k;
    sched.len  = lim;
    sched.idx  = static_cast<uint32_t>(fast) | (static_cast<uint32_t>(slow) << 3u) | ((keep & 3u) << 6u) |
                (std::min(slowW, (1u << 24) - 1) << 8u);
    return sched;
}
MovingAvg::Type       RestartSchedule::fastAvg() const { return static_cast<MovingAvg::Type>(idx & 7u); }
MovingAvg::Type       RestartSchedule::slowAvg() const { return static_cast<MovingAvg::Type>((idx >> 3u) & 7u); }
RestartSchedule::Keep RestartSchedule::keepAvg() const { return static_cast<Keep>((idx >> 6u) & 3u); }
uint32_t              RestartSchedule::slowWin() const { return idx >> 8u; }
/////////////////////////////////////////////////////////////////////////////////////////
// RestartParams
/////////////////////////////////////////////////////////////////////////////////////////
RestartParams::RestartParams()
    : rsSched()
    , block()
    , counterRestart(0)
    , counterBump(9973)
    , shuffle(0)
    , shuffleNext(0)
    , upRestart(0)
    , cntLocal(0) {
    static_assert(sizeof(RestartParams) == sizeof(ScheduleStrategy) + (3 * sizeof(uint32_t)) + sizeof(float),
                  "Invalid structure alignment");
}
void RestartParams::disable() {
    *this                                   = {};
    static_cast<ScheduleStrategy&>(rsSched) = ScheduleStrategy::none();
}
uint32_t RestartParams::prepare(bool withLookback) {
    if (not withLookback || disabled()) {
        disable();
    }
    return 0;
}
/////////////////////////////////////////////////////////////////////////////////////////
// DynamicLimit
/////////////////////////////////////////////////////////////////////////////////////////
DynamicLimit::Global::Global(MovingAvg::Type type, uint32_t size) : lbd(size, type), cfl(size, type) {}

static uint32_t verifySize(uint32_t size) {
    POTASSCO_CHECK_PRE(size != 0, "size must be > 0");
    return size;
}

DynamicLimit::DynamicLimit(float k, uint32_t size, MovingAvg::Type fast, Keep keep, MovingAvg::Type slow,
                           uint32_t slowSize, uint32_t adjustLimit)
    : global_(slow, slowSize || slow == MovingAvg::avg_sma ? slowSize : 200 * verifySize(size))
    , avg_(verifySize(size), fast)
    , num_(0)
    , keep_(keep) {
    resetAdjust(k, lbd_limit, adjustLimit);
}

void DynamicLimit::resetAdjust(float k, Type type, uint32_t lim, bool resetAvg) {
    adjust = {.limit = lim, .restarts = 0, .samples = 0, .rk = k, .type = type};
    if (resetAvg) {
        num_ = 0;
        avg_.clear();
    }
}
void DynamicLimit::block() { resetRun(Keep::keep_block); }

void DynamicLimit::resetRun(Keep k) {
    num_ = 0;
    if ((keep_ & k) == 0) {
        avg_.clear();
    }
}
void DynamicLimit::reset() {
    global_.reset();
    resetRun(Keep::keep_never);
}
void DynamicLimit::update(uint32_t dl, uint32_t lbd) {
    // update global avg
    ++adjust.samples;
    global_.cfl.push(dl);
    global_.lbd.push(lbd);
    // update moving avg
    ++num_;
    uint32_t v = adjust.type == lbd_limit ? lbd : dl;
    avg_.push(v);
}
uint32_t DynamicLimit::restart(uint32_t maxLbd, float k) {
    ++adjust.restarts;
    if (adjust.limit != UINT32_MAX && adjust.samples >= adjust.limit) {
        Type     nt   = maxLbd && global_.avg(lbd_limit) > maxLbd ? level_limit : lbd_limit;
        float    rk   = adjust.rk;
        uint32_t uLim = adjust.limit;
        if (nt == adjust.type) {
            double rLen = adjust.avgRestart();
            bool   sx   = num_ >= adjust.limit;
            if (rLen >= 16000.0) {
                rk   += 0.1f;
                uLim  = 16000;
            }
            else if (sx) {
                rk   += 0.05f;
                uLim  = std::max(16000u, uLim - 10000);
            }
            else if (rLen >= 4000.0) {
                rk += 0.05f;
            }
            else if (rLen >= 1000.0) {
                uLim += 10000u;
            }
            else if (rk > k) {
                rk -= 0.05f;
            }
        }
        resetAdjust(rk, nt, uLim);
    }
    resetRun(Keep::keep_restart);
    return adjust.limit;
}
BlockLimit::BlockLimit(uint32_t windowSize, double rf, MovingAvg::Type at)
    : avg(windowSize, at)
    , next(windowSize)
    , n(0)
    , inc(50)
    , r(static_cast<float>(rf)) {
    static_assert(sizeof(BlockLimit) == 12 * sizeof(uint32_t), "unexpected size");
}
/////////////////////////////////////////////////////////////////////////////////////////
// ReduceParams
/////////////////////////////////////////////////////////////////////////////////////////
uint32_t ReduceParams::getLimit(uint32_t base, double f, const Range32& r) {
    base = (f != 0.0 ? static_cast<uint32_t>(std::min(base * f, static_cast<double>(UINT32_MAX))) : UINT32_MAX);
    return r.clamp(base);
}
uint32_t ReduceParams::getBase(const SharedContext& ctx) const {
    uint32_t st = strategy.estimate != ReduceStrategy::est_dynamic || ctx.isExtended()
                      ? strategy.estimate
                      : static_cast<uint32_t>(ReduceStrategy::est_num_constraints);
    switch (st) {
        default:
        case ReduceStrategy::est_dynamic: {
            uint32_t mi = std::min(ctx.stats().vars.num, ctx.stats().numConstraints());
            uint32_t ma = std::max(ctx.stats().vars.num, ctx.stats().numConstraints());
            return ma > (mi * 10) ? ma : mi;
        }
        case ReduceStrategy::est_con_complexity : return ctx.stats().complexity;
        case ReduceStrategy::est_num_constraints: return ctx.stats().numConstraints();
        case ReduceStrategy::est_num_vars       : return ctx.stats().vars.num;
    }
}
void ReduceParams::disable() {
    cflSched         = ScheduleStrategy::none();
    growSched        = ScheduleStrategy::none();
    strategy.fReduce = 0;
    fGrow            = 0.0f;
    fInit            = 0.0f;
    fMax             = 0.0f;
    initRange        = Range32(UINT32_MAX, UINT32_MAX);
    maxRange         = UINT32_MAX;
    memMax           = 0;
}
Range32 ReduceParams::sizeInit(const SharedContext& ctx) const {
    if (not growSched.disabled() || growSched.defaulted()) {
        uint32_t base = getBase(ctx);
        uint32_t lo   = std::min(getLimit(base, fInit, initRange), maxRange);
        uint32_t hi   = getLimit(base, fMax, Range32(lo, maxRange));
        return {lo, hi};
    }
    return {maxRange, maxRange};
}
uint32_t ReduceParams::cflInit(const SharedContext& ctx) const {
    return cflSched.disabled() ? 0 : getLimit(getBase(ctx), fInit, initRange);
}
uint32_t ReduceParams::prepare(bool withLookback) {
    if (not withLookback || fReduce() == 0.0f) {
        disable();
        return 0;
    }
    if (cflSched.defaulted() && growSched.disabled() && not growSched.defaulted()) {
        cflSched = ScheduleStrategy::arith(4000, 600);
    }
    if (fMax != 0.0f) {
        fMax = std::max(fMax, fInit);
    }
    return 0;
}
/////////////////////////////////////////////////////////////////////////////////////////
// SolveParams
/////////////////////////////////////////////////////////////////////////////////////////
SolveParams::SolveParams() : randRuns(0u), randConf(0u), randProb(0.0f) {}
uint32_t SolveParams::prepare(bool withLookback) {
    return restart.prepare(withLookback) | reduce.prepare(withLookback);
}
bool SolveParams::randomize(Solver& s) const {
    for (uint32_t r = 0, c = randConf; r != randRuns && c; ++r) {
        if (s.search(c, UINT32_MAX, false, 1.0) != value_free) {
            return not s.hasConflict();
        }
        s.undoUntil(0);
    }
    return true;
}
/////////////////////////////////////////////////////////////////////////////////////////
// Configurations
/////////////////////////////////////////////////////////////////////////////////////////
Configuration::~Configuration() = default;
Configuration* Configuration::config(const char* n) {
    return not n || !*n || ((*n == '.' || *n == '/') && not n[1]) ? this : nullptr;
}
bool UserConfiguration::addPost(Solver& s) const { return solver(s.id()).addPropagator(s); }

BasicSatConfig::BasicSatConfig() {
    solver_.push_back(SolverParams());
    search_.push_back(SolveParams());
}
void BasicSatConfig::prepare(SharedContext& ctx) {
    uint32_t warn = 0;
    for (uint32_t i = 0, end = size32(solver_), mod = size32(search_); i != end; ++i) {
        warn |= solver_[i].prepare();
        warn |= search_[i % mod].prepare(solver_[i].search != SolverStrategies::no_learning);
        if (solver_[i].updateLbd == SolverStrategies::lbd_fixed && search_[i % mod].reduce.strategy.protect) {
            warn |= 8;
        }
    }
    if ((warn & 1) != 0) {
        ctx.warn("Selected heuristic requires lookback strategy!");
    }
    if ((warn & 2) != 0) {
        ctx.warn("Heuristic 'Unit' implies lookahead. Using 'atom'.");
    }
    if ((warn & 4) != 0) {
        ctx.warn("Domain options require heuristic 'Domain'!");
    }
    if ((warn & 8) != 0) {
        ctx.warn("Deletion protection requires LBD updates, which are off!");
    }
}
void BasicSatConfig::setHeuristic(Solver& s) const {
    s.setHeuristic(BasicSatConfig::solver(s.id()).createHeuristic(nullptr).release());
}
SolverParams& BasicSatConfig::addSolver(uint32_t i) {
    while (i >= solver_.size()) { solver_.push_back(SolverParams().setId(size32(solver_))); }
    return solver_[i];
}
SolveParams& BasicSatConfig::addSearch(uint32_t i) {
    if (i >= search_.size()) {
        search_.resize(i + 1);
    }
    return search_[i];
}

void BasicSatConfig::reset() {
    static_cast<ContextParams&>(*this) = ContextParams();
    BasicSatConfig::resize(1, 1);
    solver_[0] = SolverParams();
    search_[0] = SolveParams();
}
void BasicSatConfig::resize(uint32_t solver, uint32_t search) {
    solver_.resize(solver);
    search_.resize(search);
}
/////////////////////////////////////////////////////////////////////////////////////////
// Heuristics
/////////////////////////////////////////////////////////////////////////////////////////
auto createHeuristic(HeuristicType type, const HeuParams& p) -> std::unique_ptr<DecisionHeuristic> {
    switch (type) {
        case HeuristicType::berkmin: return std::make_unique<ClaspBerkmin>(p);
        case HeuristicType::vsids  : return std::make_unique<ClaspVsids>(p);
        case HeuristicType::vmtf   : return std::make_unique<ClaspVmtf>(p);
        case HeuristicType::domain : return std::make_unique<DomainHeuristic>(p);
        case HeuristicType::unit   : return std::make_unique<UnitHeuristic>();
        default:
            POTASSCO_CHECK_PRE(type == HeuristicType::def || type == HeuristicType::none, "Unknown heuristic id!");
            return std::make_unique<SelectFirst>();
    }
}
ModelHandler::~ModelHandler() = default;
bool ModelHandler::onUnsat(const Solver&, const Model&) { return true; }
} // namespace Clasp
