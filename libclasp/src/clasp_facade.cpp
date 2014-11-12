// 
// Copyright (c) 2006-2012, Benjamin Kaufmann
// 
// This file is part of Clasp. See http://www.cs.uni-potsdam.de/clasp/ 
// 
// Clasp is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2 of the License, or
// (at your option) any later version.
// 
// Clasp is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
// 
// You should have received a copy of the GNU General Public License
// along with Clasp; if not, write to the Free Software
// Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
//
#include <clasp/clasp_facade.h>
#include <clasp/lookahead.h>
#include <clasp/cb_enumerator.h>
#include <clasp/dependency_graph.h>
#include <clasp/minimize_constraint.h>
#include <clasp/unfounded_check.h>
#include <clasp/util/timer.h>
#include <clasp/util/atomic.h>
#include <cstdio>
#include <cstdlib>
#include <signal.h>
#include <limits>
#if WITH_THREADS
#include <clasp/util/mutex.h>
#endif
namespace Clasp {
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspConfig
/////////////////////////////////////////////////////////////////////////////////////////
ClaspConfig::ClaspConfig() : tester_(0) { }
ClaspConfig::~ClaspConfig() { delete tester_; }
void ClaspConfig::reset() {
	if (tester_) { tester_->reset(); }
	BasicSatConfig::reset();
	solve = SolveOptions();
	asp   = AspOptions();
}
BasicSatConfig* ClaspConfig::addTesterConfig() {
	if (!tester_) { tester_ = new BasicSatConfig(); }
	return tester_;
}
void ClaspConfig::prepare(SharedContext& ctx) {
	BasicSatConfig::prepare(ctx);
	uint32 numS = solve.numSolver();
	if (numS > solve.supportedSolvers()) {
		ctx.report(warning(Event::subsystem_facade, "Too many solvers."));
		numS = solve.supportedSolvers();
	}
	if (numS > solve.recommendedSolvers()) {
		ctx.report(warning(Event::subsystem_facade, clasp_format_error("Oversubscription: #Threads=%u exceeds logical CPUs=%u.", numS, solve.recommendedSolvers())));
	}
	if (std::abs(solve.numModels) != 1) { satPre.mode = SatPreParams::prepro_preserve_models; }
	solve.setSolvers(numS);
	ctx.setConcurrency(solve.numSolver(), SharedContext::mode_resize);
}
bool ClaspConfig::addPost(Solver& s) const {
	bool ok = true;
	if (s.sharedContext() && s.sharedContext()->sccGraph.get()) {
		DefaultUnfoundedCheck* pp = static_cast<DefaultUnfoundedCheck*>(s.getPost(PostPropagator::priority_reserved_ufs));
		if (pp) { pp->setReasonStrategy(static_cast<DefaultUnfoundedCheck::ReasonStrategy>(solver(s.id()).loopRep)); }
		else    { ok = s.addPost(new DefaultUnfoundedCheck(static_cast<DefaultUnfoundedCheck::ReasonStrategy>(solver(s.id()).loopRep))); }
	}
	return ok && BasicSatConfig::addPost(s);
}
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspFacade::SolveImpl/SolveStrategy/AsyncResult
/////////////////////////////////////////////////////////////////////////////////////////
struct ClaspFacade::SolveStrategy {
public:
	static const int SIGCANCEL = 9;
	enum State { state_start = 0, state_running = 1, state_result = 2, state_model = 3, state_done = 6 };
	SolveStrategy()         { state = signal = 0; algo = 0; handler = 0; }
	virtual ~SolveStrategy(){}
	bool running() const    { return (state & state_running) != 0; }
	bool interrupt(int sig) {
		if (!running()) { return false; }
		if (!signal || sig < signal) { signal = sig; } 
		return cancel(sig);
	}
	void solve(ClaspFacade& f, SolveAlgorithm* algo, EventHandler* h) {
		this->algo    = algo;
		this->handler = h;
		state = signal= 0;
		doSolve(f);
	}
	virtual void release()  {}
	virtual bool cancel(int){ return algo->interrupt(); }
	Clasp::atomic<int> state;
	Clasp::atomic<int> signal;
	SolveAlgorithm*    algo;
	EventHandler*      handler;
protected:
	void solveImpl(ClaspFacade& f, State end);
	virtual void doSolve(ClaspFacade& f) = 0;
};
struct ClaspFacade::SolveImpl {
	typedef SingleOwnerPtr<SolveAlgorithm> AlgoPtr;
	typedef SingleOwnerPtr<Enumerator>     EnumPtr;
	SolveImpl() : en(0), algo(0), active(0) { }
	~SolveImpl() { reset(); }
	void init(SolveAlgorithm* algo, Enumerator* en) {
		this->en   = en;
		this->algo = algo;
		this->algo->setEnumerator(*en);
	}
	void reset() {
		if (active)    { interrupt(SolveStrategy::SIGCANCEL); active->release(); active = 0; }
		if (algo.get()){ algo->resetSolve(); }
		if (en.get())  { en->reset(); }
	}
	void prepare(SharedContext& ctx, SharedMinimizeData* min, int numM) {
		CLASP_FAIL_IF(active, "Solve operation still active");
		int limit = en->init(ctx, min, numM);
		algo->setEnumLimit(limit ? static_cast<uint64>(limit) : UINT64_MAX);
	}
	bool update(const Solver& s, const Model& m) { return !active->handler || active->handler->onModel(s, m); }
	bool interrupt(int sig)                      { return active && active->interrupt(sig); }
	bool                      solving()   const  { return active && active->running();   }
	const Model*              lastModel() const  { return en.get() ? &en->lastModel() : 0; }
	const SharedMinimizeData* minimizer() const  { return en.get() ? en->minimizer() : 0; } 
	Enumerator*               enumerator()const  { return en.get(); }
	int                       modelType() const  { return en.get() ? en->modelType() : 0; }
	EnumPtr        en;
	AlgoPtr        algo;
	SolveStrategy* active;
};
void ClaspFacade::SolveStrategy::solveImpl(ClaspFacade& f, State done) {
	if (state != state_running){ state = state_running; }
	if (f.result().flags)      { state = done; signal = f.result().signal; return; }
	struct OnExit {
		OnExit(SolveStrategy* s, ClaspFacade* x, int st) : self(s), facade(x), endState(st), more(true) {}
		~OnExit() { 
			facade->stopStep(self->signal, !more);
			if (self->handler) { self->handler->onEvent(StepReady(facade->summary())); }
			self->state  = endState;
		}
		SolveStrategy* self;
		ClaspFacade*   facade;
		int            endState;
		bool           more;
	} scope(this, &f, done);
	f.step_.solveTime = f.step_.unsatTime = RealTime::getTime();
	scope.more = algo->solve(f.ctx, f.assume_, &f);
}

#if WITH_THREADS
struct ClaspFacade::AsyncSolve : public SolveStrategy, public EventHandler {
	static EventHandler* asyncModelHandler() { return reinterpret_cast<EventHandler*>(0x1); }
	AsyncSolve() { refs = 1; }
	virtual void doSolve(ClaspFacade& f) {
		if (handler == AsyncSolve::asyncModelHandler()) { handler = this; }
		algo->enableInterrupts();
		state  = state_running;
		result = f.result();
		if (result.flags) { signal = result.signal; state = state_done; return; }
		// start solve in worker thread
		Clasp::thread(std::mem_fun(&AsyncSolve::threadMain), this, &f).swap(task);
	}
	virtual bool cancel(int sig) {
		return SolveStrategy::cancel(sig) && (sig != SIGCANCEL || wait());
	}
	void threadMain(ClaspFacade* f) {
		try         { solveImpl(*f, state_running); }
		catch (...) { result.flags |= Result::EXT_ERROR; }
		{
			unique_lock<Clasp::mutex> lock(this->mqMutex);
			result = f->result();
			state  = state_done;
		}
		mqCond.notify_one();
	}
	virtual void release() {
		if      (--refs == 1) { interrupt(SIGCANCEL); }
		else if (refs   == 0) { join(); delete this; }
	}
	bool hasResult()const { return (state & state_result)  != 0; }
	bool next() {
		if (state != state_model) { return false; }
		unique_lock<Clasp::mutex> lock(mqMutex);
		state = state_running;
		mqCond.notify_one();
		return true;
	}
	bool wait(double s = -1.0) {
		if (state == state_start) { return false; }
		if (signal != 0)          { next(); }
		for (unique_lock<Clasp::mutex> lock(mqMutex); !hasResult(); ) {
			if (s < 0.0) { mqCond.wait(lock); }
			else {
				try { 
					mqCond.wait_for(lock, tbb::tick_count::interval_t(s));
					if (!hasResult()) { return false; }
				}
				catch (const std::runtime_error&) {
					// Due to a bug in the computation of the wait time in some tbb versions 
					// for linux wait_for might fail with eid_condvar_wait_failed.
					// See: http://software.intel.com/en-us/forums/topic/280012
					// Ignore the error and retry the wait - the computed wait time will be valid, eventually.
				}
			}
		}
		if (state == state_done) { join(); }
		return true;
	}
	bool onModel(const Solver&, const Model&) {
		const Result sat = {Result::SAT, 0};
		unique_lock<Clasp::mutex> lock(mqMutex);
		state = state_model;
		result= sat;
		mqCond.notify_one();
		while (state == state_model && signal == 0) { mqCond.wait(lock); }
		return signal == 0;
	}
	void join() { if (task.joinable()) { task.join(); } }
	Clasp::thread             task;   // async solving thread
	Clasp::mutex              mqMutex;// protects mqCond
	Clasp::condition_variable mqCond; // for iterating over models one by one
	Clasp::atomic<int>        refs;   // 1 + #AsyncResult objects
	Result                    result; // result of async operation
};
ClaspFacade::AsyncResult::AsyncResult(SolveImpl& x) : state_(static_cast<AsyncSolve*>(x.active)) { ++state_->refs; }
ClaspFacade::AsyncResult::~AsyncResult() { state_->release(); }
ClaspFacade::AsyncResult::AsyncResult(const AsyncResult& x) : state_(x.state_) { ++state_->refs; }
int  ClaspFacade::AsyncResult::interrupted()        const { return state_->signal; }
bool ClaspFacade::AsyncResult::error()              const { return ready() && state_->result.error(); }
bool ClaspFacade::AsyncResult::ready()              const { return state_->hasResult(); }
bool ClaspFacade::AsyncResult::ready(Result& r)     const { if (ready()) { r = get(); return true; } return false; }
bool ClaspFacade::AsyncResult::running()            const { return state_->running(); }
void ClaspFacade::AsyncResult::wait()               const { state_->wait(-1.0); }
bool ClaspFacade::AsyncResult::waitFor(double sec)  const { return state_->wait(sec); }
void ClaspFacade::AsyncResult::next()               const { state_->next(); }
bool ClaspFacade::AsyncResult::cancel()             const { return state_->interrupt(AsyncSolve::SIGCANCEL); }
ClaspFacade::Result ClaspFacade::AsyncResult::get() const {
	state_->wait();
	if (!state_->result.error()) { return state_->result; }
	throw std::runtime_error("Async operation failed!");
}
bool ClaspFacade::AsyncResult::end() const { 
	// first running() handles case where iterator is outdated (state was reset to start)
	// second running() is used to distinguish models from final result (summary)
	return !running() || !get().sat() || !running();
}
const Model& ClaspFacade::AsyncResult::model() const { 
	CLASP_FAIL_IF(state_->state != AsyncSolve::state_model, "Invalid iterator access!");
	return const_cast<const SolveAlgorithm*>(state_->algo)->enumerator()->lastModel();
}
#endif
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspFacade
/////////////////////////////////////////////////////////////////////////////////////////
ClaspFacade::ClaspFacade() : config_(0) {}
ClaspFacade::~ClaspFacade() { }
void ClaspFacade::discardProblem() {
	config_  = 0;
	builder_ = 0;
	lpStats_ = 0;
	solve_   = 0;
	accu_    = 0;
	step_.init(*this);
	if (ctx.numConstraints() || ctx.numVars()) { ctx.reset(); }
}
void ClaspFacade::init(ClaspConfig& config, bool discard) {
	if (discard) { discardProblem(); }
	ctx.setConfiguration(0, false); // force reload of configuration once done
	config_ = &config;
	if (config_->solve.enumMode == EnumOptions::enum_dom_record && config_->solver(0).heuId != Heuristic_t::heu_domain) {
		ctx.report(warning(Event::subsystem_facade, "Reasoning mode requires domain heuristic and is ignored!"));
		config_->solve.enumMode = EnumOptions::enum_auto;
	}
	SolveImpl::EnumPtr e(config.solve.createEnumerator(config.solve));
	if (e.get() == 0) { e = EnumOptions::nullEnumerator(); }
	if (config.solve.numSolver() > 1 && !e->supportsParallel()) {
		ctx.report(warning(Event::subsystem_facade, "Selected reasoning mode implies #Threads=1."));
		config.solve.setSolvers(1);
	}
	ctx.setConfiguration(&config, false); // prepare and apply config
	if (program() && lpStats_.get()) {
		Asp::LogicProgram* p = static_cast<Asp::LogicProgram*>(program());
		p->setOptions(config.asp);
		p->setNonHcfConfiguration(config.testerConfig());
	}
	if (!solve_.get()) { solve_ = new SolveImpl(); }
	SolveImpl::AlgoPtr a(config.solve.createSolveObject());
	solve_->init(a.release(), e.release());
	if (discard) { startStep(0); }
}

void ClaspFacade::initBuilder(ProgramBuilder* in) {
	builder_ = in;
	assume_.clear();
	builder_->startProgram(ctx);
}

ProgramBuilder& ClaspFacade::start(ClaspConfig& config, ProblemType t) {
	if      (t == Problem_t::SAT) { return startSat(config); }
	else if (t == Problem_t::PB)  { return startPB(config);  }
	else if (t == Problem_t::ASP) { return startAsp(config); }
	else                          { throw std::domain_error("Unknown problem type!"); }
}

SatBuilder& ClaspFacade::startSat(ClaspConfig& config) {
	init(config, true);
	initBuilder(new SatBuilder(config.solve.maxSat));
	return static_cast<SatBuilder&>(*builder_.get());
}

PBBuilder& ClaspFacade::startPB(ClaspConfig& config) {
	init(config, true);
	initBuilder(new PBBuilder());
	return static_cast<PBBuilder&>(*builder_.get());
}

Asp::LogicProgram& ClaspFacade::startAsp(ClaspConfig& config, bool enableUpdates) {
	init(config, true);
	Asp::LogicProgram* p = new Asp::LogicProgram();
	lpStats_             = new Asp::LpStats;
	p->accu              = lpStats_.get();
	initBuilder(p);
	p->setOptions(config.asp);
	p->setNonHcfConfiguration(config.testerConfig());
	if (enableUpdates) { enableProgramUpdates(); }
	return *p;
}

bool ClaspFacade::enableProgramUpdates() {
	CLASP_ASSERT_CONTRACT_MSG(program(), "Program was already released!");
	CLASP_ASSERT_CONTRACT(!solving() && !program()->frozen());
	if (!accu_.get()) {
		builder_->updateProgram();
		ctx.requestStepVar();
		solve_->algo->enableInterrupts();
		accu_ = new Summary();
		accu_->init(*this);
		accu_->step = UINT32_MAX;
	}
	return lpStats_.get() != 0; // currently only ASP supports program updates
}

ProgramBuilder& ClaspFacade::update(bool reloadConfig) {
	CLASP_ASSERT_CONTRACT(builder_.get() && !solving());
	CLASP_ASSERT_CONTRACT_MSG(step_.result.signal != SIGINT, "Interrupt not handled!");
	solve_->reset();
	if (reloadConfig) { init(*config_, false); }
	if (builder_->frozen()) {
		startStep(step()+1);
		if (builder_->updateProgram()) { assume_.clear(); }
		else                           { stopStep(0, true); }
	}
	return *builder_;
}
bool ClaspFacade::terminate(int signal) {
	if (solve_.get() && solve_->interrupt(signal)) {
		return true;
	}
	// solving not active or not interruptible
	stopStep(signal, false);
	return false;
}

bool ClaspFacade::prepare(EnumMode enumMode) {
	CLASP_ASSERT_CONTRACT(config_ && !solving());
	bool ok = this->ok();
	SharedMinimizeData* m = 0;
	EnumOptions& en       = config_->solve;
	if (builder_.get() && (ok = builder_->endProgram()) == true) {
		builder_->getAssumptions(assume_);
		if ((m  = en.optMode != MinimizeMode_t::ignore ? builder_->getMinimizeConstraint(&en.optBound) : 0) != 0) {
			ok = m->setMode(en.optMode, en.optBound);
			if (en.optMode == MinimizeMode_t::enumerate && en.optBound.empty()) {
				ctx.report(warning(Event::subsystem_facade, "opt-mode=enum: no bound given, optimize statement ignored."));
			}
		}
	}
	if (ok && (!ctx.frozen() || (ok = ctx.unfreeze()) == true)) {
		// Step literal only needed for volatile enumeration
		ok = (enumMode == enum_volatile || ctx.addUnary(ctx.stepLiteral()));
		if (ok) { solve_->prepare(ctx, m ? m->share() : 0, en.numModels); }
	}
	if      (!accu_.get())  { builder_ = 0; }
	else if (lpStats_.get()){ static_cast<Asp::LogicProgram*>(builder_.get())->dispose(false); }
	return (ok && ctx.endInit()) || (stopStep(0, true), false);
}
void ClaspFacade::assume(Literal p) {
	assume_.push_back(p);
}
void ClaspFacade::assume(const LitVec& ext) {
	assume_.insert(assume_.end(), ext.begin(), ext.end());
}
bool ClaspFacade::solving() const { return solve_.get() && solve_->solving(); }

const ClaspFacade::Summary& ClaspFacade::shutdown() {
	if      (!config_) { step_.init(*this); }
	else if (solving()){ terminate(SIGINT); }
	else               { stopStep(0, false); }
	return accu_.get() && accu_->step ? *accu_ : step_;
}

ClaspFacade::Result ClaspFacade::solve(EventHandler* handler) {
	CLASP_ASSERT_CONTRACT(!solving());
	struct SyncSolve : public SolveStrategy {
		SyncSolve(SolveImpl& s) : x(&s) { x->active = this; }
		~SyncSolve()                    { x->active = 0;    }
		virtual void doSolve(ClaspFacade& f) { solveImpl(f, state_done); }
		SolveImpl* x;
	} syncSolve(*solve_);
	syncSolve.solve(*this, solve_->algo.get(), handler);
	return result();
}
#if WITH_THREADS
ClaspFacade::AsyncResult ClaspFacade::solveAsync(EventHandler* handler) {
	CLASP_ASSERT_CONTRACT(!solving());
	solve_->active = new AsyncSolve();
	solve_->active->solve(*this, solve_->algo.get(), handler);
	return AsyncResult(*solve_);
}
ClaspFacade::AsyncResult ClaspFacade::startSolveAsync() {
	return solveAsync(AsyncSolve::asyncModelHandler());
}
#endif

void ClaspFacade::startStep(uint32 n) {
	step_.init(*this);
	step_.totalTime = -RealTime::getTime();
	step_.cpuTime   = -ProcessTime::getTime();
	step_.step      = n;
	ctx.report(StepStart(*this));
}
ClaspFacade::Result ClaspFacade::stopStep(int signal, bool complete) {
	if (step_.totalTime < 0) {
		double t = RealTime::getTime();
		step_.totalTime += t;
		step_.cpuTime   += ProcessTime::getTime();
		if (step_.solveTime) {
			step_.solveTime = t - step_.solveTime;
			step_.unsatTime = complete ? t - step_.unsatTime : 0;
		}
		Result res = {uint8(0), uint8(signal)};
		if (complete) { res.flags = uint8(step_.enumerated() ? Result::SAT : Result::UNSAT) | Result::EXT_EXHAUST; }
		else          { res.flags = uint8(step_.enumerated() ? Result::SAT : Result::UNKNOWN); }
		if (signal)   { res.flags|= uint8(Result::EXT_INTERRUPT); }
		step_.result = res;
		accuStep();
		ctx.report(StepReady(step_)); 
	}
	return result();
}
void ClaspFacade::accuStep() {
	if (accu_.get() && accu_->step != step_.step){
		if (step_.stats()) { ctx.accuStats(); }
		accu_->totalTime += step_.totalTime;
		accu_->cpuTime   += step_.cpuTime;
		accu_->solveTime += step_.solveTime;
		accu_->unsatTime += step_.unsatTime;
		accu_->numEnum   += step_.numEnum;
		// no aggregation
		if (step_.numEnum) { accu_->satTime = step_.satTime; }
		accu_->step       = step_.step;
		accu_->result     = step_.result;
	}
}
bool ClaspFacade::onModel(const Solver& s, const Model& m) {
	step_.unsatTime = RealTime::getTime();
	if (++step_.numEnum == 1) { step_.satTime = step_.unsatTime - step_.solveTime; }
	return solve_->update(s, m);
}
ExpectedQuantity::ExpectedQuantity(double d) : rep(d >= 0 ? d : -std::min(-d, 3.0)) {}
ExpectedQuantity::Error ExpectedQuantity::error() const {
	if (rep >= 0.0) { return error_none; }
	return static_cast<ExpectedQuantity::Error>(std::min(3, int(-rep)));
}
ExpectedQuantity::ExpectedQuantity(Error e) : rep(-double(int(e))) {}
ExpectedQuantity::operator double() const { return valid() ? rep : std::numeric_limits<double>::quiet_NaN(); }

ExpectedQuantity ClaspFacade::getStatImpl(const char* path, bool keys) const {
#define GET_KEYS(o, path) ( ExpectedQuantity((o).keys(path)) )
#define GET_OBJ(o, path)  ( ExpectedQuantity((o)[path]) )
#define COMMON_KEYS "ctx.\0solvers.\0solver.\0costs.\0time_total\0time_cpu\0time_solve\0time_unsat\0time_sat\0enumerated\0optimal\0step\0result\0"
	static const char* _keys[] = {"accu.\0hccs.\0hcc.\0lp.\0" COMMON_KEYS, 0, "accu.\0lp.\0" COMMON_KEYS, "accu.\0" COMMON_KEYS };
	enum ObjId { id_hccs, id_hcc, id_lp, id_ctx, id_solvers, id_solver, id_costs, id_total, id_cpu, id_solve, id_unsat, id_sat, id_num, id_opt, id_step, id_result };
	if (!path)  path = "";
	std::size_t kLen = 0;
	int         oId  = lpStats_.get() ? ((ctx.sccGraph.get() && ctx.sccGraph->numNonHcfs() != 0) ? id_hccs : id_lp) : id_ctx;
	const char* keyL = _keys[oId];
	bool        accu = matchStatPath(path, "accu");
	if (!*path) { 
		if (accu) { keyL += 6; }
		return keys ? ExpectedQuantity(keyL) : ExpectedQuantity::error_ambiguous_quantity;
	}
	accu = accu && step() != 0;
	for (const char* k = keyL + 6; (kLen = std::strlen(k)) != 0; k += kLen + 1, ++oId) {
		bool match = k[kLen-1] == '.' ? matchStatPath(path, k, kLen-1) : std::strcmp(path, k) == 0;
		if (match) {
			if (!*path && !keys){ return ExpectedQuantity::error_ambiguous_quantity; }
			switch(oId) {
				default: {
					const Summary* stats = accu && accu_.get() ? accu_.get() : &step_;
					if (oId == id_costs) {
						char* x;
						uint32 n = (uint32)std::strtoul(path, &x, 10);
						uint32 N = stats->optimize() && stats->costs() ? (uint32)stats->costs()->size() : 0u;
						if (x == path) {
							if (!*path) { return keys ? ExpectedQuantity("__len\0") : ExpectedQuantity::error_ambiguous_quantity; }
							if (!keys && std::strcmp(path, "__len") == 0) { return ExpectedQuantity(N); }
							return ExpectedQuantity::error_unknown_quantity;
						}
						if (*(path = x) == '.') { ++path; }
						if (*path)  { return ExpectedQuantity::error_unknown_quantity; }
						if (n >= N) { return ExpectedQuantity::error_not_available;    }
						if (!keys)  { return ExpectedQuantity((double)stats->costs()->at(n)); }
					}
					if (keys)            { return ExpectedQuantity(uint32(0)); }
					if (oId <= id_sat)   { return *((&stats->totalTime) + (oId - id_total)); }
					if (oId == id_num)   { return ExpectedQuantity(stats->numEnum); }
					if (oId == id_opt)   { return ExpectedQuantity(stats->optimal()); }
					if (oId == id_step)  { return ExpectedQuantity(stats->step);    }
					if (oId == id_result){ return ExpectedQuantity((double)stats->result); }
					return ExpectedQuantity::error_unknown_quantity; }
				case id_lp: if (!lpStats_.get()) { return ExpectedQuantity::error_not_available; }
					return keys ? GET_KEYS((*lpStats_), path) : GET_OBJ((*lpStats_), path);
				case id_ctx:     return keys ? GET_KEYS(ctx.stats(), path) : GET_OBJ(ctx.stats(), path);
				case id_solvers: return keys ? GET_KEYS(ctx.stats(*ctx.solver(0), accu), path) : getStat(ctx, path, accu, Range32(0, ctx.concurrency()));			
				case id_hccs: if (!ctx.sccGraph.get() || ctx.sccGraph->numNonHcfs() == 0) { return ExpectedQuantity::error_not_available; } else {
					ExpectedQuantity res(0.0);
					for (SharedDependencyGraph::NonHcfIter it = ctx.sccGraph->nonHcfBegin(), end = ctx.sccGraph->nonHcfEnd(); it != end; ++it) {
						const SharedContext& hCtx= it->second->ctx();
						if (keys) { return GET_KEYS(hCtx.stats(*hCtx.solver(0), accu), path); }
						ExpectedQuantity hccAccu = getStat(hCtx, path, accu, Range32(0, hCtx.concurrency()));
						if (!hccAccu.valid()) { return hccAccu; }
						res.rep += hccAccu.rep;
					}
					return res; }
				case id_solver:
				case id_hcc: 
					Range32 r(0, oId == id_solver ? ctx.concurrency() : ctx.sccGraph.get() ? ctx.sccGraph->numNonHcfs() : 0);
					char* x;
					r.lo = (uint32)std::strtoul(path, &x, 10);
					if (x == path) {
						if (!*path) { return keys ? ExpectedQuantity("__len\0") : ExpectedQuantity::error_ambiguous_quantity; }
						if (!keys && std::strcmp(path, "__len") == 0) { return ExpectedQuantity(r.hi); }
						return ExpectedQuantity::error_unknown_quantity;
					}
					if (r.lo >= r.hi)  { return ExpectedQuantity::error_not_available;    }
					if (*(path = x) == '.') { ++path; }
					const SharedContext* active = &ctx; 
					if (oId == id_hcc) {
						active = &(ctx.sccGraph->nonHcfBegin() + r.lo)->second->ctx();
						r      = Range32(0, active->concurrency());
					}
					return keys ? GET_KEYS(active->stats(*active->solver(r.lo), accu), path) : getStat(*active, path, accu, r);
			}
		}
	}
	return ExpectedQuantity::error_unknown_quantity; 
#undef GET_KEYS
#undef GET_OBJ
#undef COMMON_KEYS
}

ExpectedQuantity ClaspFacade::getStat(const char* path)const {
	return config_ && step_.totalTime >= 0.0 ? getStatImpl(path, false) : ExpectedQuantity::error_not_available;
}
const char*      ClaspFacade::getKeys(const char* path)const {
	ExpectedQuantity x =  config_ && step_.totalTime >= 0.0 ? getStatImpl(path, true) : ExpectedQuantity::error_not_available;
	if (x.valid()) { return (const char*)static_cast<uintp>(x.rep); }
	return x.error() == ExpectedQuantity::error_unknown_quantity ? 0 : "\0";
}
ExpectedQuantity ClaspFacade::getStat(const SharedContext& ctx, const char* key, bool accu, const Range<uint32>& r) const {
	if (!key || !*key) { return ExpectedQuantity::error_ambiguous_quantity; }
	ExpectedQuantity res(0.0);
	for (uint32 i = r.lo; i != r.hi && ctx.hasSolver(i); ++i) {
		ExpectedQuantity x = ctx.stats(*ctx.solver(i), accu)[key];
		if (!x.valid()) { return x; }
		res.rep += x.rep;
	}
	return res;	
}
Enumerator* ClaspFacade::enumerator() const { return solve_.get() ? solve_->enumerator() : 0; }
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspFacade::Summary
/////////////////////////////////////////////////////////////////////////////////////////
void ClaspFacade::Summary::init(ClaspFacade& f)  { std::memset(this, 0, sizeof(Summary)); facade = &f;}
int ClaspFacade::Summary::stats()          const { return ctx().master()->stats.level(); }
const Model* ClaspFacade::Summary::model() const { return facade->solve_.get() ? facade->solve_->lastModel() : 0; }
bool ClaspFacade::Summary::optimize()      const {
	if (const Enumerator* e = facade->enumerator()){
		return e->optimize() || e->lastModel().opt;
	}
	return false;
}
const char* ClaspFacade::Summary::consequences() const {
	int mt = facade->solve_.get() ? facade->solve_->modelType() : 0;
	if ( (mt & CBConsequences::brave_consequences)    == CBConsequences::brave_consequences)   { return "Brave"; }
	if ( (mt & CBConsequences::cautious_consequences) == CBConsequences::cautious_consequences){ return "Cautious"; }
	return 0;
}
uint64 ClaspFacade::Summary::optimal() const { 
	const Model* m = model();
	if (m && m->opt) {
		return !m->consequences() ? std::max(m->num, uint64(1)) : uint64(complete());
	}
	return 0;
}
}
