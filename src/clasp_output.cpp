//
// Copyright (c) 2009-present Benjamin Kaufmann
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
#include <clasp/cli/clasp_output.h>

#include <clasp/satelite.h>
#include <clasp/solver.h>
#include <clasp/util/timer.h>

#include <cmath>
#include <cstdio>

#if defined(_MSC_VER) || defined(__MINGW32__)
static inline void flockfile(FILE* file) { _lock_file(file); }
static inline void funlockfile(FILE* file) { _unlock_file(file); }
#endif
namespace {
struct FileLock {
    explicit FileLock(FILE* f) : file(f) { flockfile(f); }
    ~FileLock() {
        fflush(file);
        funlockfile(file);
    }
    FILE* file;
};
} // namespace
namespace Clasp::Cli {
/////////////////////////////////////////////////////////////////////////////////////////
// Event formatting
/////////////////////////////////////////////////////////////////////////////////////////
static int formatEvent(const BasicSolveEvent& ev, std::span<char>& str) {
    const Solver& s = *ev.solver;
    return snprintf(
        str.data(), str.size(), "%2u:%c|%7u/%-7u|%8u/%-8u|%10" PRIu64 "/%-6.3f|%8" PRId64 "/%-10" PRId64 "|", s.id(),
        static_cast<char>(ev.op), s.numFreeVars(), s.decisionLevel() > 0 ? s.levelStart(1) : s.numAssignedVars(),
        s.numConstraints(), s.numLearntConstraints(), s.stats.conflicts, ratio(s.stats.conflicts, s.stats.choices),
        ev.cLimit <= UINT32_MAX ? static_cast<int64_t>(ev.cLimit) : -1,
        ev.lLimit != UINT32_MAX ? static_cast<int64_t>(ev.lLimit) : -1);
}

static int formatEvent(const SolveTestEvent& ev, std::span<char>& str) {
    return snprintf(str.data(), str.size(), "%2u:%c| %c HCC: %-6u |%8u/%-8u|%10" PRIu64 "/%-6.3f| Time: %10.3fs |",
                    ev.solver->id(), "FP"[ev.partial], "?NY"[Clasp::clamp(ev.result, -1, 1) + 1], ev.hcc,
                    ev.solver->numConstraints(), ev.solver->numLearntConstraints(), ev.conflicts(),
                    ratio(ev.conflicts(), ev.choices()), ev.time);
}
#if CLASP_HAS_THREADS
static int formatEvent(const mt::MessageEvent& ev, std::span<char>& str) {
    using EventType = mt::MessageEvent;
    if (ev.op != EventType::completed) {
        return snprintf(str.data(), str.size(), "%2u:X| %-30.30s %-38s |", ev.solver->id(), ev.msg,
                        ev.op == EventType::sent ? "sent" : "received");
    }
    return snprintf(str.data(), str.size(), "%2u:X| %-30.30s %-20s in %13.3fs |", ev.solver->id(), ev.msg, "completed",
                    ev.time);
}
#endif
/////////////////////////////////////////////////////////////////////////////////////////
// Output
/////////////////////////////////////////////////////////////////////////////////////////
static bool stats(const ClaspFacade::Summary& summary) { return summary.facade->config()->context().stats; }
Output::Output(uint32_t verb) {
    setCallQuiet(print_no);
    setVerbosity(verb);
}
Output::~Output() = default;
void   Output::setVerbosity(uint32_t verb) { verbose_ = verb; }
void   Output::setModelQuiet(PrintLevel model) { quiet_[0] = static_cast<uint8_t>(model); }
void   Output::setOptQuiet(PrintLevel opt) { quiet_[1] = static_cast<uint8_t>(opt); }
void   Output::setCallQuiet(PrintLevel call) { quiet_[2] = static_cast<uint8_t>(call); }
double Output::elapsedTime() const { return RealTime::getTime() - start_; }
void   Output::resetStateTime() { enter_ = RealTime::getTime(); }
void   Output::start(std::string_view solver, std::string_view version, std::span<const std::string> input) {
    start_ = RealTime::getTime();
    model_ = -1.0;
    enter_ = -1.0;
    state_ = Event::Subsystem::subsystem_facade;
    doStart(solver, version, input);
}
void Output::transition(double elapsed, Event::Subsystem to, const char* message) {
    if (to != state_ || to == Event::subsystem_facade) {
        double ts = RealTime::getTime();
        if (auto es = std::exchange(state_, to); es != Event::subsystem_facade) {
            exitState(elapsed, es, ts - enter_);
        }
        enter_ = ts;
        switch (to) {
            case Event::subsystem_facade : stopStep(elapsed, ts - step_); break;
            case Event::subsystem_load   : [[fallthrough]];
            case Event::subsystem_prepare: [[fallthrough]];
            case Event::subsystem_solve:
                POTASSCO_ASSERT(message && *message);
                enterState(elapsed, to, message);
                break;
        }
    }
}
void Output::event(const Event& event) {
    using StepStart = ClaspFacade::StepStart;
    using StepReady = ClaspFacade::StepReady;
    auto t          = elapsedTime();
    if (const auto* ev = event_cast<StepStart>(event); ev) {
        summary_ = nullptr;
        last_    = false;
        state_   = Event::subsystem_facade;
        step_    = RealTime::getTime();
        enter_   = step_;
        startStep(t, static_cast<uint32_t>(ev->facade->step()));
    }
    else if (event.verb <= verbosity() && event.system != Event::subsystem_facade) {
        if (event.system == state_) {
            printProgress(t, event, RealTime::getTime() - enter_);
        }
        else if (const auto* log = event_cast<LogEvent>(event); log && log->msg) {
            transition(t, static_cast<Event::Subsystem>(log->system), log->msg);
        }
    }
    else if (auto* ready = event_cast<StepReady>(event); ready) {
        POTASSCO_ASSERT(ready->summary);
        const auto& s = *ready->summary;
        if (s.model() && last_) {
            Model m = *s.model();
            m.up    = 0; // ignore update state and always print as model
            printModel(model_, s.ctx(), m, flags(m, print_best));
        }
        else if (modelQ() == print_all && s.model() && s.model()->up && not s.model()->def) {
            printModel(model_, s.ctx(), *s.model(), flags(*s.model(), print_all));
        }
        transition(t, Event::subsystem_facade, "");
        if (callQ() == print_all) {
            summary(s, false);
        }
        else if (callQ() == print_best) {
            summary_ = ready->summary;
        }
    }
}
auto Output::flags(const Model& m, PrintLevel level) const -> ModelFlag {
    ModelFlag flags{};
    if (modelQ() <= level) {
        flags |= model_values;
    }
    if (optQ() <= level && (m.consequences() || m.hasCosts())) {
        flags |= model_meta;
    }
    return flags;
}

void Output::model(const Solver& s, const Model& m) {
    PrintLevel type    = (m.opt == 1 && not m.consequences()) || m.def ? print_best : print_all;
    bool       hasMeta = m.consequences() || m.hasCosts();
    model_             = elapsedTime();
    if (auto f = flags(m, type); f) {
        printModel(model_, *s.sharedContext(), m, f);
    }
    last_ = type != print_best && (modelQ() == print_best || (optQ() == print_best && hasMeta));
}
void Output::unsat(const Solver& s, const Model& m) {
    if (m.ctx && (modelQ() == print_all || optQ() == print_all)) {
        printUnsat(elapsedTime(), *s.sharedContext(), m);
    }
}
void Output::summary(const ClaspFacade::Summary& summary, bool final) {
    printSummary(summary, final);
    if (stats(summary)) {
        visitStats(summary);
    }
}
void Output::shutdown(const ClaspFacade::Summary& s) {
    if (summary_) {
        summary(*summary_, false);
    }
    summary(s, true);
    doShutdown();
}
void Output::enterState(double, Event::Subsystem, const char*) {}
void Output::exitState(double, Event::Subsystem, double) {}
void Output::printProgress(double, const Event&, double) {}
void Output::enterStats(StatsKey, const char*, uint32_t) {}
void Output::printLogicProgramStats(const Asp::LpStats&) {}
void Output::printProblemStats(const ProblemStats&) {}
void Output::printSolverStats(const SolverStats&) {}
void Output::printUserStats(const StatisticObject&) {}
void Output::exitStats(StatsKey) {}
auto Output::print(Literal, const char*, uintptr_t data) -> uintptr_t { return data; }
// Prints shown symbols in model.
// The function prints:
// - true literals in definite answer, followed by
// - true literals in current estimate if m.consequences()
void Output::printWitness(const SharedContext& ctx, const Model& m, uintptr_t data) {
    const auto& out = ctx.output;
    for (const auto& n : out.fact_range()) { data = print(lit_true, n.c_str(), data); }
    for (const char* x = out.theory ? out.theory->first(m) : nullptr; x; x = out.theory->next()) {
        data = print(lit_true, x, data);
    }
    const bool onlyD = m.type != Model::cautious || m.def;
    for (bool def = true;; def = not def) {
        for (const auto& pred : out.pred_range()) {
            if (m.isTrue(pred.cond) && (onlyD || m.isDef(pred.cond) == def)) {
                data = print(lit_true, pred.name.c_str(), data);
            }
        }
        if (not out.vars_range().empty()) {
            const bool showNeg = not m.consequences();
            if (out.projectMode() == ProjectMode::output || not out.filter("_")) {
                for (auto v : out.vars_range()) {
                    Literal p = posLit(v);
                    if ((showNeg || m.isTrue(p)) && (onlyD || m.isDef(p) == def)) {
                        data = print(m.isTrue(p) ? p : ~p, nullptr, data);
                    }
                }
            }
            else {
                for (auto lit : out.proj_range()) {
                    if ((showNeg || m.isTrue(lit)) && (onlyD || m.isDef(lit) == def)) {
                        data = print(m.isTrue(lit) ? lit : ~lit, nullptr, data);
                    }
                }
            }
        }
        if (def == onlyD) {
            return;
        }
    }
}
void Output::visitStats(const ClaspFacade::Summary& summary) {
    struct V : StatsVisitor {
        explicit V(Output& s) : self(&s) {}
        bool visit(StatsKey t, const char* n, Operation op, uint32_t i = 0) const {
            switch (op) {
                case enter: self->enterStats(t, n, i); break;
                case leave: self->exitStats(t); break;
            }
            return true;
        }
        bool visitGenerator(Operation) override { return true; }
        bool visitThreads(Operation op) override { return visit(stats_threads, "Thread", op); }
        bool visitTester(Operation op) override { return visit(stats_tester, "Tester", op); }
        bool visitHccs(Operation op) override { return visit(stats_hccs, "HCC", op); }
        void visitThread(uint32_t t, const SolverStats& stats) override {
            std::ignore = visit(stats_thread, "Thread", enter, t);
            V::visitSolverStats(stats);
            std::ignore = visit(stats_thread, "Thread", leave, t);
        }
        void visitHcc(uint32_t hcc, const ProblemStats& p, const SolverStats& s) override {
            std::ignore = visit(stats_thread, "HCC", enter, hcc);
            V::visitProblemStats(p);
            V::visitSolverStats(s);
            std::ignore = visit(stats_thread, "HCC", leave, hcc);
        }
        void visitLogicProgramStats(const Asp::LpStats& stats) override { self->printLogicProgramStats(stats); }
        void visitProblemStats(const ProblemStats& stats) override { self->printProblemStats(stats); }
        void visitSolverStats(const SolverStats& stats) override { self->printSolverStats(stats); }
        void visitExternalStats(const StatisticObject& stats) override {
            POTASSCO_ASSERT(stats.type() == Potassco::StatisticsType::map, "Non map statistic!");
            self->printUserStats(stats);
        }
        Output* self;
    } v{*this};
    enterStats(stats_stats, "Stats", 0);
    summary.accept(v);
    exitStats(stats_stats);
}
using StatsType = Potassco::StatisticsType;
/////////////////////////////////////////////////////////////////////////////////////////
// JsonOutput
/////////////////////////////////////////////////////////////////////////////////////////
JsonOutput::JsonOutput(uint32_t v) : Output(std::min(v, 1u)), open_("") { objStack_.reserve(10); }
JsonOutput::~JsonOutput() { JsonOutput::doShutdown(); }
void JsonOutput::printString(const char* v, const char* sep) {
    static constexpr auto     special  = "\b\f\n\r\t\"\\";
    static constexpr auto     replace  = "bfnrt\"\\";
    static constexpr uint32_t buf_size = 1024;
    assert(v);
    char buf[buf_size];
    buf[0] = '"';
    for (uint32_t n = 1; (buf[n] = *v) != 0; ++v) {
        if (const char* esc = strchr(special, buf[n])) {
            buf[n]   = '\\';
            buf[++n] = replace[esc - special];
        }
        if (++n > buf_size - 2) {
            buf[n] = 0;
            printf("%s%s", sep, buf);
            n   = 0;
            sep = "";
        }
    }
    printf("%s%s\"", sep, buf);
}
#define PRINT_KEY_VALUE(k, fmt, ...)                                                                                   \
    printf("%s%-*s\"%s\": " fmt, std::exchange(open_, ",\n"), indent(), " ", (k), __VA_ARGS__)
void JsonOutput::printKeyValue(const char* k, const char* v) {
    assert(std::strpbrk(v, "\b\f\n\r\t\"\\") == nullptr);
    PRINT_KEY_VALUE(k, "\"%s\"", v);
}
void JsonOutput::printKeyValue(const char* k, uint64_t v) { PRINT_KEY_VALUE(k, "%" PRIu64, v); }
void JsonOutput::printKeyValue(const char* k, uint32_t v) { return printKeyValue(k, static_cast<uint64_t>(v)); }
void JsonOutput::printKeyValue(const char* k, double d, bool fmtG) {
    if (std::isnan(d)) {
        PRINT_KEY_VALUE(k, "%s", "null");
    }
    else if (fmtG) {
        PRINT_KEY_VALUE(k, "%g", d);
    }
    else {
        PRINT_KEY_VALUE(k, "%.3f", d);
    }
}
#undef PRINT_KEY_VALUE
void JsonOutput::printTime(const char* name, double t) {
    if (t >= 0.0) {
        printKeyValue(name, t);
    }
}
void JsonOutput::pushObject(const char* k, ObjType t, bool startIndent) {
    char o = t == type_object ? '{' : '[';
    if (auto depth = indent(); k) {
        printf("%s%-*.*s\"%s\": %c\n", open_, depth, depth, " ", k, o);
    }
    else {
        printf("%s%-*.*s%c\n", open_, depth, depth, " ", o);
    }
    objStack_ += o;
    open_      = "";
    if (startIndent) {
        printf("%-*s", indent(), " ");
    }
}
char JsonOutput::popObject() {
    assert(not objStack_.empty());
    char o = objStack_.back();
    objStack_.pop_back();
    printf("\n%-*.*s%c", indent(), indent(), " ", o == '{' ? '}' : ']');
    open_ = ",\n";
    return o;
}
void JsonOutput::startWitness(double time) {
    assert(not objStack_.empty());
    if (objStack_.back() != '[') {
        pushObject("Witnesses", type_array);
    }
    pushObject();
    printTime("Time", time);
}
void JsonOutput::endWitness() {
    popObject();
    fflush(stdout);
}
void JsonOutput::popUntil(uint32_t sz) {
    while (size32(objStack_) > sz) { popObject(); }
}
void JsonOutput::printSum(const char* name, SumView sum, const Wsum_t* last) {
    pushObject(name, type_array, true);
    const char* sep = "";
    for (Wsum_t s : sum) {
        printf("%s%" PRId64, sep, s);
        sep = ", ";
    }
    if (last) {
        printf("%s%" PRId64, sep, *last);
    }
    popObject();
}
void JsonOutput::printCosts(SumView costs, const char* name) { printSum(name, costs); }
void JsonOutput::printCons(const SharedContext& ctx, const Model& m) {
    auto [def, open] = m.numConsequences(ctx);
    pushObject("Consequences");
    printKeyValue("True", def);
    printKeyValue("Open", open);
    popObject();
}

void JsonOutput::doStart(std::string_view solver, std::string_view version, std::span<const std::string> input) {
    if (indent() == 0) {
        open_ = "";
        pushObject();
    }
    printKeyValue("Solver", std::string(solver).append(" version ").append(version).c_str());
    pushObject("Input", type_array, true);
    for (const char* sep = ""; const auto& x : input) { printString(x.c_str(), std::exchange(sep, ",")); }
    popObject();
    pushObject("Call", type_array);
}
void JsonOutput::printModel(double elapsed, const SharedContext& ctx, const Model& m, ModelFlag flags) {
    assert(flags != model_quiet);
    startWitness(elapsed);
    if (Potassco::test(flags, model_values)) {
        pushObject("Value", type_array, true);
        printWitness(ctx, m, reinterpret_cast<uintptr_t>(""));
        popObject();
    }
    if (Potassco::test(flags, model_meta)) {
        if (m.consequences()) {
            printCons(ctx, m);
        }
        if (m.hasCosts()) {
            printCosts(m.costs);
        }
    }
    endWitness();
}
auto JsonOutput::print(Literal lit, const char* name, uintptr_t data) -> uintptr_t {
    if (const auto* sep = reinterpret_cast<const char*>(data); name) {
        printString(name, sep);
    }
    else {
        printf("%s%d", sep, toInt(lit));
    }
    return reinterpret_cast<uintptr_t>(", ");
}
void JsonOutput::printUnsat(double elapsed, const SharedContext&, const Model& m) {
    if (m.ctx->lowerBound().active() && optQ() == print_all) {
        startWitness(elapsed);
        auto lower = m.ctx->lowerBound();
        auto first = m.hasCosts() && m.costs.size() > lower.level ? m.costs.subspan(0, lower.level) : SumView();
        printSum("Lower", first, &lower.bound);
        endWitness();
    }
}
void JsonOutput::startStep(double elapsed, uint32_t) {
    popUntil(2u);
    pushObject(nullptr, type_object);
    printTime("Start", elapsed);
    fflush(stdout);
}
void JsonOutput::stopStep(double elapsed, double) {
    assert(not objStack_.empty());
    popUntil(3u);
    printTime("Stop", elapsed);
    fflush(stdout);
}
void JsonOutput::printSummary(const ClaspFacade::Summary& run, bool final) {
    popUntil(final ? 1u : 3u);
    const char* res = "UNKNOWN";
    if (run.unsat()) {
        res = "UNSATISFIABLE";
    }
    else if (run.sat()) {
        res = not run.optimum() ? "SATISFIABLE" : "OPTIMUM FOUND";
    }
    printKeyValue("Result", res);
    if (verbosity()) {
        if (run.result.interrupted()) {
            printKeyValue(run.result.signal != SIGALRM ? "INTERRUPTED" : "TIME LIMIT", 1u);
        }
        pushObject("Models");
        printKeyValue("Number", run.numEnum);
        printKeyValue("More", run.complete() ? "no" : "yes");
        if (run.sat()) {
            if (run.consequences()) {
                printKeyValue(run.consequences(), run.complete() ? "yes" : "unknown");
                printCons(run.ctx(), *run.model());
            }
            if (run.optimize()) {
                printKeyValue("Optimum", run.optimum() ? "yes" : "unknown");
                printKeyValue("Optimal", run.optimal());
                printCosts(run.costs());
            }
        }
        popObject();
        if (run.hasLower() && not run.optimum()) {
            pushObject("Bounds");
            printCosts(run.lower(), "Lower");
            printCosts(run.costs(), "Upper");
            popObject();
        }
        if (final) {
            printKeyValue("Calls", run.step + 1);
        }
        pushObject("Time");
        printKeyValue("Total", run.totalTime);
        printKeyValue("Solve", run.solveTime);
        printKeyValue("Model", run.satTime);
        printKeyValue("Unsat", run.unsatTime);
        printKeyValue("CPU", run.cpuTime);
        popObject(); // Time
        if (run.ctx().concurrency() > 1) {
            printKeyValue("Threads", run.ctx().concurrency());
            printKeyValue("Winner", run.ctx().winner());
        }
    }
}
void JsonOutput::enterStats(StatsKey t, const char* name, uint32_t) {
    switch (t) {
        case stats_stats  : pushObject(name); break;
        case stats_threads: pushObject(name, type_array); break;
        case stats_tester : pushObject(name); break;
        case stats_hccs   : pushObject(name, type_array); break;
        case stats_thread : [[fallthrough]];
        case stats_hcc    : pushObject(nullptr, type_object); break;
    }
}
void JsonOutput::exitStats(StatsKey) { popObject(); }
void JsonOutput::printLogicProgramStats(const Asp::LpStats& lp) {
    using namespace Asp;
    pushObject("LP");
    pushObject("Rules");
    printKeyValue("Original", lp.rules[0].sum());
    printKeyValue("Final", lp.rules[1].sum());
    for (auto i : irange(RuleStats::numKeys())) {
        if (i != RuleStats::normal && lp.rules[0][i]) {
            pushObject(RuleStats::toStr(i));
            printKeyValue("Original", lp.rules[0][i]);
            printKeyValue("Final", lp.rules[1][i]);
            popObject();
        }
    }
    popObject(); // Rules
    printKeyValue("Atoms", lp.atoms);
    if (lp.auxAtoms) {
        printKeyValue("AuxAtoms", lp.auxAtoms);
    }
    if (lp.disjunctions[0]) {
        pushObject("Disjunctions");
        printKeyValue("Original", lp.disjunctions[0]);
        printKeyValue("Final", lp.disjunctions[1]);
        popObject();
    }
    pushObject("Bodies");
    printKeyValue("Original", lp.bodies[0].sum());
    printKeyValue("Final", lp.bodies[1].sum());
    for (uint32_t i : irange(1u, BodyStats::numKeys())) {
        if (lp.bodies[0][i]) {
            pushObject(BodyStats::toStr(i));
            printKeyValue("Original", lp.bodies[0][i]);
            printKeyValue("Final", lp.bodies[1][i]);
            popObject();
        }
    }
    popObject();
    if (lp.sccs == 0) {
        printKeyValue("Tight", "yes");
    }
    else if (lp.sccs == PrgNode::no_scc) {
        printKeyValue("Tight", "N/A");
    }
    else {
        printKeyValue("Tight", "no");
        printKeyValue("SCCs", lp.sccs);
        printKeyValue("NonHcfs", lp.nonHcfs);
        printKeyValue("UfsNodes", lp.ufsNodes);
        printKeyValue("NonHcfGammas", lp.gammas);
    }
    pushObject("Equivalences");
    printKeyValue("Sum", lp.eqs());
    printKeyValue("Atom", lp.eqs(VarType::atom));
    printKeyValue("Body", lp.eqs(VarType::body));
    printKeyValue("Other", lp.eqs(VarType::hybrid));
    popObject();
    popObject(); // LP
}
void JsonOutput::printProblemStats(const ProblemStats& p) {
    pushObject("Problem");
    printKeyValue("Variables", p.vars.num);
    printKeyValue("Eliminated", p.vars.eliminated);
    printKeyValue("Frozen", p.vars.frozen);
    pushObject("Constraints");
    uint32_t sum = p.numConstraints();
    printKeyValue("Sum", sum);
    printKeyValue("Binary", p.constraints.binary);
    printKeyValue("Ternary", p.constraints.ternary);
    popObject(); // Constraints
    printKeyValue("AcycEdges", p.acycEdges);
    popObject(); // PS
}
void JsonOutput::printSolverStats(const SolverStats& stats) {
    printCoreStats(stats);
    if (stats.extra) {
        printExtStats(*stats.extra, objStack_.size() == 2);
        printJumpStats(stats.extra->jumps);
    }
}
void JsonOutput::printUserStats(const StatisticObject& s) { // NOLINT(misc-no-recursion)
    for (auto i : irange(s)) {
        const char* key = s.type() == StatsType::map ? s.key(i) : nullptr;
        if (StatisticObject child = key ? s.at(key) : s[i]; child.type() == StatsType::value) {
            printKeyValue(key, child.value(), true);
        }
        else {
            pushObject(key, child.type() == StatsType::map ? type_object : type_array);
            JsonOutput::printUserStats(child);
            popObject();
        }
    }
}
void JsonOutput::doShutdown() {
    if (not objStack_.empty()) {
        popUntil(0u);
        printf("\n");
        fflush(stdout);
    }
}
void JsonOutput::printCoreStats(const CoreStats& st) {
    pushObject("Core");
    printKeyValue("Choices", st.choices);
    printKeyValue("Conflicts", st.conflicts);
    printKeyValue("Backtracks", st.backtracks());
    printKeyValue("Backjumps", st.backjumps());
    printKeyValue("Restarts", st.restarts);
    printKeyValue("RestartAvg", st.avgRestart());
    printKeyValue("RestartLast", st.lastRestart);
    popObject(); // Core
}
void JsonOutput::printExtStats(const ExtendedStats& stx, bool generator) {
    pushObject("More");
    printKeyValue("CPU", stx.cpuTime);
    printKeyValue("Models", stx.models);
    if (stx.domChoices) {
        printKeyValue("DomChoices", stx.domChoices);
    }
    if (stx.hccTests) {
        pushObject("StabTests");
        printKeyValue("Sum", stx.hccTests);
        printKeyValue("Full", stx.hccTests - stx.hccPartial);
        printKeyValue("Partial", stx.hccPartial);
        popObject();
    }
    if (stx.models) {
        printKeyValue("AvgModel", stx.avgModel());
    }
    printKeyValue("Splits", stx.splits);
    printKeyValue("Problems", stx.gps);
    printKeyValue("AvgGPLength", stx.avgGp());
    pushObject("Lemma");
    printKeyValue("Sum", stx.lemmas());
    printKeyValue("Deleted", stx.deleted);
    pushObject("Type", type_array);
    const char* names[] = {"Short", "Conflict", "Loop", "Other"};
    for (auto i : irange(names)) {
        pushObject();
        printKeyValue("Type", names[i]);
        if (i == ConstraintType::static_) {
            printKeyValue("Sum", stx.binary + stx.ternary);
            printKeyValue("Ratio", percent(stx.binary + stx.ternary, stx.lemmas()));
            printKeyValue("Binary", stx.binary);
            printKeyValue("Ternary", stx.ternary);
        }
        else {
            printKeyValue("Sum", stx.lemmas(static_cast<ConstraintType>(i)));
            printKeyValue("AvgLen", stx.avgLen(static_cast<ConstraintType>(i)));
        }
        popObject();
    }
    popObject();
    popObject(); // Lemma
    if (stx.distributed || stx.integrated) {
        pushObject("Distribution");
        printKeyValue("Distributed", stx.distributed);
        printKeyValue("Ratio", stx.distRatio());
        printKeyValue("AvgLbd", stx.avgDistLbd());
        popObject();
        pushObject("Integration");
        printKeyValue("Integrated", stx.integrated);
        printKeyValue("Units", stx.intImps);
        printKeyValue("AvgJump", stx.avgIntJump());
        if (generator) {
            printKeyValue("Ratio", stx.intRatio());
        }
        popObject();
    }
    popObject(); // More
}
void JsonOutput::printJumpStats(const JumpStats& st) {
    pushObject("Jumps");
    printKeyValue("Sum", st.jumps);
    printKeyValue("Max", st.maxJump);
    printKeyValue("MaxExec", st.maxJumpEx);
    printKeyValue("Avg", st.avgJump());
    printKeyValue("AvgExec", st.avgJumpEx());
    printKeyValue("Levels", st.jumpSum);
    printKeyValue("LevelsExec", st.jumped());
    pushObject("Bounded");
    printKeyValue("Sum", st.bounded);
    printKeyValue("Max", st.maxBound);
    printKeyValue("Avg", st.avgBound());
    printKeyValue("Levels", st.boundSum);
    popObject();
    popObject();
}
/////////////////////////////////////////////////////////////////////////////////////////
// TextOutput
/////////////////////////////////////////////////////////////////////////////////////////
// NOLINTBEGIN
#define PRINT_KEY_VALUE(k, fmt, ...)                                                                                   \
    printf("%s%-*s%-*s: " fmt, format_[cat_comment], _indent(k), "", width_ - _indent(k), _key(k), __VA_ARGS__)
#define PRINT_LN(cat, fmt, ...)          printf("%s" fmt "\n", format_[cat], __VA_ARGS__)
#define PRINT_COMMENT_LN(verb, fmt, ...) (verbosity() >= (verb) && PRINT_LN(cat_comment, fmt, __VA_ARGS__))
#define PRINT_IF_LN(cond, fmt, ...)      ((cond) ? printf(fmt "\n", __VA_ARGS__) : printf("\n"))
#define PRINT_BR(cat)                    printf("%s\n", format_[cat])
static constexpr const char* _key(const char* k) { return k; }
static constexpr int         _indent(const char*) { return 0; }
static constexpr const char* _key(const auto& k) { return k.first; }
static constexpr int         _indent(const auto& k) { return k.second; }
// NOLINTEND
constexpr auto row_sep = "------------------------------------------------------------------------------------------|";
constexpr auto acc_sep = "====================================== Accumulation ======================================|";
constexpr auto sat_pre = "Sat-Prepro";
static std::string prettify(const std::string& str) {
    if (str.size() < 40) {
        return str;
    }
    std::string t("...");
    t.append(str.end() - 38, str.end());
    return t;
}
TextOutput::TextOutput(uint32_t verbosity, Format fmt, const char* catAtom, char ifs) : Output(verbosity) {
    result_[res_unknown]    = "UNKNOWN";
    result_[res_sat]        = "SATISFIABLE";
    result_[res_unsat]      = "UNSATISFIABLE";
    result_[res_opt]        = "OPTIMUM FOUND";
    format_[cat_comment]    = "";
    format_[cat_value]      = "";
    format_[cat_objective]  = "Optimization: ";
    format_[cat_result]     = "";
    format_[cat_value_term] = "";
    format_[cat_atom_name]  = "%s";
    format_[cat_atom_var]   = "-%d";
    if (fmt == format_aspcomp) {
        format_[cat_comment]   = "% ";
        format_[cat_value]     = "ANSWER\n";
        format_[cat_objective] = "COST ";
        format_[cat_atom_name] = "%s.";
        result_[res_sat]       = "";
        result_[res_unsat]     = "INCONSISTENT";
        result_[res_opt]       = "OPTIMUM";
        setModelQuiet(print_best);
        setOptQuiet(print_best);
    }
    else if (fmt == format_sat09 || fmt == format_pb09) {
        format_[cat_comment]    = "c ";
        format_[cat_value]      = "v ";
        format_[cat_objective]  = "o ";
        format_[cat_result]     = "s ";
        format_[cat_value_term] = "0";
        if (fmt == format_pb09) {
            format_[cat_value_term] = "";
            format_[cat_atom_var]   = "-x%d";
            setModelQuiet(print_best);
        }
    }
    if (catAtom && *catAtom) {
        char f = 0;
        for (const char* x = catAtom; *x; ++x) {
            POTASSCO_CHECK_PRE(*x != '\n', "cat_atom: Invalid format string - new line not allowed");
            if (*x == '%') {
                POTASSCO_CHECK_PRE(*++x, "cat_atom: Invalid format string - missing format specifier");
                if (*x != '%') {
                    POTASSCO_CHECK_PRE(f == 0, "cat_atom: Invalid format string - too many arguments");
                    POTASSCO_CHECK_PRE(std::strchr("sd0", *x) != nullptr,
                                       "cat_atom: Invalid format string - invalid format specifier");
                    f = *x;
                }
            }
        }
        if (f == '0') {
            auto len = std::strlen(catAtom);
            fmt_.reserve((len * 2) + 2);
            fmt_.append(catAtom).append(1, '\0').append(1, '-').append(catAtom);
            auto p                 = fmt_.find("%0") + 1;
            fmt_[p]                = 's';
            fmt_[len + 2 + p]      = 'd';
            format_[cat_atom_name] = fmt_.c_str();
            format_[cat_atom_var]  = fmt_.c_str() + len + 1;
        }
        else {
            format_[f == 's' ? cat_atom_name : cat_atom_var] = catAtom;
        }
    }
    POTASSCO_CHECK_PRE(*format_[cat_atom_var] == '-', "cat_atom: Invalid format string - must start with '-'");
    ifs_[0]   = ifs;
    ifs_[1]   = 0;
    width_    = 13 + static_cast<int>(strlen(format_[cat_comment]));
    progress_ = {};
}
TextOutput::~TextOutput() = default;
void TextOutput::configureMaxsat() { result_[res_sat] = "UNKNOWN"; }
void TextOutput::setModelPrinter(ModelPrinter printer) { onModel_ = std::move(printer); }
auto TextOutput::getIfsSuffix(char ifs, CategoryKey c) const -> const char* {
    return ifs != '\n' || std::string_view(format_[c]).ends_with('\n') ? "" : format_[c];
}
auto TextOutput::getIfsSuffix(CategoryKey c) const -> const char* { return getIfsSuffix(ifs_[0], c); }
auto TextOutput::fieldSeparator() const -> const char* { return ifs_; }
void TextOutput::clearProgress(int nLines) {
    if (progress_.last != -1) {
        if (progress_.last != INT_MAX) {
            progress_.last = INT_MAX;
            PRINT_COMMENT_LN(2u, "%s", row_sep);
        }
        progress_.lines -= nLines;
    }
}
// NOLINTBEGIN(readability-make-member-function-const,readability-convert-member-functions-to-static)
void TextOutput::printEnter(const char* message, const char* suffix) {
    printf("%s%-13s%s", format_[cat_comment], message, suffix);
    fflush(stdout);
}
void TextOutput::printExit(double stateElapsed) { printf("%.3fs\n", stateElapsed); }
void TextOutput::printCosts(SumView costs, char ifs, const char* ifsSuffix) {
    if (not costs.empty()) {
        printf("%" PRId64, costs[0]);
        for (auto w : costs.subspan(1)) { printf("%c%s%" PRId64, ifs, ifsSuffix, w); }
    }
}
void TextOutput::printCosts(SumView costs) { printCosts(costs, *fieldSeparator(), getIfsSuffix(cat_objective)); }
void TextOutput::printBounds(SumView lower, SumView upper) {
    const char* sep = "";
    for (auto uMax = size32(upper), lMax = size32(lower); auto i : irange(std::max(uMax, lMax))) {
        if (i >= uMax) {
            printf("%s[%" PRId64 ";*]", sep, lower[i]);
        }
        else if (i >= lMax || lower[i] == upper[i]) {
            printf("%s%" PRId64, sep, upper[i]);
        }
        else {
            printf("%s[%" PRId64 ";%" PRId64 "]", sep, lower[i], upper[i]);
        }
        sep = " ";
    }
}
void TextOutput::printMeta(const SharedContext& ctx, const Model& m) {
    if (m.consequences()) {
        auto [low, est] = m.numConsequences(ctx);
        PRINT_LN(cat_comment, "Consequences: [%u;%u]", low, low + est);
    }
    if (m.hasCosts()) {
        printf("%s", format_[cat_objective]);
        printCosts(m.costs);
        printf("\n");
    }
}
void TextOutput::printPreproEvent(double stateTime, const Event& ev) {
    if (const auto* sat = event_cast<SatElite::Progress>(ev)) {
        if (sat->op != SatElite::Progress::event_algorithm) {
            printf("%s%-13s: %c: %8u/%-8u\r", format_[cat_comment], sat_pre, static_cast<char>(sat->op), sat->cur,
                   sat->max);
        }
        else if (sat->cur != sat->max) {
            printExit(stateTime);
            printEnter(sat_pre, ":\r");
            resetStateTime();
        }
        else {
            auto* p = sat->self;
            printf("%s%-13s: %.3fs (ClRemoved: %u ClAdded: %u LitsStr: %u)\n", format_[cat_comment], sat_pre, stateTime,
                   p->stats.clRemoved, p->stats.clAdded, p->stats.litsRemoved);
            progress_.last = sat->id;
        }
    }
}
void TextOutput::printSolveEvent(double elapsed, const Event& ev, double stateTime) {
    char      lEnd = '\n';
    char      line[128];
    int       eventId = static_cast<int>(ev.id);
    std::span buffer(line, sizeof(line));
    int       written = -1;
    if (const auto* be = event_cast<BasicSolveEvent>(ev)) {
        if ((verbosity() & 1) == 0) {
            return;
        }
        written = formatEvent(*be, buffer);
    }
    else if (const auto* te = event_cast<SolveTestEvent>(ev)) {
        if ((verbosity() & 4) == 0) {
            return;
        }
        written = formatEvent(*te, buffer);
        lEnd    = te->result == -1 ? '\r' : '\n';
    }
#if CLASP_HAS_THREADS
    else if (const auto* me = event_cast<mt::MessageEvent>(ev)) {
        written = formatEvent(*me, buffer);
        eventId = static_cast<int>(Event::eventId<LogEvent>());
    }
#endif
    else if (const auto* log = event_cast<LogEvent>(ev)) {
        char tb[30];
        tb[0] = 0;
        snprintf(tb, std::size(tb), "[Solving+%.3fs]", stateTime);
        written = snprintf(buffer.data(), buffer.size(), "%2u:L| %-30s %-38.38s |", log->solver->id(), tb, log->msg);
    }
    if (written < 0 || static_cast<std::size_t>(written) >= buffer.size()) {
        return;
    }
    buffer = buffer.subspan(static_cast<std::size_t>(written));
    snprintf(buffer.data(), buffer.size(), " %10.3fs |", elapsed);
    FileLock lock(stdout);
    if (progress_.lines <= 0 || eventId != progress_.last) {
        if (progress_.lines <= 0) {
            const char* prefix = format_[cat_comment];
            if ((this->verbosity() & 1) != 0 || ev.id == Event::eventId<SolveTestEvent>()) {
                printf("%s%s\n"
                       "%sID:T       Vars           Constraints         State            Limits            Time     |\n"
                       "%s       #free/#fixed   #problem/#learnt  #conflicts/ratio #conflict/#learnt                |\n"
                       "%s%s\n",
                       prefix, row_sep, prefix, prefix, prefix, row_sep);
            }
            else {
                printf("%s%s\n"
                       "%sID:T       Info                     Info                      Info               Time     |\n"
                       "%s%s\n",
                       prefix, row_sep, prefix, prefix, row_sep);
            }
            progress_.lines = 20;
        }
        else if (progress_.last != -1) {
            PRINT_LN(cat_comment, "%s", row_sep);
        }
        progress_.last = eventId;
    }
    progress_.lines -= static_cast<int>(lEnd == '\n');
    printf("%s%s%c", format_[cat_comment], line, lEnd);
}
// NOLINTEND(readability-make-member-function-const,readability-convert-member-functions-to-static)
void TextOutput::doShutdown() {}
void TextOutput::doStart(std::string_view solver, std::string_view version, std::span<const std::string> input) {
    if (not solver.empty()) {
        PRINT_COMMENT_LN(1u, "%.*s version %.*s", static_cast<int>(solver.length()), solver.data(),
                         static_cast<int>(version.length()), version.data());
    }
    if (not input.empty()) {
        PRINT_COMMENT_LN(1u, "Reading from %s%s", prettify(input.front()).c_str(), input.size() > 1 ? " ..." : "");
    }
}
void TextOutput::printModelValues(const SharedContext& ctx, const Model& m) {
    printf("%s", format_[cat_value]);
    std::pair<uint32_t, uint32_t> data{};
    printWitness(ctx, m, reinterpret_cast<uintptr_t>(&data));
    if (*format_[cat_value_term]) {
        printf("%c%s%s", *fieldSeparator(), getIfsSuffix(cat_value), format_[cat_value_term]);
    }
    printf("\n");
}
uintptr_t TextOutput::print(Literal lit, const char* name, uintptr_t data) {
    constexpr uint32_t msb = 31u;
    auto& [accu, maxLine]  = *reinterpret_cast<std::pair<uint32_t, uint32_t>*>(data);
    if (accu == 0 && *getIfsSuffix(cat_value)) {
        Potassco::store_set_bit(accu, msb);
    }
    const char* suf = Potassco::test_bit(accu, msb) ? format_[cat_value] : "";
    Potassco::store_clear_bit(accu, msb);
    if (accu < maxLine) {
        accu += static_cast<unsigned>(printf("%c%s", *fieldSeparator(), suf));
    }
    else if (not maxLine) {
        maxLine = name || *fieldSeparator() != ' ' ? UINT32_MAX : 70;
    }
    else {
        printf("%c%s", '\n', getIfsSuffix('\n', cat_value));
        accu = 0;
    }
    POTASSCO_WARNING_PUSH()
    POTASSCO_WARNING_IGNORE_GNU("-Wformat-nonliteral") // format not a string literal
    if (name) {
        accu += static_cast<unsigned>(printf(format_[cat_atom_name], name));
    }
    else {
        accu += static_cast<unsigned>(printf(format_[cat_atom_var] + not lit.sign(), static_cast<int>(lit.var())));
    }
    POTASSCO_WARNING_POP()
    if (*suf) {
        Potassco::store_set_bit(accu, msb);
    }
    return data;
}
void TextOutput::printModel(double elapsed, const SharedContext& ctx, const Model& m, ModelFlag flags) {
    POTASSCO_ASSERT(flags != model_quiet);
    FileLock    lock(stdout);
    const char* type = not m.up ? "Answer" : "Update";
    clearProgress(3);
    PRINT_COMMENT_LN(1u, "%s: %" PRIu64 " (Time: %.3fs)", type, m.num, elapsed);
    if (Potassco::test(flags, model_values)) {
        if (not onModel_) {
            printModelValues(ctx, m);
        }
        else {
            onModel_(*this, ctx, m);
        }
    }
    if (Potassco::test(flags, model_meta)) {
        printMeta(ctx, m);
    }
}

void TextOutput::printUnsat(double elapsed, const SharedContext& ctx, const Model& m) {
    if (optQ() != print_all) {
        return;
    }
    FileLock lock(stdout);
    if (auto lb = m.ctx->lowerBound(); lb.active()) {
        clearProgress(1);
        printf("%s%-12s: ", format_[cat_comment], "Progression");
        if (m.costs.size() > lb.level) {
            for (auto i : irange(lb.level)) { printf("%" PRId64 " ", m.costs[i]); }
            Wsum_t ub = m.costs[lb.level];
            int    w  = 1;
            for (Wsum_t x = ub; x > 9; ++w) { x /= 10; }
            double err = static_cast<double>(ub - lb.bound) / static_cast<double>(lb.bound);
            if (err < 0) {
                err = -err;
            }
            printf("[%*" PRId64 ";%" PRId64 "] (Error: %g ", w, lb.bound, ub, err);
        }
        else {
            printf("[%6" PRId64 ";inf] (", lb.bound);
        }
        printf("Time: %.3fs)\n", elapsed);
    }
    if (m.num != 0 && m.up) {
        printMeta(ctx, m);
    }
}
void TextOutput::startStep(double, uint32_t step) {
    progress_ = {};
    if (callQ() != print_no) {
        PRINT_COMMENT_LN(1u, "%s", row_sep);
        PRINT_COMMENT_LN(2u, "%-13s: %d", "Call", step + 1);
    }
}
void TextOutput::enterState(double, Event::Subsystem sys, const char* activity) {
    if (sys == Event::subsystem_load || sys == Event::subsystem_prepare) {
        printEnter(activity, ": ");
    }
    else if (sys == Event::subsystem_solve) {
        PRINT_COMMENT_LN(1u, "%s...", activity);
        progress_ = {};
    }
}
void TextOutput::exitState(double, Event::Subsystem sys, double stateElapsed) {
    if (sys == Event::subsystem_load || (sys == Event::subsystem_prepare && progress_.last == -1)) {
        printExit(stateElapsed);
    }
}
void TextOutput::stopStep(double, double) { PRINT_COMMENT_LN(2u - (callQ() != print_no), "%s", row_sep); }
void TextOutput::printProgress(double elapsed, const Event& ev, double stateElapsed) {
    if (ev.system == Event::subsystem_prepare) {
        printPreproEvent(stateElapsed, ev);
    }
    else if (ev.system == Event::subsystem_solve) {
        printSolveEvent(elapsed, ev, stateElapsed);
    }
}
void TextOutput::printSummary(const ClaspFacade::Summary& run, bool final) {
    if (final && callQ() != print_no) {
        PRINT_COMMENT_LN(1u, "%s", acc_sep);
    }
    auto res = res_unknown;
    if (run.unsat()) {
        res = res_unsat;
    }
    else if (run.sat()) {
        res = not run.optimum() ? res_sat : res_opt;
    }
    if (const auto* str = result_[res]; *str) {
        PRINT_LN(cat_result, "%s", str);
    }
    if (verbosity() || stats(run)) {
        PRINT_BR(cat_comment);
        if (run.result.interrupted()) {
            const char* key = run.result.signal != SIGALRM ? "INTERRUPTED" : "TIME LIMIT";
            PRINT_KEY_VALUE(key, "%u\n", 1u);
        }
        const char* const moreStr = run.complete() ? "" : "+";
        PRINT_KEY_VALUE("Models", "%" PRIu64 "%s\n", run.numEnum, moreStr);
        if (run.sat()) {
            if (run.consequences()) {
                PRINT_KEY_VALUE(indent(run.consequences()), "%s\n", run.complete() ? "yes" : "unknown");
            }
            if (run.hasCosts()) {
                PRINT_KEY_VALUE(indent("Optimum"), "%s\n", run.optimum() ? "yes" : "unknown");
            }
            if (run.optimize()) {
                if (run.optimal() > 1) {
                    PRINT_KEY_VALUE(indent("Optimal"), "%" PRIu64 "\n", run.optimal());
                }
                PRINT_KEY_VALUE("Optimization", "%s", "");
                printCosts(run.costs(), ' ');
                printf("\n");
            }
            if (run.consequences()) {
                PRINT_KEY_VALUE("Consequences", "%u%s\n", run.model()->numConsequences(run.ctx()).first, moreStr);
            }
        }
        if (run.hasLower() && not run.optimum()) {
            PRINT_KEY_VALUE("Bounds", "%s", "");
            printBounds(run.lower(), run.costs());
            printf("\n");
        }
        if (final) {
            PRINT_KEY_VALUE("Calls", "%u\n", run.step + 1);
        }
        PRINT_KEY_VALUE("Time", "%.3fs (Solving: %.2fs 1st Model: %.2fs Unsat: %.2fs)\n", run.totalTime, run.solveTime,
                        run.satTime, run.unsatTime);
        PRINT_KEY_VALUE("CPU Time", "%.3fs\n", run.cpuTime);
        if (run.ctx().concurrency() > 1) {
            PRINT_KEY_VALUE("Threads", "%-8u (Winner: %u)\n", run.ctx().concurrency(), run.ctx().winner());
        }
    }
}
void TextOutput::startSection(const char* section) const {
    PRINT_LN(cat_comment, "============ %s Stats ============", section);
    PRINT_BR(cat_comment);
}
void TextOutput::startObject(const char* object, uint32_t n) const {
    PRINT_LN(cat_comment, "[%s %u]", object, n);
    PRINT_BR(cat_comment);
}
void TextOutput::enterStats(StatsKey t, const char* name, uint32_t n) {
    if (t == stats_stats) {
        PRINT_BR(cat_comment);
        accu_ = true;
    }
    if (t == stats_threads || t == stats_tester) {
        accu_ = false;
        startSection(name);
    }
    else if (t == stats_thread || t == stats_hcc) {
        startObject(name, n);
    }
}
void TextOutput::printSolverStats(const SolverStats& stats) {
    if (not accu_ && stats.extra) {
        PRINT_KEY_VALUE("CPU Time", "%.3fs\n", stats.extra->cpuTime);
        PRINT_KEY_VALUE("Models", "%" PRIu64 "\n", stats.extra->models);
    }
    PRINT_KEY_VALUE("Choices", "%-8" PRIu64, stats.choices);
    PRINT_IF_LN(stats.extra && stats.extra->domChoices, " (Domain: %" PRIu64 ")", stats.extra->domChoices);
    PRINT_KEY_VALUE("Conflicts", "%-8" PRIu64 " (Analyzed: %" PRIu64 ")\n", stats.conflicts, stats.backjumps());
    PRINT_KEY_VALUE("Restarts", "%-8" PRIu64, stats.restarts);
    PRINT_IF_LN(stats.restarts, " (Average: %.2f Last: %" PRIu64 " Blocked: %" PRIu64 ")", stats.avgRestart(),
                stats.lastRestart, stats.blRestarts);

    if (not stats.extra) {
        return;
    }
    const ExtendedStats& stx = *stats.extra;
    const JumpStats&     stj = stx.jumps;
    if (stx.hccTests) {
        PRINT_KEY_VALUE("Stab. Tests", "%-8" PRIu64 " (Full: %" PRIu64 " Partial: %" PRIu64 ")\n", stx.hccTests,
                        stx.hccTests - stx.hccPartial, stx.hccPartial);
    }
    if (stx.models) {
        PRINT_KEY_VALUE("Model-Level", "%-8.1f\n", stx.avgModel());
    }
    PRINT_KEY_VALUE("Problems", "%-8" PRIu64 " (Average Length: %.2f Splits: %" PRIu64 ")\n",
                    static_cast<uint64_t>(stx.gps), stx.avgGp(), static_cast<uint64_t>(stx.splits));
    uint64_t sum = stx.lemmas();
    PRINT_KEY_VALUE("Lemmas", "%-8" PRIu64 " (Deleted: %" PRIu64 ")\n", sum, stx.deleted);
    PRINT_KEY_VALUE(indent("Binary"), "%-8" PRIu64 " (Ratio: %6.2f%%)\n", static_cast<uint64_t>(stx.binary),
                    percent(stx.binary, sum));
    PRINT_KEY_VALUE(indent("Ternary"), "%-8" PRIu64 " (Ratio: %6.2f%%)\n", static_cast<uint64_t>(stx.ternary),
                    percent(stx.ternary, sum));
    const char* names[] = {"Conflict", "Loop", "Other"};
    for (auto i : irange(names)) {
        auto type = static_cast<ConstraintType>(i + 1);
        PRINT_KEY_VALUE(indent(names[i]), "%-8" PRIu64 " (Average Length: %6.1f Ratio: %6.2f%%) \n", stx.lemmas(type),
                        stx.avgLen(type), percent(stx.lemmas(type), sum));
    }
    if (stx.distributed || stx.integrated) {
        PRINT_KEY_VALUE(indent("Distributed"), "%-8" PRIu64 " (Ratio: %6.2f%% Average LBD: %.2f) \n", stx.distributed,
                        stx.distRatio() * 100.0, stx.avgDistLbd());
        PRINT_KEY_VALUE(indent("Integrated"), "%-8" PRIu64, stx.integrated);
        if (accu_) {
            printf(" (Ratio: %6.2f%% ", stx.intRatio() * 100.0);
        }
        else {
            printf(" (");
        }
        printf("Unit: %" PRIu64 " Average Jumps: %.2f)\n", stx.intImps, stx.avgIntJump());
    }
    PRINT_KEY_VALUE("Backjumps", "%-8" PRIu64 " (Average: %5.2f Max: %3u Sum: %6" PRIu64 ")\n", stj.jumps,
                    stj.avgJump(), stj.maxJump, stj.jumpSum);
    PRINT_KEY_VALUE(indent("Executed"), "%-8" PRIu64 " (Average: %5.2f Max: %3u Sum: %6" PRIu64 " Ratio: %6.2f%%)\n",
                    stj.jumps - stj.bounded, stj.avgJumpEx(), stj.maxJumpEx, stj.jumped(), stj.jumpedRatio() * 100.0);
    PRINT_KEY_VALUE(indent("Bounded"), "%-8" PRIu64 " (Average: %5.2f Max: %3u Sum: %6" PRIu64 " Ratio: %6.2f%%)\n",
                    stj.bounded, stj.avgBound(), stj.maxBound, stj.boundSum, 100.0 - (stj.jumpedRatio() * 100.0));
    PRINT_BR(cat_comment);
}
void TextOutput::printProblemStats(const ProblemStats& stats) {
    uint32_t sum = stats.numConstraints();
    PRINT_KEY_VALUE("Variables", "%-8u (Eliminated: %4u Frozen: %4u)\n", stats.vars.num, stats.vars.eliminated,
                    stats.vars.frozen);
    PRINT_KEY_VALUE("Constraints", "%-8u (Binary: %5.1f%% Ternary: %5.1f%% Other: %5.1f%%)\n", sum,
                    percent(stats.constraints.binary, sum), percent(stats.constraints.ternary, sum),
                    percent(stats.constraints.other, sum));
    if (stats.acycEdges) {
        PRINT_KEY_VALUE("Acyc-Edges", "%-8u\n", stats.acycEdges);
    }
    PRINT_BR(cat_comment);
}
void TextOutput::printLogicProgramStats(const Asp::LpStats& stats) {
    using namespace Asp;
    uint32_t rFinal = stats.rules[1].sum(), rOriginal = stats.rules[0].sum();
    PRINT_KEY_VALUE("Rules", "%-8u", rFinal);
    PRINT_IF_LN(rFinal != rOriginal, " (Original: %u)", rOriginal);
    for (auto i : irange(RuleStats::numKeys())) {
        if (i == RuleStats::normal) {
            continue;
        }
        if (uint32_t r = stats.rules[0][i]) {
            PRINT_KEY_VALUE(indent(RuleStats::toStr(i)), "%-8u", stats.rules[1][i]);
            PRINT_IF_LN(r != stats.rules[1][i], " (Original: %u)", r);
        }
    }
    PRINT_KEY_VALUE("Atoms", "%-8u", stats.atoms);
    PRINT_IF_LN(stats.auxAtoms, " (Original: %u Auxiliary: %u)", stats.atoms - stats.auxAtoms, stats.auxAtoms);
    if (stats.disjunctions[0]) {
        PRINT_KEY_VALUE("Disjunctions", "%-8u (Original: %u)\n", stats.disjunctions[1], stats.disjunctions[0]);
    }
    uint32_t bFinal = stats.bodies[1].sum(), bOriginal = stats.bodies[0].sum();
    PRINT_KEY_VALUE("Bodies", "%-8u", bFinal);
    PRINT_IF_LN(bFinal != bOriginal, " (Original: %u)", bOriginal);
    for (auto i : irange(1u, BodyStats::numKeys())) {
        if (uint32_t b = stats.bodies[0][i]) {
            PRINT_KEY_VALUE(indent(BodyStats::toStr(i)), "%-8u", stats.bodies[1][i]);
            PRINT_IF_LN(b != stats.bodies[1][i], " (Original: %u)", b);
        }
    }
    if (stats.eqs() > 0) {
        PRINT_KEY_VALUE("Equivalences", "%-8u (Atom=Atom: %u Body=Body: %u Other: %u)\n", stats.eqs(),
                        stats.eqs(VarType::atom), stats.eqs(VarType::body), stats.eqs(VarType::hybrid));
    }
    if (const char* tight = "Tight"; stats.sccs == 0) {
        PRINT_KEY_VALUE(tight, "%s\n", "Yes");
    }
    else if (stats.sccs != PrgNode::no_scc) {
        PRINT_KEY_VALUE(tight, "%-8s (SCCs: %u Non-Hcfs: %u Nodes: %u Gammas: %u)\n", "No", stats.sccs, stats.nonHcfs,
                        stats.ufsNodes, stats.gammas);
    }
    else {
        PRINT_KEY_VALUE(tight, "%s\n", "N/A");
    }
}
void TextOutput::printUserStats(const StatisticObject& stats) { printChildren(stats); }
// NOLINTNEXTLINE(misc-no-recursion)
void TextOutput::printChildren(const StatisticObject& s, int level, char const* prefix) {
    const auto map    = s.type() == StatsType::map;
    const auto indent = level * 2;
    for (auto i : irange(s)) {
        const char*     key   = map ? s.key(i) : nullptr;
        StatisticObject child = map ? s.at(key) : s[i];
        if (auto type = child.type(); type == StatsType::array && key) {
            printChildren(child, level, key);
        }
        else {
            printf("%s%-*.*s", format_[cat_comment], indent, indent, " ");
            auto len = key ? printf("%s", key) : printf("[%s%-*s%u]", prefix, *prefix != 0, "", i);
            if (type == StatsType::value) {
                printf("%-*s: %g\n", std::max(0, (width_ - indent) - len), "", child.value());
            }
            else {
                printf("\n");
                printChildren(child, std::min(level, 50) + 1);
            }
        }
    }
}
#undef PRINT_BR
#undef PRINT_COMMENT_LN
#undef PRINT_LN
#undef PRINT_KEY_VALUE
#undef PRINT_IF_LN
} // namespace Clasp::Cli
