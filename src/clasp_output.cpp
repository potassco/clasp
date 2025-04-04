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
#include <cstdarg>
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
Output::Output(uint32_t verb) : time_(-1.0), model_(-1.0) {
    setCallQuiet(print_no);
    setVerbosity(verb);
}
Output::~Output() = default;
void Output::setVerbosity(uint32_t verb) {
    auto x = static_cast<Event::Verbosity>(std::min(verbose_ = verb, static_cast<uint32_t>(Event::verbosity_max)));
    EventHandler::setVerbosity(Event::subsystem_facade, x);
    EventHandler::setVerbosity(Event::subsystem_load, x);
    EventHandler::setVerbosity(Event::subsystem_prepare, x);
    EventHandler::setVerbosity(Event::subsystem_solve, x);
}
void Output::setModelQuiet(PrintLevel model) { quiet_[0] = static_cast<uint8_t>(model); }
void Output::setOptQuiet(PrintLevel opt) { quiet_[1] = static_cast<uint8_t>(opt); }
void Output::setCallQuiet(PrintLevel call) { quiet_[2] = static_cast<uint8_t>(call); }
void Output::onEvent(const Event& ev) {
    using StepStart = ClaspFacade::StepStart;
    using StepReady = ClaspFacade::StepReady;
    if (time_ == -1.0) {
        time_ = RealTime::getTime();
    }
    if (const auto* start = event_cast<StepStart>(ev)) {
        startStep(*start->facade);
    }
    else if (const auto* ready = event_cast<StepReady>(ev)) {
        stopStep(*ready->summary);
    }
}
bool Output::onModel(const Solver& s, const Model& m) {
    PrintLevel type    = (m.opt == 1 && not m.consequences()) || m.def ? print_best : print_all;
    bool       hasMeta = m.consequences() || m.hasCosts();
    model_             = elapsedTime();
    if (modelQ() <= type || (hasMeta && optQ() <= type)) {
        printModel(s.outputTable(), m, type);
    }
    last_ = type != print_best && (modelQ() == print_best || (optQ() == print_best && hasMeta));
    return true;
}
bool Output::onUnsat(const Solver& s, const Model& m) {
    if (m.ctx) {
        auto        lowerBound = m.ctx->lowerBound();
        const auto* prevModel  = m.num ? &m : nullptr;
        if (modelQ() == print_all || optQ() == print_all) {
            printUnsat(s.outputTable(), lowerBound.active() ? &lowerBound : nullptr, prevModel);
        }
    }
    return true;
}
void Output::startStep(const ClaspFacade&) {
    summary_ = nullptr;
    last_    = false;
}
void Output::stopStep(const ClaspFacade::Summary& s) {
    if (s.model() && last_) {
        Model m = *s.model();
        m.up    = 0; // ignore update state and always print as model
        printModel(s.ctx().output, m, print_best);
    }
    else if (modelQ() == print_all && s.model() && s.model()->up && not s.model()->def) {
        printModel(s.ctx().output, *s.model(), print_all);
    }
    if (callQ() == print_all) {
        printSummary(s, false);
        if (stats(s)) {
            printStatistics(s, false);
        }
    }
    else if (callQ() == print_best) {
        summary_ = &s;
    }
}
void Output::shutdown(const ClaspFacade::Summary& summary) {
    if (summary_) {
        printSummary(*summary_, false);
        if (stats(summary)) {
            printStatistics(*summary_, false);
        }
    }
    printSummary(summary, true);
    if (stats(summary)) {
        printStatistics(summary, true);
    }
    shutdown();
    time_ = -1.0;
}
// Returns the number of consequences and estimates in m.
// For a model m with m.consequences and a return value ret:
//   - ret.first  is the number of definite consequences
//   - ret.second is the number of remaining possible consequences
Output::UPair Output::numCons(const OutputTable& out, const Model& m) { return m.numConsequences(out); }

// Prints shown symbols in model.
// The function prints:
// - true literals in definite answer, followed by
// - true literals in current estimate if m.consequences()
void Output::printWitness(const OutputTable& out, const Model& m, uintptr_t data) {
    for (const auto& theory : out.theory_range()) {
        for (const char* x = theory->first(m); x; x = theory->next()) { data = doPrint(OutPair(x, lit_true), data); }
    }
    const bool onlyD = m.type != Model::cautious || m.def;
    for (bool def = true;; def = not def) {
        for (const auto& pred : out.pred_range()) {
            if (m.isTrue(pred.cond) && (onlyD || m.isDef(pred.cond) == def)) {
                data = doPrint(OutPair(pred.name.c_str(), lit_true), data);
            }
        }
        if (not out.vars_range().empty()) {
            const bool showNeg = not m.consequences();
            if (out.projectMode() == ProjectMode::output || not out.filter("_")) {
                for (auto v : out.vars_range()) {
                    Literal p = posLit(v);
                    if ((showNeg || m.isTrue(p)) && (onlyD || m.isDef(p) == def)) {
                        data = doPrint(OutPair(static_cast<const char*>(nullptr), m.isTrue(p) ? p : ~p), data);
                    }
                }
            }
            else {
                for (auto lit : out.proj_range()) {
                    if ((showNeg || m.isTrue(lit)) && (onlyD || m.isDef(lit) == def)) {
                        data = doPrint(OutPair(static_cast<const char*>(nullptr), m.isTrue(lit) ? lit : ~lit), data);
                    }
                }
            }
        }
        if (def == onlyD) {
            return;
        }
    }
}
void      Output::printUnsat(const OutputTable&, const LowerBound*, const Model*) {}
uintptr_t Output::doPrint(const OutPair&, UPtr data) { return data; }
bool      Output::stats(const ClaspFacade::Summary& summary) { return summary.facade->config()->context().stats != 0; }
double    Output::elapsedTime() const { return time_ != -1.0 ? RealTime::getTime() - time_ : -1.0; }
double    Output::modelTime() const { return model_; }
using StatsType = Potassco::StatisticsType;
/////////////////////////////////////////////////////////////////////////////////////////
// JsonOutput
/////////////////////////////////////////////////////////////////////////////////////////
JsonOutput::JsonOutput(uint32_t v) : Output(std::min(v, 1u)), open_("") { objStack_.reserve(10); }
JsonOutput::~JsonOutput() { JsonOutput::shutdown(); }
void JsonOutput::run(const char* solver, const char* version, const std::string* iBeg, const std::string* iEnd) {
    if (indent() == 0) {
        open_ = "";
        pushObject();
    }
    printKeyValue("Solver", std::string(solver).append(" version ").append(version).c_str());
    pushObject("Input", type_array, true);
    for (const char* sep = ""; iBeg != iEnd; ++iBeg, sep = ",") { printString(iBeg->c_str(), sep); }
    popObject();
    pushObject("Call", type_array);
}
void JsonOutput::shutdown() {
    if (!objStack_.empty()) {
        popUntil(0u);
        printf("\n");
        fflush(stdout);
    }
}
void JsonOutput::startStep(const ClaspFacade& f) {
    Output::startStep(f);
    popUntil(2u);
    pushObject(nullptr, type_object);
    printTime("Start", elapsedTime());
    fflush(stdout);
}
void JsonOutput::stopStep(const ClaspFacade::Summary& s) {
    assert(not objStack_.empty());
    Output::stopStep(s);
    popUntil(3u);
    printTime("Stop", elapsedTime());
    if (callQ() != print_best) { // keep call object open for last summary
        popObject();
    }
    fflush(stdout);
}

bool JsonOutput::visitThreads(Operation op) {
    if (op == enter) {
        pushObject("Thread", type_array);
    }
    else if (op == leave) {
        popObject();
    }
    return true;
}
bool JsonOutput::visitTester(Operation op) {
    if (op == enter) {
        pushObject("Tester");
    }
    else if (op == leave) {
        popObject();
    }
    return true;
}
bool JsonOutput::visitHccs(Operation op) {
    if (op == enter) {
        pushObject("HCC", type_array);
    }
    else if (op == leave) {
        popObject();
    }
    return true;
}
void JsonOutput::visitThread(uint32_t, const SolverStats& stats) {
    pushObject(nullptr, type_object);
    JsonOutput::visitSolverStats(stats);
    popObject();
}
void JsonOutput::visitHcc(uint32_t, const ProblemStats& p, const SolverStats& s) {
    pushObject(nullptr, type_object);
    JsonOutput::visitProblemStats(p);
    JsonOutput::visitSolverStats(s);
    popObject();
}

void JsonOutput::visitSolverStats(const SolverStats& stats) {
    printCoreStats(stats);
    if (stats.extra) {
        printExtStats(*stats.extra, objStack_.size() == 2);
        printJumpStats(stats.extra->jumps);
    }
}

void JsonOutput::printChildren(const StatisticObject& s) { // NOLINT(misc-no-recursion)
    for (auto i : irange(s)) {
        const char*     key   = s.type() == StatsType::map ? s.key(i) : nullptr;
        StatisticObject child = key ? s.at(key) : s[i];
        if (child.type() == StatsType::value) {
            printKeyValue(key, child);
        }
        else {
            pushObject(key, child.type() == StatsType::map ? type_object : type_array);
            printChildren(child);
            popObject();
        }
    }
}

void JsonOutput::visitExternalStats(const StatisticObject& stats) {
    POTASSCO_ASSERT(stats.type() == StatsType::map, "Non map statistic!");
    printChildren(stats);
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
void JsonOutput::visitLogicProgramStats(const Asp::LpStats& lp) {
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
void JsonOutput::visitProblemStats(const ProblemStats& p) {
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

void JsonOutput::printKey(const char* k) {
    if (k) {
        printf("%s%-*.*s\"%s\": ", open_, indent(), indent(), " ", k);
    }
    else {
        printf("%s%-*.*s", open_, indent(), indent(), " ");
    }
}

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

void JsonOutput::printKeyValue(const char* k, const char* v) {
    printf("%s%-*s\"%s\": ", open_, indent(), " ", k);
    printString(v, "");
    open_ = ",\n";
}
void JsonOutput::printKeyValue(const char* k, uint64_t v) {
    printf("%s%-*s\"%s\": %" PRIu64, open_, indent(), " ", k, v);
    open_ = ",\n";
}
void JsonOutput::printKeyValue(const char* k, uint32_t v) { return printKeyValue(k, static_cast<uint64_t>(v)); }
void JsonOutput::printKeyValue(const char* k, double v) {
    if (not std::isnan(v)) {
        printf("%s%-*s\"%s\": %.3f", open_, indent(), " ", k, v);
    }
    else {
        printf("%s%-*s\"%s\": %s", open_, indent(), " ", k, "null");
    }
    open_ = ",\n";
}
void JsonOutput::printKeyValue(const char* k, const StatisticObject& o) {
    double v = o.value();
    printKey(k);
    if (not std::isnan(v)) {
        printf("%g", v);
    }
    else {
        printf("%s", "null");
    }
    open_ = ",\n";
}

void JsonOutput::pushObject(const char* k, ObjType t, bool startIndent) {
    printKey(k);
    char o     = t == type_object ? '{' : '[';
    objStack_ += o;
    printf("%c\n", o);
    open_ = "";
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
    if (not hasWitnesses()) {
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
uintptr_t JsonOutput::doPrint(const OutPair& out, uintptr_t data) {
    const char* sep = reinterpret_cast<const char*>(data);
    if (out.first) {
        printString(out.first, sep);
    }
    else {
        printf("%s%d", sep,
               out.second.sign() ? -static_cast<int>(out.second.var()) : static_cast<int>(out.second.var()));
    }
    return reinterpret_cast<UPtr>(", ");
}
void JsonOutput::printModel(const OutputTable& out, const Model& m, PrintLevel x) {
    auto onEnter = objStack_.size();
    if (modelQ() <= x) {
        startWitness(modelTime());
        pushObject("Value", type_array, true);
        printWitness(out, m, reinterpret_cast<UPtr>(""));
        popObject();
    }
    if (optQ() <= x && (m.consequences() || m.hasCosts())) {
        if (objStack_.size() == onEnter) {
            startWitness(modelTime());
        }
        if (m.consequences()) {
            printCons(numCons(out, m));
        }
        if (m.hasCosts()) {
            printCosts(m.costs);
        }
    }
    if (objStack_.size() != onEnter) {
        endWitness();
    }
}
void JsonOutput::printUnsat(const OutputTable&, const LowerBound* lower, const Model* prevModel) {
    if (lower && optQ() == print_all) {
        startWitness(elapsedTime());
        auto first = SumView();
        if (prevModel && prevModel->hasCosts() && prevModel->costs.size() > lower->level) {
            first = prevModel->costs.subspan(0, lower->level);
        }
        printSum("Lower", first, &lower->bound);
        endWitness();
    }
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
void JsonOutput::printCons(const UPair& cons) {
    pushObject("Consequences");
    printKeyValue("True", cons.first);
    printKeyValue("Open", cons.second);
    popObject();
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
                printCons(numCons(run.ctx().output, *run.model()));
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
void JsonOutput::printStatistics(const ClaspFacade::Summary& summary, bool final) {
    popUntil(final ? 1u : 3u);
    pushObject("Stats", type_object);
    summary.accept(*this);
    popObject();
}
void JsonOutput::printTime(const char* name, double t) {
    if (t >= 0.0) {
        printKeyValue(name, t);
    }
}
/////////////////////////////////////////////////////////////////////////////////////////
// TextOutput
/////////////////////////////////////////////////////////////////////////////////////////
#define PRINT_KEY_VALUE(k, fmt, value)   printf("%s%-*s: " fmt, format[cat_comment], width_, (k), (value))
#define PRINT_S_KEY_VALUE(k, fmt, value) printf("  %s%-*s: " fmt, format[cat_comment], width_ - 2, (k), (value))
#define PRINT_LN(cat, fmt, ...)          printf("%s" fmt "\n", format[cat], __VA_ARGS__)
#define PRINT_BR(cat)                    printf("%s\n", format[cat])
#define PRINT_KEY(k)                     printf("%s%-*s: ", format[cat_comment], width_, (k))
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
    result[res_unknown]    = "UNKNOWN";
    result[res_sat]        = "SATISFIABLE";
    result[res_unsat]      = "UNSATISFIABLE";
    result[res_opt]        = "OPTIMUM FOUND";
    format[cat_comment]    = "";
    format[cat_value]      = "";
    format[cat_objective]  = "Optimization: ";
    format[cat_result]     = "";
    format[cat_value_term] = "";
    format[cat_atom_name]  = "%s";
    format[cat_atom_var]   = "-%d";
    if (fmt == format_aspcomp) {
        format[cat_comment]   = "% ";
        format[cat_value]     = "ANSWER\n";
        format[cat_objective] = "COST ";
        format[cat_atom_name] = "%s.";
        result[res_sat]       = "";
        result[res_unsat]     = "INCONSISTENT";
        result[res_opt]       = "OPTIMUM";
        setModelQuiet(print_best);
        setOptQuiet(print_best);
    }
    else if (fmt == format_sat09 || fmt == format_pb09) {
        format[cat_comment]    = "c ";
        format[cat_value]      = "v ";
        format[cat_objective]  = "o ";
        format[cat_result]     = "s ";
        format[cat_value_term] = "0";
        if (fmt == format_pb09) {
            format[cat_value_term] = "";
            format[cat_atom_var]   = "-x%d";
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
            auto p                = fmt_.find("%0") + 1;
            fmt_[p]               = 's';
            fmt_[len + 2 + p]     = 'd';
            format[cat_atom_name] = fmt_.c_str();
            format[cat_atom_var]  = fmt_.c_str() + len + 1;
        }
        else {
            format[f == 's' ? cat_atom_name : cat_atom_var] = catAtom;
        }
    }
    POTASSCO_CHECK_PRE(*format[cat_atom_var] == '-', "cat_atom: Invalid format string - must start with '-'");
    ifs_[0] = ifs;
    ifs_[1] = 0;
    width_  = 13 + static_cast<int>(strlen(format[cat_comment]));
    progress_.clear();
}
TextOutput::~TextOutput() = default;

void TextOutput::comment(uint32_t v, const char* fmt, ...) const {
    if (verbosity() >= v) {
        printf("%s", format[cat_comment]);
        POTASSCO_WARNING_PUSH()
        POTASSCO_WARNING_IGNORE_CLANG("-Wformat-nonliteral")
        va_list args;
        va_start(args, fmt);
        vfprintf(stdout, fmt, args);
        va_end(args);
        POTASSCO_WARNING_POP()
        fflush(stdout);
    }
}

void TextOutput::run(const char* solver, const char* version, const std::string* begInput,
                     const std::string* endInput) {
    if (solver) {
        comment(1, "%s version %s\n", solver, version ? version : "");
    }
    if (begInput != endInput) {
        comment(1, "Reading from %s%s\n", prettify(*begInput).c_str(), (endInput - begInput) > 1 ? " ..." : "");
    }
}
void TextOutput::shutdown() {}
void TextOutput::printSummary(const ClaspFacade::Summary& run, bool final) {
    if (final && callQ() != print_no) {
        comment(1, "%s\n", acc_sep);
    }
    const char* res = result[res_unknown];
    if (run.unsat()) {
        res = result[res_unsat];
    }
    else if (run.sat()) {
        res = not run.optimum() ? result[res_sat] : result[res_opt];
    }
    if (*res) {
        PRINT_LN(cat_result, "%s", res);
    }
    if (verbosity() || stats(run)) {
        PRINT_BR(cat_comment);
        if (run.result.interrupted()) {
            PRINT_KEY_VALUE((run.result.signal != SIGALRM ? "INTERRUPTED" : "TIME LIMIT"), "%u\n", 1u);
        }
        const char* const moreStr = run.complete() ? "" : "+";
        PRINT_KEY("Models");
        printf("%" PRIu64 "%s\n", run.numEnum, moreStr);
        if (run.sat()) {
            if (run.consequences()) {
                PRINT_LN(cat_comment, "  %-*s: %s", width_ - 2, run.consequences(),
                         (run.complete() ? "yes" : "unknown"));
            }
            if (run.hasCosts()) {
                PRINT_KEY_VALUE("  Optimum", "%s\n", run.optimum() ? "yes" : "unknown");
            }
            if (run.optimize()) {
                if (run.optimal() > 1) {
                    PRINT_KEY_VALUE("  Optimal", "%" PRIu64 "\n", run.optimal());
                }
                PRINT_KEY("Optimization");
                printCostsImpl(run.costs(), ' ');
                printf("\n");
            }
            if (run.consequences()) {
                PRINT_KEY("Consequences");
                printf("%u%s\n", numCons(run.ctx().output, *run.model()).first, moreStr);
            }
        }
        if (run.hasLower() && not run.optimum()) {
            PRINT_KEY("Bounds");
            printBounds(run.lower(), run.costs());
            printf("\n");
        }
        if (final) {
            PRINT_KEY_VALUE("Calls", "%u\n", run.step + 1);
        }
        PRINT_KEY("Time");
        printf("%.3fs (Solving: %.2fs 1st Model: %.2fs Unsat: %.2fs)\n", run.totalTime, run.solveTime, run.satTime,
               run.unsatTime);
        PRINT_KEY_VALUE("CPU Time", "%.3fs\n", run.cpuTime);
        if (run.ctx().concurrency() > 1) {
            PRINT_KEY_VALUE("Threads", "%-8u", run.ctx().concurrency());
            printf(" (Winner: %u)\n", run.ctx().winner());
        }
    }
}
void TextOutput::printStatistics(const ClaspFacade::Summary& run, bool) {
    PRINT_BR(cat_comment);
    accu_ = true;
    run.accept(*this);
}
void TextOutput::startStep(const ClaspFacade& f) {
    Output::startStep(f);
    setState(Event::subsystem_facade, 0, nullptr);
    if (callQ() != print_no) {
        comment(1, "%s\n", row_sep);
        comment(2, "%-13s: %d\n", "Call", f.step() + 1);
    }
}
void TextOutput::stopStep(const ClaspFacade::Summary& s) {
    setState(Event::subsystem_facade, 0, nullptr);
    comment(2 - (callQ() != print_no), "%s\n", row_sep);
    Output::stopStep(s);
}
void TextOutput::onEvent(const Event& ev) {
    using SatPre = SatElite::Progress;
    if (ev.verb <= verbosity() && ev.system != Event::subsystem_facade) {
        if (ev.system == state_) {
            if (ev.system == Event::subsystem_solve) {
                printSolveProgress(ev);
            }
            else if (const auto* sat = event_cast<SatPre>(ev)) {
                if (sat->op != SatElite::Progress::event_algorithm) {
                    comment(2, "%-13s: %c: %8u/%-8u\r", sat_pre, static_cast<char>(sat->op), sat->cur, sat->max);
                }
                else if (sat->cur != sat->max) {
                    setState(ev.system, 2, sat_pre);
                }
                else {
                    auto*  p    = sat->self;
                    double tEnd = RealTime::getTime();
                    comment(2, "%-13s: %.3fs (ClRemoved: %u ClAdded: %u LitsStr: %u)\n", sat_pre, tEnd - stTime_,
                            p->stats.clRemoved, p->stats.clAdded, p->stats.litsRemoved);
                    state_ = Event::subsystem_facade;
                }
            }
        }
        else if (const auto* log = event_cast<LogEvent>(ev)) {
            setState(ev.system, ev.verb, log->msg);
        }
    }
    Output::onEvent(ev);
}

void TextOutput::setState(uint32_t state, uint32_t verb, const char* m) {
    double ts = RealTime::getTime();
    if (verb <= verbosity()) {
        if (state_ == Event::subsystem_load || state_ == Event::subsystem_prepare) {
            printf("%.3fs\n", ts - stTime_);
        }
        if (state == Event::subsystem_load) {
            comment(2, "%-13s: ", m ? m : "Reading");
        }
        else if (state == Event::subsystem_prepare) {
            comment(2, "%-13s:%s", m ? m : "Preprocessing", m == sat_pre ? "\r" : " ");
        }
        else if (state == Event::subsystem_solve) {
            comment(1, "Solving...\n");
        }
    }
    progress_.clear();
    stTime_ = ts;
    state_  = state;
}

void TextOutput::printSolveProgress(const Event& ev) {
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
        snprintf(tb, std::size(tb), "[Solving+%.3fs]", RealTime::getTime() - stTime_);
        written = snprintf(buffer.data(), buffer.size(), "%2u:L| %-30s %-38.38s |", log->solver->id(), tb, log->msg);
    }
    if (written < 0 || static_cast<std::size_t>(written) >= buffer.size()) {
        return;
    }
    buffer = buffer.subspan(static_cast<std::size_t>(written));
    snprintf(buffer.data(), buffer.size(), " %10.3fs |", elapsedTime());
    FileLock lock(stdout);
    if (progress_.lines <= 0 || eventId != progress_.last) {
        if (progress_.lines <= 0) {
            const char* prefix = format[cat_comment];
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
    printf("%s%s%c", format[cat_comment], line, lEnd);
}

const char* TextOutput::getIfsSuffix(char ifs, CategoryKey c) const {
    return ifs != '\n' || std::string_view(format[c]).ends_with('\n') ? "" : format[c];
}
const char* TextOutput::getIfsSuffix(CategoryKey c) const { return getIfsSuffix(ifs_[0], c); }
const char* TextOutput::fieldSeparator() const { return ifs_; }
bool        TextOutput::clearProgress(int nLines) {
    if (progress_.last != -1) {
        if (progress_.last != INT_MAX) {
            progress_.last = INT_MAX;
            comment(2, "%s\n", row_sep);
        }
        progress_.lines -= nLines;
        return true;
    }
    return false;
}
int       TextOutput::printSep(CategoryKey k) const { return printf("%s%s", fieldSeparator(), getIfsSuffix(k)); }
uintptr_t TextOutput::doPrint(const OutPair& s, UPtr data) {
    constexpr uint32_t msb     = 31u;
    uint32_t&          accu    = reinterpret_cast<UPair*>(data)->first;
    uint32_t&          maxLine = reinterpret_cast<UPair*>(data)->second;
    if (accu == 0 && *getIfsSuffix(cat_value)) {
        Potassco::store_set_bit(accu, msb);
    }
    const char* suf = Potassco::test_bit(accu, msb) ? format[cat_value] : "";
    Potassco::store_clear_bit(accu, msb);
    if (accu < maxLine) {
        accu += static_cast<unsigned>(printf("%c%s", *fieldSeparator(), suf));
    }
    else if (not maxLine) {
        maxLine = s.first || *fieldSeparator() != ' ' ? UINT32_MAX : 70;
    }
    else {
        printf("%c%s", '\n', getIfsSuffix('\n', cat_value));
        accu = 0;
    }
    POTASSCO_WARNING_PUSH()
    POTASSCO_WARNING_IGNORE_GNU("-Wformat-nonliteral") // format not a string literal
    if (s.first) {
        accu += static_cast<unsigned>(printf(format[cat_atom_name], s.first));
    }
    else {
        accu +=
            static_cast<unsigned>(printf(format[cat_atom_var] + not s.second.sign(), static_cast<int>(s.second.var())));
    }
    POTASSCO_WARNING_POP()
    if (*suf) {
        Potassco::store_set_bit(accu, msb);
    }
    return data;
}
void TextOutput::printValues(const OutputTable& out, const Model& m) {
    printf("%s", format[cat_value]);
    UPair data;
    printWitness(out, m, reinterpret_cast<UPtr>(&data));
    if (*format[cat_value_term]) {
        printf("%c%s%s", *fieldSeparator(), getIfsSuffix(cat_value), format[cat_value_term]);
    }
    printf("\n");
}
void TextOutput::printMeta(const OutputTable& out, const Model& m) {
    if (m.consequences()) {
        UPair cons = numCons(out, m);
        PRINT_LN(cat_comment, "Consequences: [%u;%u]", cons.first, cons.first + cons.second);
    }
    if (m.hasCosts()) {
        printf("%s", format[cat_objective]);
        printCosts(m.costs);
        printf("\n");
    }
}

void TextOutput::printModelValues(const OutputTable& out, const Model& m) { printValues(out, m); }

void TextOutput::printModel(const OutputTable& out, const Model& m, PrintLevel x) {
    FileLock lock(stdout);
    bool     printValues = modelQ() <= x;
    bool     printOpt    = optQ() <= x;
    if (printValues || printOpt) {
        const char* type = not m.up ? "Answer" : "Update";
        clearProgress(3);
        comment(1, "%s: %" PRIu64 " (Time: %.3fs)\n", type, m.num, modelTime());
        if (printValues) {
            printModelValues(out, m);
        }
        if (printOpt) {
            printMeta(out, m);
        }
    }
}
void TextOutput::printUnsat(const OutputTable& out, const LowerBound* lower, const Model* prevModel) {
    FileLock lock(stdout);
    if (lower && optQ() == print_all) {
        auto   costs = prevModel ? prevModel->costs : SumView{};
        double ts    = elapsedTime();
        clearProgress(1);
        comment(0, "%-12s: ", "Progression");
        if (costs.size() > lower->level) {
            for (auto i : irange(lower->level)) { printf("%" PRId64 " ", costs[i]); }
            Wsum_t ub = costs[lower->level];
            int    w  = 1;
            for (Wsum_t x = ub; x > 9; ++w) { x /= 10; }
            double err = static_cast<double>(ub - lower->bound) / static_cast<double>(lower->bound);
            if (err < 0) {
                err = -err;
            }
            printf("[%*" PRId64 ";%" PRId64 "] (Error: %g ", w, lower->bound, ub, err);
        }
        else {
            printf("[%6" PRId64 ";inf] (", lower->bound);
        }
        printf("Time: %.3fs)\n", ts);
    }
    if (prevModel && prevModel->up && optQ() == print_all) {
        printMeta(out, *prevModel);
    }
}

void TextOutput::printBounds(SumView lower, SumView upper) const {
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

void TextOutput::printCosts(SumView costs) const {
    printCostsImpl(costs, *fieldSeparator(), getIfsSuffix(cat_objective));
}

void TextOutput::printCostsImpl(SumView costs, char ifs, const char* ifsSuffix) const {
    if (not costs.empty()) {
        printf("%" PRId64, costs[0]);
        for (auto w : costs.subspan(1)) { printf("%c%s%" PRId64, ifs, ifsSuffix, w); }
    }
}
bool TextOutput::startSection(const char* n) const {
    PRINT_LN(cat_comment, "============ %s Stats ============", n);
    PRINT_BR(cat_comment);
    return true;
}
void TextOutput::startObject(const char* n, uint32_t i) const {
    PRINT_LN(cat_comment, "[%s %u]", n, i);
    PRINT_BR(cat_comment);
}
bool TextOutput::visitThreads(Operation op) {
    accu_ = false;
    return op != enter || startSection("Thread");
}
bool TextOutput::visitTester(Operation op) {
    accu_ = false;
    return op != enter || startSection("Tester");
}
void TextOutput::visitThread(uint32_t i, const SolverStats& stats) {
    startObject("Thread", i);
    TextOutput::visitSolverStats(stats);
}
void TextOutput::visitHcc(uint32_t i, const ProblemStats& p, const SolverStats& s) {
    startObject("HCC", i);
    TextOutput::visitProblemStats(p);
    TextOutput::visitSolverStats(s);
}
void TextOutput::visitLogicProgramStats(const Asp::LpStats& lp) {
    using namespace Asp;
    uint32_t rFinal = lp.rules[1].sum(), rOriginal = lp.rules[0].sum();
    PRINT_KEY_VALUE("Rules", "%-8u", rFinal);
    if (rFinal != rOriginal) {
        printf(" (Original: %u)", rOriginal);
    }
    printf("\n");
    for (auto i : irange(RuleStats::numKeys())) {
        if (i == RuleStats::normal) {
            continue;
        }
        if (uint32_t r = lp.rules[0][i]) {
            PRINT_S_KEY_VALUE(RuleStats::toStr(i), "%-8u", lp.rules[1][i]);
            if (r != lp.rules[1][i]) {
                printf(" (Original: %u)", r);
            }
            printf("\n");
        }
    }
    PRINT_KEY_VALUE("Atoms", "%-8u", lp.atoms);
    if (lp.auxAtoms) {
        printf(" (Original: %u Auxiliary: %u)", lp.atoms - lp.auxAtoms, lp.auxAtoms);
    }
    printf("\n");
    if (lp.disjunctions[0]) {
        PRINT_KEY_VALUE("Disjunctions", "%-8u", lp.disjunctions[1]);
        printf(" (Original: %u)\n", lp.disjunctions[0]);
    }
    uint32_t bFinal = lp.bodies[1].sum(), bOriginal = lp.bodies[0].sum();
    PRINT_KEY_VALUE("Bodies", "%-8u", bFinal);
    if (bFinal != bOriginal) {
        printf(" (Original: %u)", bOriginal);
    }
    printf("\n");
    for (auto i : irange(1u, BodyStats::numKeys())) {
        if (uint32_t b = lp.bodies[0][i]) {
            PRINT_S_KEY_VALUE(BodyStats::toStr(i), "%-8u", lp.bodies[1][i]);
            if (b != lp.bodies[1][i]) {
                printf(" (Original: %u)", b);
            }
            printf("\n");
        }
    }
    if (lp.eqs() > 0) {
        PRINT_KEY_VALUE("Equivalences", "%-8u", lp.eqs());
        printf(" (Atom=Atom: %u Body=Body: %u Other: %u)\n", lp.eqs(VarType::atom), lp.eqs(VarType::body),
               lp.eqs(VarType::hybrid));
    }
    PRINT_KEY("Tight");
    if (lp.sccs == 0) {
        printf("Yes");
    }
    else if (lp.sccs != PrgNode::no_scc) {
        printf("%-8s (SCCs: %u Non-Hcfs: %u Nodes: %u Gammas: %u)", "No", lp.sccs, lp.nonHcfs, lp.ufsNodes, lp.gammas);
    }
    else {
        printf("N/A");
    }
    printf("\n");
}
void TextOutput::visitProblemStats(const ProblemStats& ps) {
    uint32_t sum = ps.numConstraints();
    PRINT_KEY_VALUE("Variables", "%-8u", ps.vars.num);
    printf(" (Eliminated: %4u Frozen: %4u)\n", ps.vars.eliminated, ps.vars.frozen);
    PRINT_KEY_VALUE("Constraints", "%-8u", sum);
    printf(" (Binary: %5.1f%% Ternary: %5.1f%% Other: %5.1f%%)\n", percent(ps.constraints.binary, sum),
           percent(ps.constraints.ternary, sum), percent(ps.constraints.other, sum));
    if (ps.acycEdges) {
        PRINT_KEY_VALUE("Acyc-Edges", "%-8u\n", ps.acycEdges);
    }
    PRINT_BR(cat_comment);
}
void TextOutput::visitSolverStats(const SolverStats& st) {
    printStats(st);
    PRINT_BR(cat_comment);
}

int TextOutput::printChildKey(unsigned level, const char* key, uint32_t idx, const char* prefix) const {
    const unsigned indent = level * 2;
    int            len;
    printf("%s%-*.*s", format[cat_comment], indent, indent, " ");
    if (key) {
        len = printf("%s", key);
    }
    else if (prefix) {
        len = printf("[%s %u]", prefix, idx);
    }
    else {
        len = printf("[%u]", idx);
    }
    return (width_ - static_cast<int>(indent)) - len;
}

// NOLINTNEXTLINE(misc-no-recursion)
void TextOutput::printChildren(const StatisticObject& s, unsigned level, char const* prefix) {
    const bool map = s.type() == StatsType::map;
    for (auto i : irange(s)) {
        const char*     key   = map ? s.key(i) : nullptr;
        StatisticObject child = map ? s.at(key) : s[i];
        if (child.type() == StatsType::value) {
            int align = printChildKey(level, key, i, prefix);
            printf("%-*s: %g\n", std::max(0, align), "", child.value());
        }
        else if (child.type() == StatsType::array && key) {
            printChildren(child, level, key);
        }
        else {
            std::ignore = printChildKey(level, key, i, prefix);
            printf("\n");
            printChildren(child, level + 1);
        }
    }
}

void TextOutput::visitExternalStats(const StatisticObject& stats) {
    POTASSCO_ASSERT(stats.type() == StatsType::map, "Non map statistic!");
    printChildren(stats);
}

void TextOutput::printStats(const SolverStats& st) const {
    if (not accu_ && st.extra) {
        PRINT_KEY_VALUE("CPU Time", "%.3fs\n", st.extra->cpuTime);
        PRINT_KEY_VALUE("Models", "%" PRIu64 "\n", st.extra->models);
    }
    PRINT_KEY_VALUE("Choices", "%-8" PRIu64, st.choices);
    if (st.extra && st.extra->domChoices) {
        printf(" (Domain: %" PRIu64 ")", st.extra->domChoices);
    }
    printf("\n");
    PRINT_KEY_VALUE("Conflicts", "%-8" PRIu64 "", st.conflicts);
    printf(" (Analyzed: %" PRIu64 ")\n", st.backjumps());
    PRINT_KEY_VALUE("Restarts", "%-8" PRIu64 "", st.restarts);
    if (st.restarts) {
        printf(" (Average: %.2f Last: %" PRIu64 " Blocked: %" PRIu64 ")", st.avgRestart(), st.lastRestart,
               st.blRestarts);
    }
    printf("\n");
    if (not st.extra) {
        return;
    }
    const ExtendedStats& stx = *st.extra;
    if (stx.hccTests) {
        PRINT_KEY_VALUE("Stab. Tests", "%-8" PRIu64, stx.hccTests);
        printf(" (Full: %" PRIu64 " Partial: %" PRIu64 ")\n", stx.hccTests - stx.hccPartial, stx.hccPartial);
    }
    if (stx.models) {
        PRINT_KEY_VALUE("Model-Level", "%-8.1f\n", stx.avgModel());
    }
    PRINT_KEY_VALUE("Problems", "%-8" PRIu64, static_cast<uint64_t>(stx.gps));
    printf(" (Average Length: %.2f Splits: %" PRIu64 ")\n", stx.avgGp(), static_cast<uint64_t>(stx.splits));
    uint64_t sum = stx.lemmas();
    PRINT_KEY_VALUE("Lemmas", "%-8" PRIu64, sum);
    printf(" (Deleted: %" PRIu64 ")\n", stx.deleted);
    PRINT_KEY_VALUE("  Binary", "%-8" PRIu64, static_cast<uint64_t>(stx.binary));
    printf(" (Ratio: %6.2f%%)\n", percent(stx.binary, sum));
    PRINT_KEY_VALUE("  Ternary", "%-8" PRIu64, static_cast<uint64_t>(stx.ternary));
    printf(" (Ratio: %6.2f%%)\n", percent(stx.ternary, sum));
    const char* names[] = {"  Conflict", "  Loop", "  Other"};
    for (auto i : irange(names)) {
        auto type = static_cast<ConstraintType>(i + 1);
        PRINT_KEY_VALUE(names[i], "%-8" PRIu64, stx.lemmas(type));
        printf(" (Average Length: %6.1f Ratio: %6.2f%%) \n", stx.avgLen(type), percent(stx.lemmas(type), sum));
    }
    if (stx.distributed || stx.integrated) {
        PRINT_KEY_VALUE("  Distributed", "%-8" PRIu64, stx.distributed);
        printf(" (Ratio: %6.2f%% Average LBD: %.2f) \n", stx.distRatio() * 100.0, stx.avgDistLbd());
        PRINT_KEY_VALUE("  Integrated", "%-8" PRIu64, stx.integrated);
        if (accu_) {
            printf(" (Ratio: %6.2f%% ", stx.intRatio() * 100.0);
        }
        else {
            printf(" (");
        }
        printf("Unit: %" PRIu64 " Average Jumps: %.2f)\n", stx.intImps, stx.avgIntJump());
    }
    printJumps(stx.jumps);
}
void TextOutput::printJumps(const JumpStats& st) const {
    PRINT_KEY_VALUE("Backjumps", "%-8" PRIu64, st.jumps);
    printf(" (Average: %5.2f Max: %3u Sum: %6" PRIu64 ")\n", st.avgJump(), st.maxJump, st.jumpSum);
    PRINT_KEY_VALUE("  Executed", "%-8" PRIu64, st.jumps - st.bounded);
    printf(" (Average: %5.2f Max: %3u Sum: %6" PRIu64 " Ratio: %6.2f%%)\n", st.avgJumpEx(), st.maxJumpEx, st.jumped(),
           st.jumpedRatio() * 100.0);
    PRINT_KEY_VALUE("  Bounded", "%-8" PRIu64, st.bounded);
    printf(" (Average: %5.2f Max: %3u Sum: %6" PRIu64 " Ratio: %6.2f%%)\n", st.avgBound(), st.maxBound, st.boundSum,
           100.0 - (st.jumpedRatio() * 100.0));
}

#undef PRINT_KEY_VALUE
#undef PRINT_S_KEY_VALUE
#undef PRINT_KEY
#undef PRINT_LN
#undef PRINT_BR
} // namespace Clasp::Cli
