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

#include <potassco/format.h>

#include <clasp/solver.h>
#include <clasp/util/timer.h>

#include <chrono>
#include <cmath>
#include <cstdarg>
#include <cstdio>
using namespace std::literals;

static const char* signalName(int signal) {
    switch (signal) {
        case 1 : return "SIGHUP";
        case 2 : return "SIGINT";
        case 3 : return "SIGQUIT";
        case 4 : return "SIGILL";
        case 5 : return "SIGTRAP";
        case 6 : return "SIGABRT";
        case 7 : return "SIGBUS";
        case 9 : return "SIGKILL";
        case 10: return "SIGUSR1";
        case 11: return "SIGSEGV";
        case 12: return "SIGUSR2";
        case 13: return "SIGPIPE";
        case 14: return "SIGALRM";
        case 15: return "SIGTERM";
        case 16: return "SIGSTKFLT";
        case 17: return "SIGCHLD";
        default: return "";
    }
}
namespace Clasp::Cli {
namespace {
template <auto S = 128 - sizeof(Potassco::DynamicBuffer)>
class TmpBuffer { // NOLINT
public:
    TmpBuffer() = default; // NOLINT
    void push(char c) { buffer_.push(c); }
    auto back() -> char& { return buffer_.back(); }
    auto append(std::string_view v) -> TmpBuffer& {
        buffer_.append(v);
        return *this;
    }
    [[nodiscard]] auto data() const noexcept -> char* { return buffer_.data(); }
    [[nodiscard]] auto view() const noexcept -> std::string_view { return buffer_.view(); }
    [[nodiscard]] auto rep() noexcept -> Potassco::DynamicBuffer& { return buffer_; }
    [[nodiscard]] auto empty() const noexcept -> bool { return buffer_.size() == 0; }
    [[nodiscard]] auto size() const noexcept -> uint32_t { return buffer_.size(); }

private:
    char                    mem_[S];
    Potassco::DynamicBuffer buffer_{mem_};
};
} // namespace

void printf(struct printf_is_probably_not_intended); // poison printf
/////////////////////////////////////////////////////////////////////////////////////////
// Event formatting
/////////////////////////////////////////////////////////////////////////////////////////
using ModelNum = std::pair<uint64_t, bool>;
static std::size_t formatEvent(Potassco::DynamicBuffer& buffer, const BasicSolveEvent& ev) {
    const Solver& s = *ev.solver;
    return Potassco::formatTo(buffer, "%2u:%c|%7u/%-7u|%8u/%-8u|%10" PRIu64 "/%-6.3f|%8" PRId64 "/%-10" PRId64 "|",
                              s.id(), static_cast<char>(ev.op), s.numFreeVars(),
                              s.decisionLevel() > 0 ? s.levelStart(1) : s.numAssignedVars(), s.numConstraints(),
                              s.numLearntConstraints(), s.stats.conflicts, ratio(s.stats.conflicts, s.stats.choices),
                              ev.cLimit <= UINT32_MAX ? static_cast<int64_t>(ev.cLimit) : -1,
                              ev.lLimit != UINT32_MAX ? static_cast<int64_t>(ev.lLimit) : -1);
}

static std::size_t formatEvent(Potassco::DynamicBuffer& buffer, const SolveTestEvent& ev) {
    return Potassco::formatTo(buffer, "%2u:%c| %c HCC: %-6u |%8u/%-8u|%10" PRIu64 "/%-6.3f| Time: %10.3fs |",
                              ev.solver->id(), "FP"[ev.partial], "?NY"[Clasp::clamp(ev.result, -1, 1) + 1], ev.hcc,
                              ev.solver->numConstraints(), ev.solver->numLearntConstraints(), ev.conflicts(),
                              ratio(ev.conflicts(), ev.choices()), ev.time);
}
#if CLASP_HAS_THREADS
static std::size_t formatEvent(Potassco::DynamicBuffer& buffer, const mt::MessageEvent& ev) {
    using EventType = mt::MessageEvent;
    if (ev.op != EventType::completed) {
        return Potassco::formatTo(buffer, "%2u:X| %-30.30s %-38s |", ev.solver->id(), ev.msg,
                                  ev.op == EventType::sent ? "sent" : "received");
    }
    return Potassco::formatTo(buffer, "%2u:X| %-30.30s %-20s in %13.3fs |", ev.solver->id(), ev.msg, "completed",
                              ev.time);
}
#endif
/////////////////////////////////////////////////////////////////////////////////////////
// Output
/////////////////////////////////////////////////////////////////////////////////////////
static bool stats(const ClaspFacade::Summary& summary) {
    return summary.facade && summary.facade->config() && summary.facade->config()->context().stats;
}
static auto interruptedString(const ClaspFacade::Result& r) -> const char* {
    return r.signal != SIGALRM ? "INTERRUPTED" : "TIME LIMIT";
}
template <typename S>
static auto formatCosts(const S& costs, char ifs = ' ', const char* ifsSuffix = "") -> TmpBuffer<> {
    TmpBuffer<> buf;
    for (auto w : costs) {
        if (not buf.empty()) {
            buf.push(ifs);
            buf.append(ifsSuffix);
        }
        Potassco::toChars(buf, w);
    }
    buf.push(0);
    return buf;
}
Output::Output(FILE* sink, uint32_t verb) : sink_(sink) {
    POTASSCO_CHECK(sink, std::errc::bad_file_descriptor, "invalid output sink");
    result_[res_unknown] = "UNKNOWN";
    result_[res_sat]     = "SATISFIABLE";
    result_[res_unsat]   = "UNSATISFIABLE";
    result_[res_opt]     = "OPTIMUM FOUND";
    setCallQuiet(print_no);
    setVerbosity(verb);
    std::fill_n(style_, num_col, "");
    time_.start = RealTime::getTime();
}
Output::~Output() = default;
void Output::setVerbosity(uint32_t verb) { verbose_ = verb; }
void Output::setModelQuiet(PrintLevel model) { quiet_[0] = static_cast<uint8_t>(model); }
void Output::setOptQuiet(PrintLevel opt) { quiet_[1] = static_cast<uint8_t>(opt); }
void Output::setCallQuiet(PrintLevel call) { quiet_[2] = static_cast<uint8_t>(call); }
auto Output::elapsedTime() const -> ElapsedTime { return ElapsedTime{RealTime::getTime() - time_.start}; }
auto Output::diffTime(double end, double start) -> ElapsedTime { return ElapsedTime{Clasp::diffTime(end, start)}; }
void Output::resetStateTime() { time_.enter = RealTime::getTime(); }
int  Output::print(const char* format, ...) {
    std::va_list args;
    va_start(args, format);
    auto ret = vfprintf(sink_, format, args);
    va_end(args);
    return ret;
}
void Output::flush() { fflush(sink_); }
auto Output::lockSink() -> FileLock {
    Potassco::lockFile(sink_);
    return FileLock{sink_, +[](FILE* f) {
                        fflush(f);
                        Potassco::unlockFile(f);
                    }};
}
auto Output::enableColor(bool enable, std::string_view style) -> std::errc {
    using namespace std::literals;
    std::fill_n(style_, num_col, "");
    if (enable) {
        if (auto ec = Potassco::enableAnsiColorSupport(sink_); ec != std::errc{}) {
            return ec;
        }
        colorStyle_.clear();
        style_[col_trace]          = "\033[0;95m"; // Light-Pink
        style_[col_info]           = "\033[1;32m"; // Bold-Green
        style_[col_note]           = "\033[0;93m"; // Light-Yellow
        style_[col_warn]           = "\033[1;93m"; // Bold-Light-Yellow
        style_[col_err]            = "\033[1;31m"; // Bold-Red
        style_[col_reset]          = "\033[0m";    // Reset all styles
        static constexpr auto keys = {"default="sv, "trace="sv, "info="sv, "note="sv, "warning="sv, "error="sv};
        if (not style.empty()) {
            colorStyle_.reserve(style.size());
            colorStyle_.clear();
            const char* d = colorStyle_.data();
            while (not style.empty()) {
                auto kIt = std::ranges::find_if(keys, [&](std::string_view k) { return style.starts_with(k); });
                POTASSCO_CHECK(kIt != keys.end(), std::errc::invalid_argument, "unknown color key '%" PRIsv "'",
                               PRI_SV(style));
                auto        colKey    = static_cast<ColorStyle>(std::distance(keys.begin(), kIt));
                auto        value     = style.substr(kIt->size());
                const auto* ansiStyle = colorStyle_.data() + colorStyle_.size();
                colorStyle_.append("\033[");
                for (unsigned n = 0, grp = 0; not value.empty(); value.remove_prefix(1)) {
                    if (std::isdigit(static_cast<unsigned char>(value.front()))) {
                        n = (n * 10) + static_cast<unsigned>(value.front() - '0');
                        POTASSCO_CHECK(n < 256, std::errc::invalid_argument, "number out of range in '%" PRIsv "'",
                                       PRI_SV(style));
                    }
                    else if (value.front() == ';') {
                        POTASSCO_CHECK(++grp < 3, std::errc::invalid_argument, "too many styles in '%" PRIsv "'",
                                       PRI_SV(style));
                        n = 0;
                    }
                    else {
                        break;
                    }
                    colorStyle_.append(1, value.front());
                }
                POTASSCO_CHECK(colorStyle_.back() != ';' && colorStyle_.back() != '[', std::errc::invalid_argument,
                               "number expected after '%" PRIsv "'", PRI_SV(style));
                colorStyle_.append(1, 'm');
                colorStyle_.append(1, 0);
                style_[colKey] = ansiStyle;
                POTASSCO_CHECK(value.empty() || value.front() == ':', std::errc::invalid_argument,
                               "expected ':' in '%" PRIsv "'", PRI_SV(style));
                style = value.substr(not value.empty());
            }
            POTASSCO_ASSERT(d == colorStyle_.data(), "unexpected color style reallocation");
        }
        doEnableColor(enable);
    }
    return {};
}
void Output::start(std::string_view solver, std::string_view version, std::span<const std::string> input) {
    time_       = {};
    time_.start = RealTime::getTime();
    state_      = Event::Subsystem::subsystem_facade;
    doStart(solver, version, input);
}
void Output::transition(ElapsedTime elapsed, Event::Subsystem to, const char* message) {
    if (to != state_ || to == Event::subsystem_facade) {
        double ts = RealTime::getTime();
        if (auto es = std::exchange(state_, to); es != Event::subsystem_facade) {
            exitState(elapsed, es, diffTime(ts, time_.enter));
        }
        time_.enter = ts;
        switch (to) {
            case Event::subsystem_facade : stopStep(elapsed, diffTime(ts, time_.step)); break;
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
        lastC_     = 0;
        lastM_     = 0;
        state_     = Event::subsystem_facade;
        time_.step = time_.enter = RealTime::getTime();
        startStep(t, static_cast<uint32_t>(ev->facade->step()));
    }
    else if (event.verb <= verbosity() && event.system != Event::subsystem_facade) {
        if (event.system == state_) {
            printProgress(t, event, diffTime(RealTime::getTime(), time_.enter));
        }
        else if (const auto* log = event_cast<LogEvent>(event); log && log->msg) {
            transition(t, static_cast<Event::Subsystem>(log->system), log->msg);
        }
    }
    else if (auto* ready = event_cast<StepReady>(event); ready) {
        POTASSCO_ASSERT(ready->summary);
        const auto& s = *ready->summary;
        if (s.model() && lastM_) {
            Model m = *s.model();
            m.up    = 0; // ignore update state and always print as model
            printModel(time_.model, s.ctx(), m, flags(m, print_best));
        }
        else if (modelQ() == print_all && s.model() && s.model()->up && not s.model()->def) {
            printModel(time_.model, s.ctx(), *s.model(), flags(*s.model(), print_all));
        }
        transition(t, Event::subsystem_facade, "");
        if (callQ() == print_all) {
            summary(s, false);
        }
        else if (callQ() == print_best) {
            lastC_ = 1;
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
    time_.model        = elapsedTime();
    if (auto f = flags(m, type); f) {
        printModel(time_.model, *s.sharedContext(), m, f);
    }
    lastM_ = type != print_best && (modelQ() == print_best || (optQ() == print_best && hasMeta));
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
    if (lastC_ && s.facade) {
        summary(s.facade->summary(), false);
    }
    summary(s, true);
    doShutdown();
}
void Output::doEnableColor(bool) {}
void Output::enterState(ElapsedTime, Event::Subsystem, const char*) {}
void Output::exitState(ElapsedTime, Event::Subsystem, ElapsedTime) {}
void Output::printProgress(ElapsedTime, const Event&, ElapsedTime) {}
void Output::enterStats(StatsKey, const char*, uint32_t) {}
void Output::printLogicProgramStats(const Asp::LpStats&) {}
void Output::printProblemStats(const ProblemStats&) {}
void Output::printSolverStats(const SolverStats&) {}
void Output::printUserStats(const StatisticObject&) {}
void Output::exitStats(StatsKey) {}
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
auto Output::resultString(const ClaspFacade::Summary& summary) -> const char* {
    auto res = res_unknown;
    if (summary.unsat()) {
        res = res_unsat;
    }
    else if (summary.sat()) {
        res = not summary.optimum() ? res_sat : res_opt;
    }
    return result_[res];
}
void Output::setResultString(ResultStr r, const char* str) {
    POTASSCO_ASSERT(r < num_str);
    result_[r] = str;
}
using StatsType = Potassco::StatisticsType;
/////////////////////////////////////////////////////////////////////////////////////////
// JsonOutput
/////////////////////////////////////////////////////////////////////////////////////////
static constexpr auto json_special = "\b\f\n\r\t\"\\"sv;
static constexpr auto json_replace = "bfnrt\"\\"sv;
JsonOutput::JsonOutput(FILE* sink, uint32_t v) : Output(sink, std::min(v, 1u)), open_("") { objStack_.reserve(10); }
JsonOutput::~JsonOutput() { JsonOutput::doShutdown(); }
void JsonOutput::printString(std::string_view s, const char* sep, ColorStyle st) {
    TmpBuffer<1024> buf;
    if (auto p = s.find_first_of(json_special); p != std::string_view::npos) {
        buf.append(s.substr(0, p));
        s.remove_prefix(p);
        for (auto c : s) {
            buf.push(c);
            if (p = json_special.find(c); p != std::string_view::npos) {
                buf.back() = '\\';
                buf.push(json_replace[p]);
            }
        }
        s = buf.view();
    }
    auto styleBegin = style(st);
    auto styleEnd   = *styleBegin ? style() : styleBegin;
    print("%s%s\"%" PRIsv "\"%s", sep, styleBegin, PRI_SV(s), styleEnd);
}
void JsonOutput::printKeyValueImpl(std::string_view k, ColorStyle vStyle, std::string_view val, const char* vQuote) {
    const auto* col = style(vStyle);
    print("%s%-*s%s\"%" PRIsv "\"%s: %s%s%" PRIsv "%s%s", std::exchange(open_, ",\n"), indent(), "", style(col_info),
          PRI_SV(k), style(), col, vQuote, PRI_SV(val), vQuote, *col ? style() : "");
}
void JsonOutput::printKeyValue(std::string_view k, std::string_view v, ColorStyle valStyle) {
    assert(v.find_first_of(json_special) == std::string_view::npos);
    return printKeyValueImpl(k, valStyle, v, "\"");
}
template <typename V>
void JsonOutput::printKeyValue(std::string_view k, V v, ColorStyle valStyle) {
    TmpBuffer<> buffer;
    if constexpr (std::is_same_v<V, ElapsedTime>) {
        assert(v >= ElapsedTime{0.0});
        formatTo(buffer.rep(), "%.3f", v.count());
    }
    else if constexpr (std::is_floating_point_v<V>) {
        if (std::isnan(v)) {
            buffer.append("null"sv);
        }
        else if (std::round(v) == v) {
            Potassco::toChars(buffer, static_cast<int64_t>(v));
        }
        else {
            formatTo(buffer.rep(), "%.3f", v);
        }
    }
    else {
        static_assert(std::is_unsigned_v<V>);
        Potassco::toChars(buffer, static_cast<uint64_t>(v));
    }
    printKeyValueImpl(k, valStyle, buffer.view(), "");
}

void JsonOutput::pushObject(std::string_view k, ObjType t, bool startIndent) {
    char o   = t == type_object ? '{' : '[';
    auto col = k.empty() ? "" : style(col_info);
    auto q   = k.empty() ? "" : "\"";
    print("%s%-*s%s%s%" PRIsv "%s%s%c\n", open_, indent(), "", col, q, PRI_SV(k), *q ? "\": " : "", *col ? style() : "",
          o);
    objStack_ += o;
    open_      = "";
    if (startIndent) {
        print("%-*s", indent(), "");
        flush();
    }
}
char JsonOutput::popObject() {
    assert(not objStack_.empty());
    char o = objStack_.back();
    objStack_.pop_back();
    print("\n%-*s%c", indent(), "", o == '{' ? '}' : ']');
    open_ = ",\n";
    return o;
}
void JsonOutput::startWitness(ElapsedTime time) {
    assert(not objStack_.empty());
    if (objStack_.back() != '[') {
        pushObject("Witnesses"sv, type_array);
    }
    pushObject();
    printKeyValue("Time"sv, time, col_trace);
}
void JsonOutput::endWitness() {
    popObject();
    flush();
}
void JsonOutput::popUntil(uint32_t sz) {
    while (size32(objStack_) > sz) { popObject(); }
}
void JsonOutput::printSum(std::string_view name, SumView sum, const Wsum_t* last) {
    pushObject(name, type_array, true);
    auto buf = formatCosts(std::ranges::join_view(std::array{sum, SumView{last, last != nullptr}}), ',', " ");
    print("%s", buf.data());
    popObject();
}
void JsonOutput::printCosts(SumView costs, std::string_view name) { printSum(name, costs); }
void JsonOutput::printCons(const SharedContext& ctx, const Model& m) {
    auto [def, open] = m.numConsequences(ctx);
    pushObject("Consequences"sv);
    printKeyValue("True"sv, def);
    printKeyValue("Open"sv, open);
    popObject();
}

void JsonOutput::doStart(std::string_view solver, std::string_view version, std::span<const std::string> input) {
    if (indent() == 0) {
        open_ = "";
        pushObject();
    }
    printKeyValue("Solver"sv, std::string_view{std::string(solver).append(" version ").append(version)}, col_warn);
    pushObject("Input"sv, type_array, true);
    for (const auto* sep = ""; const auto& x : input) { printString(x, std::exchange(sep, ","), col_trace); }
    popObject();
    pushObject("Call"sv, type_array);
}
void JsonOutput::printModel(ElapsedTime elapsed, const SharedContext& ctx, const Model& m, ModelFlag flags) {
    assert(flags != model_quiet);
    startWitness(elapsed);
    if (Potassco::test(flags, model_values)) {
        pushObject("Value"sv, type_array, true);
        printWitness(ctx, m, [this, first = true](Literal lit, const char* name) mutable {
            if (auto sep = std::exchange(first, false) ? "" : ", "; name) {
                printString(name, sep, col_trace);
            }
            else {
                print("%s%d", sep, toInt(lit));
            }
        });
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
void JsonOutput::printUnsat(ElapsedTime elapsed, const SharedContext&, const Model& m) {
    if (m.ctx->lowerBound().active() && optQ() == print_all) {
        startWitness(elapsed);
        auto lower = m.ctx->lowerBound();
        auto first = m.hasCosts() && m.costs.size() > lower.level ? m.costs.subspan(0, lower.level) : SumView();
        printSum("Lower"sv, first, &lower.bound);
        endWitness();
    }
}
void JsonOutput::startStep(ElapsedTime elapsed, uint32_t) {
    popUntil(2u);
    pushObject({}, type_object);
    printKeyValue("Start"sv, elapsed, col_none);
    flush();
}
void JsonOutput::stopStep(ElapsedTime elapsed, ElapsedTime) {
    assert(not objStack_.empty());
    popUntil(3u);
    printKeyValue("Stop"sv, elapsed, col_trace);
    flush();
}
void JsonOutput::printSummary(const ClaspFacade::Summary& run, bool final) {
    popUntil(final ? 1u : 3u);
    printKeyValue("Result"sv, std::string_view{resultString(run)}, final ? col_warn : col_note);
    if (verbosity()) {
        if (run.result.interrupted()) {
            printKeyValue(interruptedString(run.result), 1u);
        }
        pushObject("Models"sv);
        printKeyValue("Number"sv, run.numEnum);
        printKeyValue("More"sv, run.complete() ? "no"sv : "yes"sv, col_note);
        if (run.sat()) {
            if (run.consequences()) {
                printKeyValue(run.consequences(), run.complete() ? "yes"sv : "unknown"sv, col_note);
                printCons(run.ctx(), *run.model());
            }
            if (run.optimize()) {
                printKeyValue("Optimum"sv, run.optimum() ? "yes"sv : "unknown"sv, col_note);
                printKeyValue("Optimal"sv, run.optimal());
                printCosts(run.costs());
            }
        }
        popObject();
        if (run.hasLower() && not run.optimum()) {
            pushObject("Bounds"sv);
            printCosts(run.lower(), "Lower"sv);
            printCosts(run.costs(), "Upper"sv);
            popObject();
        }
        if (final) {
            printKeyValue("Calls"sv, run.step + 1);
        }
        pushObject("Time"sv);
        printKeyValue("Total"sv, run.totalTime);
        printKeyValue("Solve"sv, run.solveTime);
        printKeyValue("Model"sv, run.satTime);
        printKeyValue("Unsat"sv, run.unsatTime);
        printKeyValue("CPU"sv, run.cpuTime);
        popObject(); // Time
        if (run.ctx().concurrency() > 1) {
            printKeyValue("Threads"sv, run.ctx().concurrency());
            printKeyValue("Winner"sv, run.ctx().winner());
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
        case stats_hcc    : pushObject({}, type_object); break;
    }
}
void JsonOutput::exitStats(StatsKey) { popObject(); }
void JsonOutput::printLogicProgramStats(const Asp::LpStats& lp) {
    using namespace Asp;
    pushObject("LP"sv);
    pushObject("Rules"sv);
    printKeyValue("Original"sv, lp.rules[0].sum());
    printKeyValue("Final"sv, lp.rules[1].sum());
    for (auto i : irange(RuleStats::numKeys())) {
        if (i != RuleStats::normal && lp.rules[0][i]) {
            pushObject(RuleStats::toStr(i));
            printKeyValue("Original"sv, lp.rules[0][i]);
            printKeyValue("Final"sv, lp.rules[1][i]);
            popObject();
        }
    }
    popObject(); // Rules
    printKeyValue("Atoms"sv, lp.atoms);
    if (lp.auxAtoms) {
        printKeyValue("AuxAtoms"sv, lp.auxAtoms);
    }
    if (lp.disjunctions[0]) {
        pushObject("Disjunctions"sv);
        printKeyValue("Original"sv, lp.disjunctions[0]);
        printKeyValue("Final"sv, lp.disjunctions[1]);
        popObject();
    }
    pushObject("Bodies"sv);
    printKeyValue("Original"sv, lp.bodies[0].sum());
    printKeyValue("Final"sv, lp.bodies[1].sum());
    for (uint32_t i : irange(1u, BodyStats::numKeys())) {
        if (lp.bodies[0][i]) {
            pushObject(BodyStats::toStr(i));
            printKeyValue("Original"sv, lp.bodies[0][i]);
            printKeyValue("Final"sv, lp.bodies[1][i]);
            popObject();
        }
    }
    popObject();
    if (lp.sccs == 0) {
        printKeyValue("Tight"sv, "yes"sv);
    }
    else if (lp.sccs == PrgNode::scc_not_set) {
        printKeyValue("Tight"sv, "N/A"sv);
    }
    else {
        printKeyValue("Tight"sv, "no"sv);
        printKeyValue("SCCs"sv, lp.sccs);
        printKeyValue("NonHcfs"sv, lp.nonHcfs);
        printKeyValue("UfsNodes"sv, lp.ufsNodes);
        printKeyValue("NonHcfGammas"sv, lp.gammas);
    }
    pushObject("Equivalences"sv);
    printKeyValue("Sum"sv, lp.eqs());
    printKeyValue("Atom"sv, lp.eqs(VarType::atom));
    printKeyValue("Body"sv, lp.eqs(VarType::body));
    printKeyValue("Other"sv, lp.eqs(VarType::hybrid));
    popObject();
    popObject(); // LP
}
void JsonOutput::printProblemStats(const ProblemStats& p) {
    pushObject("Problem"sv);
    printKeyValue("Variables"sv, p.vars.num);
    printKeyValue("Eliminated"sv, p.vars.eliminated);
    printKeyValue("Frozen"sv, p.vars.frozen);
    pushObject("Constraints"sv);
    uint32_t sum = p.numConstraints();
    printKeyValue("Sum"sv, sum);
    printKeyValue("Binary"sv, p.constraints.binary);
    printKeyValue("Ternary"sv, p.constraints.ternary);
    popObject(); // Constraints
    printKeyValue("AcycEdges"sv, p.acycEdges);
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
    for (auto map = s.type() == StatsType::map; auto i : irange(s)) {
        auto key = map ? s.key(i) : std::string_view{};
        if (auto child = not key.empty() ? s.at(key) : s[i]; child.type() == StatsType::value) {
            printKeyValue(key, child.value());
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
        print("\n");
        flush();
    }
}
void JsonOutput::printCoreStats(const CoreStats& st) {
    pushObject("Core"sv);
    printKeyValue("Choices"sv, st.choices);
    printKeyValue("Conflicts"sv, st.conflicts);
    printKeyValue("Backtracks"sv, st.backtracks());
    printKeyValue("Backjumps"sv, st.backjumps());
    printKeyValue("Restarts"sv, st.restarts);
    printKeyValue("RestartAvg"sv, st.avgRestart());
    printKeyValue("RestartLast"sv, st.lastRestart);
    popObject(); // Core
}
void JsonOutput::printExtStats(const ExtendedStats& stx, bool generator) {
    pushObject("More"sv);
    printKeyValue("CPU"sv, stx.cpuTime);
    printKeyValue("Models"sv, stx.models);
    if (stx.domChoices) {
        printKeyValue("DomChoices"sv, stx.domChoices);
    }
    if (stx.hccTests) {
        pushObject("StabTests"sv);
        printKeyValue("Sum"sv, stx.hccTests);
        printKeyValue("Full"sv, stx.hccTests - stx.hccPartial);
        printKeyValue("Partial"sv, stx.hccPartial);
        popObject();
    }
    if (stx.models) {
        printKeyValue("AvgModel"sv, stx.avgModel());
    }
    printKeyValue("Splits"sv, stx.splits);
    printKeyValue("Problems"sv, stx.gps);
    printKeyValue("AvgGPLength"sv, stx.avgGp());
    pushObject("Lemma"sv);
    printKeyValue("Sum"sv, stx.lemmas());
    printKeyValue("Deleted"sv, stx.deleted);
    pushObject("Type"sv, type_array);
    std::string_view names[] = {"Short"sv, "Conflict"sv, "Loop"sv, "Other"sv};
    for (auto i : irange(names)) {
        pushObject();
        printKeyValue("Type"sv, names[i], col_trace);
        if (i == ConstraintType::static_) {
            printKeyValue("Sum"sv, stx.binary + stx.ternary);
            printKeyValue("Ratio"sv, percent(stx.binary + stx.ternary, stx.lemmas()));
            printKeyValue("Binary"sv, stx.binary);
            printKeyValue("Ternary"sv, stx.ternary);
        }
        else {
            printKeyValue("Sum"sv, stx.lemmas(static_cast<ConstraintType>(i)));
            printKeyValue("AvgLen"sv, stx.avgLen(static_cast<ConstraintType>(i)));
        }
        popObject();
    }
    popObject();
    popObject(); // Lemma
    if (stx.distributed || stx.integrated) {
        pushObject("Distribution"sv);
        printKeyValue("Distributed"sv, stx.distributed);
        printKeyValue("Ratio"sv, stx.distRatio());
        printKeyValue("AvgLbd"sv, stx.avgDistLbd());
        popObject();
        pushObject("Integration"sv);
        printKeyValue("Integrated"sv, stx.integrated);
        printKeyValue("Units"sv, stx.intImps);
        printKeyValue("AvgJump"sv, stx.avgIntJump());
        if (generator) {
            printKeyValue("Ratio"sv, stx.intRatio());
        }
        popObject();
    }
    popObject(); // More
}
void JsonOutput::printJumpStats(const JumpStats& st) {
    pushObject("Jumps"sv);
    printKeyValue("Sum"sv, st.jumps);
    printKeyValue("Max"sv, st.maxJump);
    printKeyValue("MaxExec"sv, st.maxJumpEx);
    printKeyValue("Avg"sv, st.avgJump());
    printKeyValue("AvgExec"sv, st.avgJumpEx());
    printKeyValue("Levels"sv, st.jumpSum);
    printKeyValue("LevelsExec"sv, st.jumped());
    pushObject("Bounded"sv);
    printKeyValue("Sum"sv, st.bounded);
    printKeyValue("Max"sv, st.maxBound);
    printKeyValue("Avg"sv, st.avgBound());
    printKeyValue("Levels"sv, st.boundSum);
    popObject();
    popObject();
}
/////////////////////////////////////////////////////////////////////////////////////////
// TextOutput
/////////////////////////////////////////////////////////////////////////////////////////
// NOLINTBEGIN
#define PRINT_KEY_VALUE_IMPL(K, FMT, EOK, ...)                                                                         \
    print("%s%s%-*s%-*s: " FMT "%s" EOK, format_[cat_comment], style(keyStyle_), _indent(K), "", width_ - _indent(K),  \
          _key(K) POTASSCO_OPTARGS(__VA_ARGS__), exitKey())
#define PRINT_KEY_VALUE(K, V) PRINT_KEY_VALUE_IMPL(K, "%s", "\n", _valStr(V).c_str())
#define PRINT_KEY_VALUE_EXT(K, V, FMT_E, ...)                                                                          \
    PRINT_KEY_VALUE_IMPL(K, "%-8s (" FMT_E ")", "\n", _valStr(V).c_str(), __VA_ARGS__)
#define PRINT_KEY_VALUE_COND(K, V, C, FMT_E, ...)                                                                      \
    (C ? PRINT_KEY_VALUE_EXT(K, V, FMT_E, __VA_ARGS__) : PRINT_KEY_VALUE(K, V))
#define PRINT_LN(st, cat, fmt, ...)          print("%s%s" fmt "%s\n", format_[cat], style(st), __VA_ARGS__, style())
#define PRINT_BR(cat)                        print("%s\n", format_[cat])
#define PRINT_COMMENT_LN(st, verb, fmt, ...) (verbosity() >= (verb) && PRINT_LN(st, cat_comment, fmt, __VA_ARGS__))

static constexpr const char* _key(const char* k) { return k; }
static constexpr int         _indent(const char*) { return 0; }
static constexpr const char* _key(const auto& k) { return k.first; }
static constexpr int         _indent(const auto& k) { return k.second; }
static auto                  _valStr(const auto& val) -> Potassco::StrF {
    return Overload{
        [&]<std::signed_integral T>(T v) { return Potassco::formatF("%" PRId64, static_cast<int64_t>(v)); },
        [&]<std::unsigned_integral T>(T v) { return Potassco::formatF("%" PRIu64, static_cast<int64_t>(v)); },
        [&]<std::floating_point T>(T v) { return Potassco::formatF("%g", static_cast<double>(v)); },
        [&](const char* v) { return Potassco::formatF("%s", v); },
        [&](Output::ElapsedTime v) { return Potassco::formatF("%.3fs", static_cast<double>(v.count())); },
        [&](const ModelNum& v) {
            return Potassco::formatF("%" PRIu64 "%s", static_cast<uint64_t>(v.first), not v.second ? "+" : "");
        },
    }(val);
}
// NOLINTEND
static constexpr uint32_t numChars(Wsum_t n) {
    auto x = n >= 0 ? static_cast<uint64_t>(n) : ~static_cast<uint64_t>(n) + 1;
    auto r = 1u + (n < 0);
    if (x >= 100000000) {
        r += 8;
        x /= 100000000;
    }
    if (x >= 100000000) {
        r += 8;
        x /= 100000000;
    }
    if (x >= 10000) {
        r += 4;
        x /= 10000;
    }
    if (x >= 100) {
        r += 2;
        x /= 100;
    }
    if (x >= 10) {
        r += 1;
    }
    return r;
}
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
static auto formatBounds(SumView lower, SumView upper) -> TmpBuffer<> {
    TmpBuffer<> buf;
    for (auto uMax = size32(upper), lMax = size32(lower); auto i : irange(std::max(uMax, lMax))) {
        if (not buf.empty()) {
            buf.push(' ');
        }
        if (i >= uMax) {
            Potassco::toChars(buf.append("["sv), lower[i]).append(";*]"sv);
        }
        else if (i >= lMax || lower[i] == upper[i]) {
            Potassco::toChars(buf, upper[i]);
        }
        else {
            Potassco::toChars(buf.append("["sv), lower[i]).append(";"sv);
            Potassco::toChars(buf, upper[i]).append("]"sv);
        }
    }
    buf.push(0);
    return buf;
}

auto TextOutput::CatAtom::fromString(std::string_view fmt) -> CatAtom {
    using namespace std::literals;
    auto           fmtPos = UINT32_MAX;
    auto           start  = 0u;
    CatAtom        result;
    constexpr auto check = [](bool x, const char* y) {
        if (not x) {
            throw std::invalid_argument(y);
        }
    };
    for (char f = 's'; not fmt.empty();) {
        if (fmt.front() == ':' && std::min(result.atom_, result.var_) == UINT32_MAX) {
            if (not result.buffer_.empty()) {
                result.atom_ = start;
                result.buffer_.push_back(0);
            }
            fmt.remove_prefix(1);
            fmtPos = UINT32_MAX;
            if (not fmt.empty()) {
                start       = size32(result.buffer_);
                result.var_ = start;
                f           = 'u';
            }
            continue;
        }
        check(fmt.front() != '\n', "new line not allowed");
        result.buffer_.push_back(fmt.front());
        fmt.remove_prefix(1);
        if (result.buffer_.back() == '%') {
            check(not fmt.empty(), "missing format specifier");
            if (fmt.starts_with('0')) {
                check(fmtPos == UINT32_MAX, "too many arguments");
                fmtPos = size32(result.buffer_);
                result.buffer_.push_back(f);
            }
            else {
                check(fmt.starts_with('%'), "invalid format specifier");
            }
            fmt.remove_prefix(1);
        }
        else if (result.buffer_.back() == '\\' && fmt.starts_with(':')) {
            result.buffer_.back() = ':';
            fmt.remove_prefix(1);
        }
    }
    if (not result.buffer_.empty() && std::min(result.atom_, result.var_) == UINT32_MAX) {
        auto sz      = size32(result.buffer_);
        result.atom_ = start;
        result.buffer_.reserve((sz * 2) + 1);
        result.buffer_.push_back(0);
        result.var_ = size32(result.buffer_);
        result.buffer_.insert(result.buffer_.end(), result.buffer_.begin(),
                              result.buffer_.begin() + static_cast<std::ptrdiff_t>(sz));
        if (fmtPos != UINT32_MAX) {
            assert(result.buffer_[result.var_ + fmtPos] == 's');
            result.buffer_[result.var_ + fmtPos] = 'u';
        }
    }
    return result;
}
auto TextOutput::CatAtom::fmtAtom() const -> const char* {
    return atom_ < size32(buffer_) ? buffer_.data() + atom_ : nullptr;
}
auto TextOutput::CatAtom::fmtVar() const -> const char* {
    return var_ < size32(buffer_) ? buffer_.data() + var_ : nullptr;
}

TextOutput::TextOutput(FILE* sink, const Options& options) : Output(sink, options.verbosity) {
    format_[cat_comment]    = "";
    format_[cat_value]      = "";
    format_[cat_objective]  = "Optimization: ";
    format_[cat_result]     = "";
    format_[cat_value_term] = "";
    const auto* fmtAtom     = "%s";
    const auto* fmtVar      = "%u";
    if (options.format == format_aspcomp) {
        format_[cat_comment]   = "% ";
        format_[cat_value]     = "ANSWER\n";
        format_[cat_objective] = "COST ";
        fmtAtom                = "%s.";
        setResultString(res_sat, "");
        setResultString(res_unsat, "INCONSISTENT");
        setResultString(res_opt, "OPTIMUM");
        setModelQuiet(print_best);
        setOptQuiet(print_best);
    }
    else if (options.format == format_sat09 || options.format == format_pb09 || options.format == format_maxsat09) {
        format_[cat_comment]    = "c ";
        format_[cat_value]      = "v ";
        format_[cat_objective]  = "o ";
        format_[cat_result]     = "s ";
        format_[cat_value_term] = "0";
        if (options.format == format_maxsat09) {
            setResultString(res_sat, "UNKNOWN");
        }
        else if (options.format == format_pb09) {
            format_[cat_value_term] = "";
            fmtVar                  = "x%u";
            setModelQuiet(print_best);
        }
    }
    if (const auto* x = options.catAtom.fmtAtom(); x) {
        fmtAtom = x;
    }
    if (const auto* x = options.catAtom.fmtVar(); x) {
        fmtVar = x;
    }
    fmtAtom_.append("%s%s").append(fmtAtom).append(1, 0);
    auto fmtVarPos = fmtAtom_.size();
    fmtAtom_.append("%s%s%s").append(fmtVar);
    format_[cat_atom_name] = fmtAtom_.data();
    format_[cat_atom_var]  = fmtAtom_.data() + fmtVarPos;
    ifs_[0]                = options.ifs;
    ifs_[1]                = 0;
    width_                 = 13;
    progress_              = {};
}
TextOutput::~TextOutput() = default;
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
            PRINT_COMMENT_LN(col_trace, 2u, "%s", row_sep);
        }
        progress_.lines -= nLines;
    }
}
// NOLINTBEGIN(readability-make-member-function-const,readability-convert-member-functions-to-static)
void TextOutput::printEnter(const char* message, const char* suffix) {
    print("%s%-*s%s", format_[cat_comment], width_, message, suffix);
    flush();
}
void TextOutput::printExit(ElapsedTime stateElapsed) { print("%.3fs\n", stateElapsed.count()); }
void TextOutput::printMeta(const SharedContext& ctx, const Model& m) {
    if (m.consequences()) {
        auto [low, est] = m.numConsequences(ctx);
        auto st         = m.def || est == 0 ? col_warn : col_note;
        PRINT_LN(st, cat_comment, "Consequences: [%u;%u]", low, low + est);
    }
    if (m.hasCosts()) {
        auto st = m.opt ? col_warn : col_note;
        print("%s%s%s%s\n", style(st), format_[cat_objective],
              formatCosts(m.costs, *fieldSeparator(), getIfsSuffix(cat_objective)).data(), style());
    }
}
void TextOutput::printPreproEvent(ElapsedTime stateTime, const Event& ev) {
    using SatPreProgress = SatPreprocessor::Progress;
    if (const auto* sat = event_cast<SatPreProgress>(ev)) {
        progress_.last = sat->id;
        switch (static_cast<SatPreProgress::EventOp>(sat->op)) {
            default:
                print("%s%-*s: %c: %8u/%-8u\r", format_[cat_comment], width_, sat_pre, static_cast<char>(sat->op),
                      sat->cur, sat->max);
                flush();
                break;
            case SatPreProgress::event_enter:
                printExit(stateTime);
                printEnter(sat_pre, ":\r");
                resetStateTime();
                break;
            case SatPreProgress::event_exit:
                auto* p = sat->self;
                PRINT_KEY_VALUE_EXT(sat_pre, stateTime, "ClRemoved: %u ClAdded: %u LitsStr: %u", p->stats.clRemoved,
                                    p->stats.clAdded, p->stats.litsRemoved);
                progress_.last = -1;
                break;
        }
    }
}
void TextOutput::printSolveEvent(ElapsedTime elapsed, const Event& ev, ElapsedTime stateTime) {
    char           lEnd = '\n';
    TmpBuffer<128> buffer;
    int            eventId = static_cast<int>(ev.id);
    if (const auto* be = event_cast<BasicSolveEvent>(ev)) {
        if ((verbosity() & 1) == 0) {
            return;
        }
        formatEvent(buffer.rep(), *be);
    }
    else if (const auto* te = event_cast<SolveTestEvent>(ev)) {
        if ((verbosity() & 4) == 0) {
            return;
        }
        formatEvent(buffer.rep(), *te);
        lEnd = te->result == -1 ? '\r' : '\n';
    }
#if CLASP_HAS_THREADS
    else if (const auto* me = event_cast<mt::MessageEvent>(ev)) {
        formatEvent(buffer.rep(), *me);
        eventId = static_cast<int>(Event::eventId<LogEvent>());
    }
#endif
    else if (const auto* log = event_cast<LogEvent>(ev)) {
        auto w     = Potassco::formatTo(buffer.rep(), "%2u:L| [Solving+%.3fs]", log->solver->id(), stateTime.count());
        auto width = w < 37 ? static_cast<int>(37 - w) : 0;
        Potassco::formatTo(buffer.rep(), "%-*s%-38.38s |", width, "", log->msg);
    }
    if (buffer.empty()) {
        return;
    }
    Potassco::formatTo(buffer.rep(), " %10.3fs |", elapsed.count());
    auto lock = lockSink();
    if (progress_.lines <= 0 || eventId != progress_.last) {
        if (progress_.lines <= 0) {
            const char* pre = header_.c_str();
            const char* cls = style();
            if ((this->verbosity() & 1) != 0 || ev.id == Event::eventId<SolveTestEvent>()) {
                print(
                    "%s%s%s\n"
                    "%sID:T       Vars           Constraints         State            Limits            Time     |%s\n"
                    "%s       #free/#fixed   #problem/#learnt  #conflicts/ratio #conflict/#learnt                |%s\n"
                    "%s%s%s\n",
                    pre, row_sep, cls, pre, cls, pre, cls, pre, row_sep, cls);
            }
            else {
                print(
                    "%s%s%s\n"
                    "%sID:T       Info                     Info                      Info               Time     |%s\n"
                    "%s%s%s\n",
                    pre, row_sep, cls, pre, cls, pre, row_sep, cls);
            }
            progress_.lines = 20;
        }
        else if (progress_.last != -1) {
            PRINT_LN(col_trace, cat_comment, "%s", row_sep);
        }
        progress_.last = eventId;
    }
    progress_.lines -= static_cast<int>(lEnd == '\n');
    auto line        = buffer.view();
    print("%s%" PRIsv "%c", format_[cat_comment], PRI_SV(line), lEnd);
}
// NOLINTEND(readability-make-member-function-const,readability-convert-member-functions-to-static)
void TextOutput::doEnableColor(bool enable) {
    header_.assign(format_[cat_comment]);
    if (enable) {
        header_.append(style(col_trace));
    }
}
void TextOutput::doShutdown() {}
void TextOutput::doStart(std::string_view solver, std::string_view version, std::span<const std::string> input) {
    if (not solver.empty()) {
        PRINT_COMMENT_LN(col_warn, 1u, "%" PRIsv " version %" PRIsv, PRI_SV(solver), PRI_SV(version));
    }
    if (not input.empty()) {
        PRINT_COMMENT_LN(col_none, 1u, "Reading from %s%s%s%s", style(col_info), prettify(input.front()).c_str(),
                         input.size() > 1 ? " ..." : "", style());
    }
}
void TextOutput::printModelValues(const SharedContext& ctx, const Model& m) {
    static constexpr const char* sign[2] = {"", "-"};
    print("%s", format_[cat_value]);
    auto ifsSuffix = getIfsSuffix(cat_value);
    printWitness(ctx, m, [this, accu = 0u, maxLine = 0u, ifsSuffix](Literal lit, const char* name) mutable {
        auto ifs = std::pair{"", ""};
        if (not maxLine) {
            maxLine = name || *fieldSeparator() != ' ' ? UINT32_MAX : 70;
        }
        else if (accu < maxLine) {
            ifs = std::pair{fieldSeparator(), ifsSuffix};
        }
        else {
            print("\n%s", getIfsSuffix('\n', cat_value));
            accu = 0;
        }
        POTASSCO_WARNING_PUSH()
        POTASSCO_WARNING_IGNORE_GNU("-Wformat-nonliteral") // format not a string literal
        accu += static_cast<unsigned>(
            name ? print(format_[cat_atom_name], ifs.first, ifs.second, name)
                 : print(format_[cat_atom_var], ifs.first, ifs.second, sign[lit.sign()], lit.var()));
        POTASSCO_WARNING_POP()
    });
    if (const auto* term = format_[cat_value_term]; *term) {
        print("%s%s%s\n", fieldSeparator(), ifsSuffix, term);
    }
    else {
        print("\n");
    }
}

void TextOutput::printModel(ElapsedTime elapsed, const SharedContext& ctx, const Model& m, ModelFlag flags) {
    POTASSCO_ASSERT(flags != model_quiet);
    auto        lock = lockSink();
    const char* type = not m.up ? "Answer" : "Update";
    clearProgress(3);
    PRINT_COMMENT_LN(col_info, 1u, "%s: %" PRIu64 " (Time: %.3fs)", type, m.num, elapsed.count());
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

void TextOutput::printUnsat(ElapsedTime elapsed, const SharedContext& ctx, const Model& m) {
    if (optQ() != print_all) {
        return;
    }
    auto lock = lockSink();
    if (auto lb = m.ctx->lowerBound(); lb.active()) {
        clearProgress(1);
        TmpBuffer<> bound;
        if (m.costs.size() > lb.level) {
            for (auto i : irange(lb.level)) { Potassco::toChars(bound, m.costs[i]).push(' '); }
            auto ub  = m.costs[lb.level];
            auto err = static_cast<double>(ub - lb.bound) / static_cast<double>(lb.bound);
            if (err < 0) {
                err = -err;
            }
            bound.push('[');
            if (auto x = numChars(ub), y = numChars(lb.bound); x > y) {
                auto n = x - y;
                std::fill_n(bound.rep().alloc(n).data(), n, ' ');
            }
            Potassco::toChars(bound, lb.bound).append(";"sv);
            Potassco::toChars(bound, ub).append("] (Error: "sv);
            Potassco::toChars(bound, err).push(' ');
        }
        else {
            formatTo(bound.rep(), "[%6" PRId64 ";inf] (", lb.bound);
        }
        bound.push(0);
        print("%s%s%-12s: %sTime: %.3fs)%s\n", format_[cat_comment], style(col_trace), "Progression", bound.data(),
              elapsed.count(), style());
    }
    if (m.num != 0 && m.up) {
        printMeta(ctx, m);
    }
}
void TextOutput::startStep(ElapsedTime, uint32_t step) {
    progress_ = {};
    if (callQ() != print_no) {
        PRINT_COMMENT_LN(col_trace, 1u, "%s", row_sep);
        PRINT_COMMENT_LN(col_info, 2u, "%-*s: %d", width_, "Call", step + 1);
    }
}
void TextOutput::enterState(ElapsedTime, Event::Subsystem sys, const char* activity) {
    if (sys == Event::subsystem_load || sys == Event::subsystem_prepare) {
        printEnter(activity, ": ");
        progress_.last = -2;
    }
    else if (sys == Event::subsystem_solve) {
        PRINT_COMMENT_LN(col_none, 1u, "%s...", activity);
        progress_ = {};
    }
}
void TextOutput::exitState(ElapsedTime, Event::Subsystem, ElapsedTime stateElapsed) {
    if (progress_.last != -1) {
        if (progress_.last == -2) {
            printExit(stateElapsed);
        }
        else if (std::cmp_equal(progress_.last, Event::eventId<SatPreprocessor::Progress>())) {
            PRINT_KEY_VALUE_EXT(sat_pre, stateElapsed, "%s", "unexpected state change - result unknown");
        }
        progress_ = {};
    }
}
void TextOutput::stopStep(ElapsedTime, ElapsedTime) {
    PRINT_COMMENT_LN(col_trace, 2u - (callQ() != print_no), "%s", row_sep);
}
void TextOutput::printProgress(ElapsedTime elapsed, const Event& ev, ElapsedTime stateElapsed) {
    if (ev.system == Event::subsystem_prepare) {
        printPreproEvent(stateElapsed, ev);
    }
    else if (ev.system == Event::subsystem_solve) {
        printSolveEvent(elapsed, ev, stateElapsed);
    }
}
void TextOutput::printSummary(const ClaspFacade::Summary& run, bool final) {
    if (final && callQ() != print_no) {
        PRINT_COMMENT_LN(col_trace, 1u, "%s", acc_sep);
    }
    if (const auto* str = resultString(run); *str) {
        PRINT_LN(final ? col_warn : col_note, cat_result, "%s", str);
    }
    if (verbosity() || stats(run)) {
        PRINT_BR(cat_comment);
        if (run.result.interrupted()) {
            keyStyle_           = col_err;
            auto        val     = run.result.signal != SIGALRM ? run.result.signal : 1;
            const auto* sigName = signalName(run.result.signal);
            PRINT_KEY_VALUE_COND(interruptedString(run.result), val, run.result.signal != SIGALRM && sigName, "%s",
                                 sigName);
        }
        keyStyle_ = col_info;
        POTASSCO_SCOPE_EXIT({ keyStyle_ = col_none; });
        PRINT_KEY_VALUE("Models", ModelNum(run.numEnum, run.complete()));
        if (run.sat()) {
            if (run.consequences()) {
                PRINT_KEY_VALUE(indent(run.consequences()), run.complete() ? "yes" : "unknown");
            }
            if (run.hasCosts()) {
                PRINT_KEY_VALUE(indent("Optimum"), run.optimum() ? "yes" : "unknown");
            }
            if (run.optimize()) {
                if (run.optimal() > 1) {
                    PRINT_KEY_VALUE(indent("Optimal"), run.optimal());
                }
                PRINT_KEY_VALUE("Optimization", formatCosts(run.costs()).data());
            }
            if (run.consequences()) {
                ModelNum m{run.model()->numConsequences(run.ctx()).first, run.complete()};
                PRINT_KEY_VALUE("Consequences", m);
            }
        }
        if (run.hasLower() && not run.optimum()) {
            PRINT_KEY_VALUE("Bounds", formatBounds(run.lower(), run.costs()).data());
        }
        if (final) {
            PRINT_KEY_VALUE("Calls", run.step + 1);
        }
        PRINT_KEY_VALUE_EXT("Time", ElapsedTime{run.totalTime}, "Solving: %.2fs 1st Model: %.2fs Unsat: %.2fs",
                            run.solveTime, run.satTime, run.unsatTime);
        PRINT_KEY_VALUE("CPU Time", ElapsedTime{run.cpuTime});
        if (run.ctx().concurrency() > 1) {
            PRINT_KEY_VALUE_EXT("Threads", run.ctx().concurrency(), "Winner: %u", run.ctx().winner());
        }
    }
}
void TextOutput::startSection(const char* section) {
    PRINT_LN(col_trace, cat_comment, "============ %s Stats ============", section);
    PRINT_BR(cat_comment);
}
void TextOutput::startObject(const char* object, uint32_t n) {
    PRINT_LN(col_trace, cat_comment, "[%s %u]", object, n);
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
        PRINT_KEY_VALUE("CPU Time", ElapsedTime{stats.extra->cpuTime});
        PRINT_KEY_VALUE("Models", stats.extra->models);
    }
    PRINT_KEY_VALUE_COND("Choices", stats.choices, stats.extra && stats.extra->domChoices, "Domain: %" PRIu64,
                         stats.extra->domChoices);
    PRINT_KEY_VALUE_EXT("Conflicts", stats.conflicts, "Analyzed: %" PRIu64, stats.backjumps());
    PRINT_KEY_VALUE_COND("Restarts", stats.restarts, stats.restarts,
                         "Average: %.2f Last: %" PRIu64 " Blocked: %" PRIu64, stats.avgRestart(), stats.lastRestart,
                         stats.blRestarts);

    if (not stats.extra) {
        return;
    }
    const ExtendedStats& stx = *stats.extra;
    const JumpStats&     stj = stx.jumps;
    if (stx.hccTests) {
        PRINT_KEY_VALUE_EXT("Stab. Tests", stx.hccTests, "Full: %" PRIu64 " Partial: %" PRIu64,
                            stx.hccTests - stx.hccPartial, stx.hccPartial);
    }
    if (stx.models) {
        PRINT_KEY_VALUE("Model-Level", stx.avgModel());
    }
    PRINT_KEY_VALUE_EXT("Problems", static_cast<uint64_t>(stx.gps), "Average Length: %.2f Splits: %" PRIu64,
                        stx.avgGp(), static_cast<uint64_t>(stx.splits));
    uint64_t sum = stx.lemmas();
    PRINT_KEY_VALUE_EXT("Lemmas", sum, "Deleted: %" PRIu64, stx.deleted);
    PRINT_KEY_VALUE_EXT(indent("Binary"), static_cast<uint64_t>(stx.binary), "Ratio: %6.2f%%",
                        percent(stx.binary, sum));
    PRINT_KEY_VALUE_EXT(indent("Ternary"), static_cast<uint64_t>(stx.ternary), "Ratio: %6.2f%%",
                        percent(stx.ternary, sum));
    const char* names[] = {"Conflict", "Loop", "Other"};
    for (auto i : irange(names)) {
        auto type = static_cast<ConstraintType>(i + 1);
        PRINT_KEY_VALUE_EXT(indent(names[i]), stx.lemmas(type), "Average Length: %6.1f Ratio: %6.2f%%",
                            stx.avgLen(type), percent(stx.lemmas(type), sum));
    }
    if (stx.distributed || stx.integrated) {
        PRINT_KEY_VALUE_EXT(indent("Distributed"), stx.distributed, "Ratio: %6.2f%% Average LBD: %.2f",
                            stx.distRatio() * 100.0, stx.avgDistLbd());
        if (accu_) {
            PRINT_KEY_VALUE_EXT(indent("Integrated"), stx.integrated,
                                "Ratio: %6.2f%% Unit: %" PRIu64 " Average Jumps: %.2f", stx.intRatio() * 100.0,
                                stx.intImps, stx.avgIntJump());
        }
        else {
            PRINT_KEY_VALUE_EXT(indent("Integrated"), stx.integrated, "Unit: %" PRIu64 " Average Jumps: %.2f",
                                stx.intImps, stx.avgIntJump());
        }
    }
    PRINT_KEY_VALUE_EXT("Backjumps", stj.jumps, "Average: %5.2f Max: %3u Sum: %6" PRIu64, stj.avgJump(), stj.maxJump,
                        stj.jumpSum);
    PRINT_KEY_VALUE_EXT(indent("Executed"), stj.jumps - stj.bounded,
                        "Average: %5.2f Max: %3u Sum: %6" PRIu64 " Ratio: %6.2f%%", stj.avgJumpEx(), stj.maxJumpEx,
                        stj.jumped(), stj.jumpedRatio() * 100.0);
    PRINT_KEY_VALUE_EXT(indent("Bounded"), stj.bounded, "Average: %5.2f Max: %3u Sum: %6" PRIu64 " Ratio: %6.2f%%",
                        stj.avgBound(), stj.maxBound, stj.boundSum, 100.0 - (stj.jumpedRatio() * 100.0));
    PRINT_BR(cat_comment);
}
void TextOutput::printProblemStats(const ProblemStats& stats) {
    uint32_t sum = stats.numConstraints();
    PRINT_KEY_VALUE_EXT("Variables", stats.vars.num, "Eliminated: %4u Frozen: %4u", stats.vars.eliminated,
                        stats.vars.frozen);
    PRINT_KEY_VALUE_EXT("Constraints", sum, "Binary: %5.1f%% Ternary: %5.1f%% Other: %5.1f%%",
                        percent(stats.constraints.binary, sum), percent(stats.constraints.ternary, sum),
                        percent(stats.constraints.other, sum));
    if (stats.acycEdges) {
        PRINT_KEY_VALUE("Acyc-Edges", stats.acycEdges);
    }
    PRINT_BR(cat_comment);
}
void TextOutput::printLogicProgramStats(const Asp::LpStats& stats) {
    using namespace Asp;
    uint32_t rFinal = stats.rules[1].sum(), rOriginal = stats.rules[0].sum();
    PRINT_KEY_VALUE_COND("Rules", rFinal, rFinal != rOriginal, "Original: %u", rOriginal);
    for (auto i : irange(RuleStats::numKeys())) {
        if (i == RuleStats::normal) {
            continue;
        }
        if (uint32_t r = stats.rules[0][i]) {
            PRINT_KEY_VALUE_COND(indent(RuleStats::toStr(i)), stats.rules[1][i], r != stats.rules[1][i], "Original: %u",
                                 r);
        }
    }
    PRINT_KEY_VALUE_COND("Atoms", stats.atoms, stats.auxAtoms != 0, "Original: %u Auxiliary: %u",
                         stats.atoms - stats.auxAtoms, stats.auxAtoms);
    if (stats.disjunctions[0]) {
        PRINT_KEY_VALUE_EXT("Disjunctions", stats.disjunctions[1], "Original: %u", stats.disjunctions[0]);
    }
    uint32_t bFinal = stats.bodies[1].sum(), bOriginal = stats.bodies[0].sum();
    PRINT_KEY_VALUE_COND("Bodies", bFinal, bFinal != bOriginal, "Original: %u", bOriginal);
    for (auto i : irange(1u, BodyStats::numKeys())) {
        if (uint32_t b = stats.bodies[0][i]) {
            PRINT_KEY_VALUE_COND(indent(BodyStats::toStr(i)), stats.bodies[1][i], b != stats.bodies[1][i],
                                 "Original: %u", b);
        }
    }
    if (stats.eqs() > 0) {
        PRINT_KEY_VALUE_EXT("Equivalences", stats.eqs(), "Atom=Atom: %u Body=Body: %u Other: %u",
                            stats.eqs(VarType::atom), stats.eqs(VarType::body), stats.eqs(VarType::hybrid));
    }
    if (const char* tight = "Tight"; stats.sccs == 0) {
        PRINT_KEY_VALUE(tight, "Yes");
    }
    else if (stats.sccs != PrgNode::scc_not_set) {
        PRINT_KEY_VALUE_EXT(tight, "No", "SCCs: %u Non-Hcfs: %u Nodes: %u Gammas: %u", stats.sccs, stats.nonHcfs,
                            stats.ufsNodes, stats.gammas);
    }
    else {
        PRINT_KEY_VALUE(tight, "N/A");
    }
}
void TextOutput::printUserStats(const StatisticObject& stats) { printChildren(stats); }
int  TextOutput::printUserStatsKey(int level, std::string_view key, const uint32_t* idx) {
    int indent = std::min(level, 50) * 2;
    if (const auto* cat = format_[cat_comment]; not idx) {
        return print("%s%-*s%" PRIsv, cat, indent, "", PRI_SV(key));
    }
    else if (key.empty()) {
        return print("%s%-*s[%u]", cat, indent, "", *idx);
    }
    else {
        return print("%s%-*s[%" PRIsv " %u]", cat, indent, "", PRI_SV(key), *idx);
    }
}

// NOLINTNEXTLINE(misc-no-recursion)
void TextOutput::printChildren(const StatisticObject& s, int level, std::string_view prefix) {
    const auto map = s.type() == StatsType::map;
    for (auto i : irange(s)) {
        auto key   = map ? s.key(i) : std::string_view{};
        auto child = map ? s.at(key) : s[i];
        if (auto type = child.type(); type == StatsType::array && not key.empty()) {
            printChildren(child, level, key);
        }
        else {
            auto len = not key.empty() ? printUserStatsKey(level, key) : printUserStatsKey(level, prefix, &i);
            if (type == StatsType::value) {
                auto w = width_ + static_cast<int>(std::strlen(format_[cat_comment]));
                print("%-*s: %g\n", std::max(0, (w - len)), "", child.value());
            }
            else {
                print("\n");
                printChildren(child, level + 1);
            }
        }
    }
}
#undef PRINT_BR
#undef PRINT_COMMENT_LN
#undef PRINT_LN
#undef PRINT_KEY_VALUE_IMPL
#undef PRINT_KEY_VALUE
#undef PRINT_KEY_VALUE_EXT
#undef PRINT_KEY_VALUE_COND

} // namespace Clasp::Cli
