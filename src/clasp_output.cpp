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

#include <amc/vector.hpp>

#include <chrono>
#include <cmath>
#include <cstdio>
using namespace std::literals;

static constexpr std::string_view signal_names[] = {
    ""sv,        "SIGHUP"sv,  "SIGINT"sv,    "SIGQUIT"sv, "SIGILL"sv,  "SIGTRAP"sv, "SIGABRT"sv,
    "SIGBUS"sv,  ""sv,        "SIGKILL"sv,   "SIGUSR1"sv, "SIGSEGV"sv, "SIGUSR2"sv, "SIGPIPE"sv,
    "SIGALRM"sv, "SIGTERM"sv, "SIGSTKFLT"sv, "SIGCHLD"sv, ""sv,
};
static constexpr auto sig_max = static_cast<uint8_t>(signal_names->size() - 1);

namespace Potassco {
template <auto W>
static constexpr auto elapsed(Clasp::Cli::Output::ElapsedTime t) {
    return Potassco::num<W + 1, 3>(t.count(), 's');
}
template <CharBuffer S>
static S& toChars(S& b, Clasp::Cli::Output::ElapsedTime t) {
    if (Clasp::isValidTime(t.count())) {
        toChars(b, elapsed<0>(t));
    }
    else {
        toChars(b, "N/A");
    }
    return b;
}
} // namespace Potassco

namespace Clasp::Cli {
void printf(struct printf_is_probably_not_intended); // poison printf
/////////////////////////////////////////////////////////////////////////////////////////
// Event formatting
/////////////////////////////////////////////////////////////////////////////////////////
static auto startSolverEvent(Potassco::BasicCharBuffer& buffer, const Solver& s,
                             char op) -> Potassco::BasicCharBuffer& {
    return buffer.append(Potassco::num<2>(s.id())).append(':').append(op).append('|');
}
static auto addBasicCol(Potassco::BasicCharBuffer& buffer, const Potassco::Field& n1,
                        const Potassco::Field& n2) -> Potassco::BasicCharBuffer& {
    return buffer.append(n1).append('/').append(n2).append("|"sv);
}
static auto appendBasicStats(Potassco::BasicCharBuffer& buffer, const Solver& s, uint64_t conflicts,
                             uint64_t choices) -> Potassco::BasicCharBuffer& {
    using Potassco::num;
    addBasicCol(buffer, num<8>(s.numConstraints()), num<-8>(s.numLearntConstraints()));
    return addBasicCol(buffer, num<10>(conflicts), num<-6, 3>(ratio(conflicts, choices)));
}
static auto formatEvent(Potassco::BasicCharBuffer& buffer, const BasicSolveEvent& ev) -> Potassco::BasicCharBuffer& {
    using Potassco::num;
    const Solver& s     = *ev.solver;
    auto          fixed = s.decisionLevel() > 0 ? s.levelStart(1) : s.numAssignedVars();
    startSolverEvent(buffer, s, static_cast<char>(ev.op));
    addBasicCol(buffer, num<7>(s.numFreeVars()), num<-7>(fixed));
    appendBasicStats(buffer, s, s.stats.conflicts, s.stats.choices);
    return addBasicCol(buffer, num<8>(ev.cLimit <= UINT32_MAX ? static_cast<int64_t>(ev.cLimit) : -1),
                       num<-10>(ev.lLimit != UINT32_MAX ? static_cast<int64_t>(ev.lLimit) : -1));
}
static auto formatEvent(Potassco::BasicCharBuffer& buffer, const SolveTestEvent& ev) -> Potassco::BasicCharBuffer& {
    const Solver& s     = *ev.solver;
    auto          fixed = s.decisionLevel() > 0 ? s.levelStart(1) : s.numAssignedVars();
    startSolverEvent(buffer, *ev.solver, "FP"[ev.partial]);
    std::string_view r = ev.result < 0 ? "?" : ev.result == 0 ? "N" : "Y";
    addBasicCol(buffer, Potassco::num<7>(s.numVars() - fixed), Potassco::str<-7>(r));
    appendBasicStats(buffer, s, ev.conflicts(), ev.choices());
    buffer.append(Potassco::num<8>(ev.hcc, ':')).append(Potassco::elapsed<9>(Output::ElapsedTime{ev.time}));
    return buffer.append(" |"sv);
}
#if CLASP_HAS_THREADS
static auto formatEvent(Potassco::BasicCharBuffer& buffer, const mt::MessageEvent& ev) -> Potassco::BasicCharBuffer& {
    using EventType = mt::MessageEvent;
    auto msg        = std::string_view(ev.msg).substr(0, 30);
    startSolverEvent(buffer, *ev.solver, 'X').append(' ').append(Potassco::str<-31>(msg));
    auto str = "completed"sv;
    if (ev.op != EventType::completed) {
        str = ev.op == EventType::sent ? "sent"sv : "received"sv;
        buffer.append(Potassco::str<-38>(str));
    }
    else {
        buffer.append(Potassco::str<-20>(str))
            .append(" in "sv)
            .append(Potassco::elapsed<13>(Output::ElapsedTime{ev.time}));
    }
    return buffer.append(" |"sv);
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
auto Output::ColorStyleSpec::defaultColors() -> ColorStyleSpec {
    ColorStyleSpec ret;
    ret.trace_ = Spec{} | TextStyle::Color::bright_magenta;
    ret.info_  = TextStyle::Color::green | TextStyle::Emphasis::bold;
    ret.note_  = Spec{} | TextStyle::Color::bright_yellow;
    ret.warn_  = TextStyle::Color::bright_yellow | TextStyle::Emphasis::bold;
    ret.err_   = TextStyle::Color::red | TextStyle::Emphasis::bold;
    return ret;
}
Output::ColorStyleSpec::ColorStyleSpec(std::string_view style) {
    static_assert(alignof(Spec) == 1);
    static_assert(offsetof(ColorStyleSpec, info_) == sizeof(Spec));
    if (style.starts_with("*:")) {
        *this = defaultColors();
        style.remove_prefix(2);
    }
    if (not style.empty()) {
        try {
            static constexpr auto keys = {"trace="sv, "info="sv, "note="sv, "warning="sv, "error="sv};
            for (;;) {
                auto kIt = std::ranges::find_if(keys, [&](std::string_view k) { return style.starts_with(k); });
                POTASSCO_CHECK(kIt != keys.end(), std::errc::invalid_argument, "unknown color key '%" PRIsv "'",
                               PRI_SV(style));
                auto  next = style.find(':', kIt->size());
                auto* ts   = &trace_ + std::distance(keys.begin(), kIt);
                *ts        = Spec::fromString(style.substr(0, next), kIt->size());
                if (next == std::string_view::npos) {
                    break;
                }
                style = style.substr(next + 1);
            }
        }
        catch (const std::exception& error) {
            const auto* what = error.what();
            const auto* eol  = strchr(error.what(), '\n');
            eol != nullptr ? throw std::invalid_argument(std::string(what, static_cast<std::size_t>(eol - what)))
                            : throw std::invalid_argument(what);
        }
    }
}
OutputSink::OutputSink(FILE* file) {
    POTASSCO_CHECK(file, std::errc::bad_file_descriptor, "invalid output sink");
    static auto vtab = VTable{
        .write = +[](void* f, std::string_view s) { return std::fwrite(s.data(), 1, s.size(), static_cast<FILE*>(f)); },
        .flush = +[](void* f) { std::fflush(static_cast<FILE*>(f)); },
        .file  = +[](void* f) { return static_cast<FILE*>(f); },
    };
    vptr_ = &vtab;
    impl_ = file;
}
OutputSink::OutputSink(std::ostream& os) {
    static auto vtab = VTable{
        .write = +[](void* o, std::string_view s) { return (*static_cast<std::ostream*>(o) << s) ? s.size() : 0; },
        .flush = +[](void* o) { static_cast<std::ostream*>(o)->flush(); },
        .file  = &noFile,
    };
    vptr_ = &vtab;
    impl_ = &os;
}
Output::Output(OutputSink sink, uint32_t verb, Mode mode) : sink_(sink) {
    result_[res_unknown] = "UNKNOWN";
    result_[res_sat]     = "SATISFIABLE";
    result_[res_unsat]   = "UNSATISFIABLE";
    result_[res_opt]     = "OPTIMUM FOUND";
    setCallQuiet(print_no);
    setVerbosity(verb);
    setMode(mode);
    style_      = {};
    time_.start = RealTime::getTime();
}
Output::~Output() = default;
void Output::setVerbosity(uint32_t verb) { verbose_ = verb; }
void Output::setModelQuiet(PrintLevel model) { quiet_[0] = static_cast<uint8_t>(model); }
void Output::setOptQuiet(PrintLevel opt) { quiet_[1] = static_cast<uint8_t>(opt); }
void Output::setCallQuiet(PrintLevel call) { quiet_[2] = static_cast<uint8_t>(call); }
void Output::setMode(Mode m) { mode_ = static_cast<uint8_t>(m); }
auto Output::elapsedTime() const -> ElapsedTime { return ElapsedTime{RealTime::diffTime(time_.start)}; }
auto Output::diffTime(double end, double start) -> ElapsedTime { return ElapsedTime{RealTime::diffTime(end, start)}; }
void Output::splitStateTime() { time_.split = RealTime::getTime(); }
auto Output::write(std::string_view s) -> std::size_t { return sink_.write(s); }
void Output::flush() { return sink_.flush(); }
auto Output::lockSink() -> SinkLock {
    if (auto* sinkFile = sink_.file(); sinkFile) {
        Potassco::lockFile(sinkFile);
        return SinkLock{sinkFile, +[](void* f) {
                            fflush(static_cast<FILE*>(f));
                            Potassco::unlockFile(static_cast<FILE*>(f));
                        }};
    }
    else {
        // The sink is not (directly) associated with a FILE object.
        // Misuse the lock of stdout to guarantee synchronization between threads sharing this output object.
        // Note that this could be a pessimization because it could also affect unrelated threads.
        Potassco::lockFile(stdout);
        return SinkLock{sinkFile, +[](void* self) {
                            static_cast<Output*>(self)->flush();
                            Potassco::unlockFile(stdout);
                        }};
    }
}
void Output::enableColor(const ColorStyleSpec& spec) {
    using namespace std::literals;
    style_      = {};
    auto enable = spec != ColorStyleSpec{};
    if (enable) {
        style_.trace = spec.trace();
        style_.info  = spec.info();
        style_.note  = spec.note();
        style_.warn  = spec.warn();
        style_.err   = spec.err();
    }
    doEnableColor(enable);
}
void Output::start(std::string_view solver, std::string_view version, std::span<const std::string> input) {
    time_       = {};
    time_.start = RealTime::getTime();
    state_      = Event::Subsystem::subsystem_facade;
    doStart(solver, version, input);
}
void Output::transition(ElapsedTime elapsed, Event::Subsystem to) {
    if (to != state_ || to == Event::subsystem_facade) {
        double ts = RealTime::getTime();
        if (auto es = std::exchange(state_, to); es != Event::subsystem_facade) {
            exitState(elapsed, es, diffTime(ts, time_.enter), diffTime(ts, time_.split));
        }
        time_.enter = time_.split = ts;
        switch (to) {
            case Event::subsystem_facade : stopStep(elapsed, diffTime(ts, time_.step)); break;
            case Event::subsystem_load   : [[fallthrough]];
            case Event::subsystem_prepare: [[fallthrough]];
            case Event::subsystem_solve  : enterState(elapsed, to); break;
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
        time_.step = time_.enter = time_.split = RealTime::getTime();
        startStep(t, static_cast<uint32_t>(ev->facade->step()));
    }
    else if (event.verb <= verbosity() && event.system != Event::subsystem_facade) {
        if (event.system == state_) {
            auto ts = RealTime::getTime();
            printProgress(t, event, diffTime(ts, time_.enter), diffTime(ts, time_.split));
        }
        else if (const auto* enter = event_cast<EnterEvent>(event)) {
            transition(t, static_cast<Event::Subsystem>(enter->system));
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
        transition(t, Event::subsystem_facade);
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
    if (modelQ() == print_all || optQ() == print_all) {
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
void Output::enterState(ElapsedTime, Event::Subsystem) {}
void Output::exitState(ElapsedTime, Event::Subsystem, ElapsedTime, ElapsedTime) {}
void Output::printProgress(ElapsedTime, const Event&, ElapsedTime, ElapsedTime) {}
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
struct JsonOutput::JString {
    static constexpr auto json_special = "\b\f\n\r\t\"\\"sv;
    static constexpr auto json_replace = "bfnrt\"\\"sv;
    //
    friend auto toChars(Potassco::BasicCharBuffer& buffer, const JString& js) -> Potassco::BasicCharBuffer& {
        buffer.open(js.style);
        auto s = js.str;
        auto p = s.find_first_of(json_special);
        buffer.append('"').append(s.substr(0, p));
        s.remove_prefix(std::min(p, s.size()));
        for (auto c : s) {
            buffer.push_back(c);
            if (p = json_special.find(c); p != std::string_view::npos) {
                buffer.back() = '\\';
                buffer.push_back(json_replace[p]);
            }
        }
        buffer.append('"').close();
        return buffer;
    }
    std::string_view           str;
    const Potassco::TextStyle& style;
};
JsonOutput::JsonOutput(OutputSink sink, uint32_t v, Mode mode) : Output(sink, std::min(v, 1u), mode), open_("") {
    objStack_.reserve(10);
}
JsonOutput::~JsonOutput() { JsonOutput::doShutdown(); }
auto JsonOutput::jString(std::string_view s) const -> JString { return JString{s, style().trace}; }
auto JsonOutput::appendKey(Buffer& buffer, std::string_view key) -> Buffer& {
    return buffer.append(std::exchange(open_, ",\n"))
        .append(indent(), ' ')
        .append(Potassco::styled(Potassco::quoted(key), style().info))
        .append(": "sv);
}

template <typename V>
void JsonOutput::printKeyValue(std::string_view k, const V& v, const TextStyle* valStyle) {
    Buffer buffer;
    appendKey(buffer, k).open(valStyle ? *valStyle : style().def);
    if constexpr (std::is_same_v<V, std::string_view> || std::is_same_v<V, std::string>) {
        assert(v.find_first_of(JString::json_special) == std::string_view::npos);
        buffer.append(Potassco::quoted(v));
    }
    else if constexpr (std::is_floating_point_v<V>) {
        if (std::isnan(v)) {
            buffer.append("null"sv);
        }
        else if (std::round(v) == v) {
            buffer.append(static_cast<int64_t>(v));
        }
        else {
            buffer.append(Potassco::num<0, 3>(v));
        }
    }
    else {
        static_assert(std::is_unsigned_v<V>);
        buffer.append(static_cast<uint64_t>(v));
    }
    write(buffer.close());
}
void JsonOutput::printKeyValue(std::string_view k, ElapsedTime v) {
    if (isValidTime(v.count())) {
        printKeyValue(k, v.count(), &style().trace);
    }
}

void JsonOutput::pushObject(std::string_view k, ObjType t, bool startIndent) {
    Buffer buffer;
    k.empty() ? buffer.append(open_).append(indent(), ' ') : appendKey(buffer, k);
    char o     = t == type_object ? '{' : '[';
    objStack_ += o;
    open_      = "";
    buffer.append(o).append('\n').append(startIndent ? indent() : 0, ' ');
    write(buffer.view());
    if (startIndent) {
        flush();
    }
}
char JsonOutput::popObject() {
    assert(not objStack_.empty());
    char o = objStack_.back();
    objStack_.pop_back();
    Buffer buffer;
    buffer.append("\n"sv).append(indent(), ' ').push_back(o == '{' ? '}' : ']');
    write(buffer.view());
    open_ = ",\n";
    return o;
}
void JsonOutput::startWitness(ElapsedTime time) {
    assert(not objStack_.empty());
    if (objStack_.back() != '[') {
        pushObject("Witnesses"sv, type_array);
    }
    pushObject();
    printKeyValue("Time"sv, time);
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
    Buffer buf;
    for (auto x : std::ranges::join_view(std::array{sum, SumView{last, last != nullptr}})) {
        buf.append(x).append(", "sv);
    }
    write(buf.view().substr(0, buf.size() - 2));
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
    printKeyValue("Solver"sv, std::string(solver).append(" version ").append(version), &style().warn);
    pushObject("Input"sv, type_array, true);
    if (not input.empty()) {
        Buffer buffer;
        for (const auto& x : input) { buffer.append(jString(x)).append(", "sv); }
        write(buffer.view().substr(0, buffer.size() - 2));
    }
    popObject();
    pushObject("Call"sv, type_array);
}
void JsonOutput::printModel(ElapsedTime elapsed, const SharedContext& ctx, const Model& m, ModelFlag flags) {
    assert(flags != model_quiet);
    startWitness(elapsed);
    if (Potassco::test(flags, model_values)) {
        pushObject("Value"sv, type_array, true);
        Buffer buffer;
        m.visitWitness(ctx.output, [&, first = true](OutputTable::Type, Literal lit, const char* name) mutable {
            buffer.append(std::exchange(first, false) ? "" : ", ");
            if (name) {
                buffer.append(jString(name));
            }
            else {
                buffer.append(toInt(lit));
            }
            if (buffer.size() > 80) {
                write(buffer.view());
                buffer.clear();
            }
        });
        buffer.empty() || write(buffer.view());
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
    if (m.lb && m.lower.active() && optQ() == print_all) {
        startWitness(elapsed);
        auto lower = m.lower;
        auto first = m.hasCosts() && m.costs.size() > lower.level ? m.costs.subspan(0, lower.level) : SumView();
        printSum("Lower"sv, first, &lower.bound);
        endWitness();
    }
}
void JsonOutput::startStep(ElapsedTime elapsed, uint32_t) {
    popUntil(2u);
    pushObject({}, type_object);
    printKeyValue("Start"sv, elapsed);
    flush();
}
void JsonOutput::stopStep(ElapsedTime elapsed, ElapsedTime) {
    assert(not objStack_.empty());
    popUntil(3u);
    printKeyValue("Stop"sv, elapsed);
    flush();
}
void JsonOutput::printSummary(const ClaspFacade::Summary& run, bool final) {
    popUntil(final ? 1u : 3u);
    printKeyValue("Result"sv, std::string_view{resultString(run)}, final ? &style().warn : &style().note);
    if (verbosity()) {
        if (run.result.interrupted()) {
            printKeyValue(interruptedString(run.result), 1u);
        }
        pushObject("Models"sv);
        printKeyValue("Number"sv, run.numEnum, &style().note);
        printKeyValue("More"sv, run.complete() ? "no"sv : "yes"sv, &style().note);
        if (run.sat()) {
            if (run.consequences()) {
                printKeyValue(run.consequences(), run.complete() ? "yes"sv : "unknown"sv, &style().note);
                printCons(run.ctx(), *run.model());
            }
            if (run.optimize()) {
                printKeyValue("Optimum"sv, run.optimum() ? "yes"sv : "unknown"sv, &style().note);
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
        printKeyValue("Total"sv, ElapsedTime{run.totalTime});
        printKeyValue("Solve"sv, ElapsedTime{run.solveTime});
        printKeyValue("Model"sv, ElapsedTime{run.satTime});
        printKeyValue("Unsat"sv, ElapsedTime{run.unsatTime});
        printKeyValue("CPU"sv, ElapsedTime{run.cpuTime});
        if (run.killTime != 0.0) {
            printKeyValue("Signal"sv, ElapsedTime{run.killTime});
        }
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
    for (auto i : irange(1u, BodyStats::numKeys())) {
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
        write("\n"sv);
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
    printKeyValue("CPU"sv, ElapsedTime{stx.cpuTime});
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
        printKeyValue("Type"sv, names[i], &style().trace);
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
static constexpr auto numChars(uint64_t x) -> uint32_t {
    auto r = 1u;
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
template <std::integral T>
static constexpr auto numChars(T n) -> uint32_t {
    auto x = n >= 0 ? static_cast<uint64_t>(n) : ~static_cast<uint64_t>(n) + 1;
    return numChars(x) + (n < 0);
}
namespace {
template <auto W = 7, auto P = 2, typename T>
constexpr auto pct(const T& arg) -> Potassco::Field {
    return Potassco::num<W, P>(arg, '%');
}
constexpr auto models(uint64_t n, bool complete) -> Potassco::Field {
    return Potassco::num<0>(n, complete ? static_cast<char>(0) : '+');
}
using Potassco::keyed;
constexpr auto optkv(bool c, std::string_view k, const auto& v) {
    return c ? std::make_optional(Potassco::keyed(k, v)) : std::nullopt;
}
struct Jumps {
    friend auto toChars(Potassco::BasicCharBuffer& buffer, const Jumps& j) -> Potassco::BasicCharBuffer& {
        return buffer.appendSep(" ", keyed("Average", Potassco::num<5, 2>(j.avg)),
                                keyed("Max", Potassco::num<3>(j.max)), keyed("Sum", Potassco::num<6>(j.sum)),
                                optkv(j.ratio >= 0.0, "Ratio", pct(j.ratio)));
    }
    double   avg{};
    uint32_t max{};
    uint64_t sum{};
    double   ratio{-1.0};
};
struct Bounds {
    friend auto toChars(Potassco::BasicCharBuffer& buf, const Bounds& c) -> Potassco::BasicCharBuffer& {
        auto s  = std::string_view{&c.sep, 1};
        auto sx = c.sepSuffix;
        if (c.hasLower) {
            for (auto uSize = size32(c.upper), lSize = size32(c.lower); auto i : irange(std::max(uSize, lSize))) {
                if (i > 0) {
                    buf.append(s).append(sx);
                }
                appendBound(buf, i < lSize ? c.lower[i] : weight_sum_max, i < uSize ? c.upper[i] : weight_sum_max,
                            false);
            }
        }
        else {
            for (auto i : irange(std::min(size32(c.upper), c.lb->level))) {
                appendBound(buf, weight_sum_max, c.upper[i], true);
                buf.append(s).append(sx);
            }
            appendBound(buf, c.lb->bound, c.upper.size() > c.lb->level ? c.upper[c.lb->level] : weight_sum_max, true);
        }
        return buf;
    }
    static void appendBound(Potassco::BasicCharBuffer& buffer, Wsum_t lower, Wsum_t upper, bool width) {
        if (lower >= upper) {
            buffer.append(upper);
        }
        else {
            auto w = width && upper != weight_sum_max ? numChars(upper) : 6 * width;
            auto n = Potassco::num(lower, static_cast<Potassco::Field::Width>(w));
            buffer.append("["sv).append(n).append(";"sv);
            if (upper != weight_sum_max) {
                buffer.append(upper);
            }
            else {
                buffer.append(width ? "inf"sv : "*"sv);
            }
            buffer.append("]"sv);
        }
    }

    union {
        const LowerBound* lb = nullptr;
        SumView           lower;
    };
    SumView          upper;
    std::string_view sepSuffix;
    char             sep      = ' ';
    bool             hasLower = false;
};
auto bounds(SumView lower, SumView upper, char sep = ' ', std::string_view sepSuffix = {}) -> Bounds {
    return {.lower = lower, .upper = upper, .sepSuffix = sepSuffix, .sep = sep, .hasLower = true};
}
auto bounds(const LowerBound& lb, SumView upper) -> Bounds {
    return {.lb = &lb, .upper = upper, .sepSuffix = "", .sep = ' '};
}
} // namespace
constexpr auto row_sep = "------------------------------------------------------------------------------------------|";
constexpr auto acc_sep = "====================================== Accumulation ======================================|";
constexpr auto h1_ln1  = "ID:T       Vars           Constraints         State            Limits            Time     |";
constexpr auto h1_ln2  = "       #free/#fixed   #problem/#learnt  #conflicts/ratio #conflict/#learnt                |";
constexpr auto h2_ln1  = "ID:T  Info                           Info                                        Time     |";
constexpr auto sat_pre = "Sat-Prepro";
static constexpr void checkArg(bool req, const char* error) {
    if (not req) {
        throw std::invalid_argument(error);
    }
}
static auto matchNum(std::string_view& arg, const char* what) -> int {
    int n;
    checkArg(Potassco::matchNum(arg, nullptr, &n), what);
    return n;
}
static constexpr auto getIfsSuffix(std::string_view prefix, char ifs) -> std::string_view {
    return ifs != '\n' || prefix.ends_with('\n') ? ""sv : prefix;
}
static auto prettify(std::span<const std::string> input) -> std::string {
    std::string res;
    if (const auto& str = input.front(); str.size() < 40) {
        res = str;
    }
    else {
        res.assign("...").append(str.end() - 38, str.end());
    }
    if (input.size() > 1) {
        res.append(" ...");
    }
    return res;
}

auto TextOutput::CatAtom::fromString(std::string_view fmt) -> CatAtom {
    using namespace std::literals;
    CatAtom result;
    auto*   fmtPos = &result.atomSep_;
    while (not fmt.empty()) {
        auto c = fmt.front();
        fmt.remove_prefix(1);
        checkArg(c != '\n', "new line not allowed");
        result.buffer_.push_back(c);
        if (c == ':') {
            checkArg(fmtPos == &result.atomSep_ || fmt.empty(), "too many separators");
            if (not result.buffer_.starts_with(':')) {
                result.buffer_.pop_back();
            }
            if (not fmt.empty()) {
                result.varStart_ = size32(result.buffer_);
            }
            fmtPos = &result.varSep_;
        }
        else if (c == '%' && not fmt.empty()) {
            if (int n; Potassco::matchNum(fmt, nullptr, &n)) {
                checkArg(*fmtPos == UINT32_MAX, "too many arguments");
                checkArg(n == 0, "argument out of bounds");
                result.buffer_.pop_back();
                *fmtPos = size32(result.buffer_);
            }
            else {
                result.buffer_.append(fmt.substr(0, not fmt.starts_with('%')));
                fmt.remove_prefix(1);
            }
        }
        else if (c == '\\' && fmt.starts_with(':')) {
            result.buffer_.back() = ':';
            fmt.remove_prefix(1);
        }
    }
    if (result.hasAtom() && fmtPos == &result.atomSep_) {
        result.varStart_ = 0;
        result.varSep_   = result.atomSep_;
    }
    return result;
}
TextOutput::CatAtom::operator bool() const noexcept { return hasAtom() || hasVar(); }
auto TextOutput::CatAtom::hasAtom() const -> bool { return not buffer_.empty() && not buffer_.starts_with(':'); }
auto TextOutput::CatAtom::hasVar() const -> bool { return varStart_ != UINT32_MAX; }
void TextOutput::CatAtom::formatTo(Buffer& buf, const auto& v, uint32_t s, uint32_t m, uint32_t e) const {
    if (auto fmt = std::string_view{buffer_}; s == e) {
        buf.append(v);
    }
    else if (m != UINT32_MAX) {
        buf.append(fmt.substr(s, m - s)).append(v).append(fmt.substr(m, e - m));
    }
    else {
        buf.append(fmt.substr(s, e - s));
    }
}
void TextOutput::CatAtom::formatTo(Buffer& buf, std::string_view atom) const {
    auto e = (varStart_ != 0 ? varStart_ : size32(buffer_)) * hasAtom();
    formatTo(buf, atom, 0u, atomSep_, e);
}
void TextOutput::CatAtom::formatTo(Buffer& buf, Literal lit) const {
    formatTo(buf.append(lit.sign() ? "-" : ""), lit.var(), varStart_, varSep_, std::max(varStart_, size32(buffer_)));
}
struct TextOutput::Key {
    friend auto toChars(Potassco::BasicCharBuffer& buffer, const Key& k) -> Potassco::BasicCharBuffer& {
        buffer.append(k.ind, ' ');
        if (auto x = Potassco::clear_bit(k.ext, arr_bit); x == k.ext) {
            auto w = -static_cast<int>(std::max(x, k.ind) - k.ind);
            buffer.append(Potassco::str(k.key, Potassco::Field::Width{w}));
        }
        else {
            buffer.append("[").append(k.key).append(not k.key.empty() ? " " : "").append(x).append("]");
        }
        return buffer.append(k.sep);
    }
    Key(const char* k) : Key(k, 0, 0) {} // NOLINT
    // NOLINTNEXTLINE(bugprone-easily-swappable-parameters)
    Key(std::string_view k, uint32_t w, uint32_t i = 0, std::string_view t = ": ") : key(k), sep(t), ext(w), ind(i) {}
    static Key indent(std::string_view t, uint32_t i = 2) { return {t, 0, i}; }
    static Key array(std::string_view n, uint32_t idx, std::string_view t = ": ") {
        return {n, Potassco::set_bit(idx, arr_bit), 0, t};
    }

    static constexpr auto arr_bit = 31;
    std::string_view      key;
    std::string_view      sep;
    uint32_t              ext{0};
    uint32_t              ind{0};
};
TextOutput::CatTemplate::CatTemplate(std::string_view caption, std::string_view id, uint32_t arity,
                                     std::string_view fmt)
    : capStart_(static_cast<uint32_t>(id.size()))
    , fmtStart_(static_cast<uint32_t>(id.size() + caption.size()))
    , arity_(static_cast<uint8_t>(arity)) {
    checkArg(not id.empty(), "predicate id must not be empty");
    checkArg(arity_ == arity, "arity out of bounds");
    auto inId = static_cast<char>(0);
    for (auto c : id) {
        checkArg(c == '_' || c == '\'' || (inId && std::isalnum(static_cast<unsigned char>(c))) ||
                     std::islower(static_cast<unsigned char>(inId = c)),
                 "invalid character in predicate id");
    }
    checkArg(inId != 0, "predicate id must have lowercase letter");
    auto pos = caption.find('\n');
    checkArg(pos == std::string_view::npos || caption.find_first_not_of('\n', pos) == std::string_view::npos,
             "new line not allowed in caption");
    data_.reserve(caption.size() + id.size() + fmt.size());
    data_.append(id).append(caption);
    while (not fmt.empty()) {
        auto c = fmt.front();
        fmt.remove_prefix(1);
        checkArg(c != '\n', "new line not allowed in format string");
        data_.push_back(c);
        if (c == '%') {
            if (not fmt.starts_with('%')) {
                auto argId = static_cast<uint32_t>(matchNum(fmt, "argument number expected"));
                checkArg(argId < arity, "argument out of bounds");
                maxArg_ = std::max(maxArg_, static_cast<uint8_t>(argId));
                data_.push_back(static_cast<char>(static_cast<uint8_t>(argId)));
            }
            else {
                data_.push_back(c);
                fmt.remove_prefix(1);
            }
        }
    }
}
TextOutput::CatTemplate::operator bool() const noexcept { return not data_.empty(); }
auto TextOutput::CatTemplate::fromString(std::string_view str, std::string_view defCap,
                                         std::string_view defFmt) -> CatTemplate {
    if (not str.empty() && str != ":"sv) { // [<cap>,]<id>/<arity>[:<fmt>]
        if (auto pos = str.find(','); pos != std::string_view::npos) {
            defCap = str.substr(0, pos);
            str.remove_prefix(pos + 1);
        }
        auto id = str.substr(0, str.find('/'));
        checkArg(str.size() > id.size() && str[id.size()] == '/', "'/' expected after predicate name");
        str.remove_prefix(id.size() + 1);
        auto arity = static_cast<uint32_t>(matchNum(str, "arity expected"));
        if (not str.empty()) {
            checkArg(str.starts_with(':'), "':' expected after predicate arity");
            str.remove_prefix(1);
            defFmt = str;
        }
        return {defCap, id, arity, defFmt};
    }
    return {};
}
bool TextOutput::CatTemplate::matches(std::string_view otherId, int otherArity) const noexcept {
    return std::cmp_equal(otherArity, arity()) && otherId == id();
}
auto TextOutput::CatTemplate::start(Buffer& buffer, char sep, TextStyle st) const -> Buffer& {
    if (auto cap = caption(); not cap.empty()) {
        auto sepV = std::string_view{&sep, 1};
        if (std::isspace(static_cast<unsigned char>(cap.back()))) {
            sep = cap.back();
            cap.remove_suffix(1);
        }
        buffer.append(Potassco::styled(cap, st)).append(sepV);
    }
    return buffer;
}
auto TextOutput::CatTemplate::formatTo(Buffer& buf, std::span<std::string_view> args) const -> Buffer& {
    for (auto fmt = std::string_view{data_}.substr(fmtStart_);;) {
        auto pos = fmt.find('%');
        buf.append(fmt.substr(0, pos));
        if (pos == std::string_view::npos) {
            return buf;
        }
        fmt.remove_prefix(pos + 1);
        if (fmt.starts_with('%')) {
            buf.push_back('%');
        }
        else {
            auto argId = static_cast<uint8_t>(fmt.front());
            checkArg(argId < args.size() && argId <= maxArg(), "argument out of bounds");
            buf.append(args[argId]);
        }
        fmt.remove_prefix(1);
    }
}
TextOutput::CatStep::CatStep(Arg timeArg, std::string_view stepCaption)
    : caption_(stepCaption)
    , arg_(timeArg)
    , active_(true) {
    checkArg(stepCaption.find('\n') == std::string_view::npos, "new line not allowed");
}
TextOutput::CatStep::operator bool() const noexcept { return active_; }
auto TextOutput::CatStep::fromString(std::string_view str) -> CatStep {
    if (not str.empty() && str != ":"sv) {
        auto argStr = str.substr(0, str.find(':'));
        auto arg    = Arg::last;
        if (argStr == Potassco::enum_name(Arg::first)) {
            arg = Arg::first;
        }
        else {
            checkArg(argStr == Potassco::enum_name(Arg::last), "argument position 'first' or 'last' expected");
        }
        str = str.substr(argStr.size());
        return CatStep{arg, str.empty() ? "State"sv : str.substr(1)};
    }
    return {};
}
TextOutput::TextOutput(OutputSink sink, const Options& options)
    : Output(sink, options.verbosity, options.mode)
    , fmtAssign_(options.catAssign)
    , fmtCost_(options.catCosts)
    , fmtStep_(options.catStep)
    , predSep_(options.predSep) {
    static constexpr auto asp_prefix      = Prefix{};
    static constexpr auto sat_prefix      = Prefix{.comment = "c "sv, .cost = "o "sv, .result = "s "sv};
    static constexpr auto asp_comp_prefix = Prefix{.comment = "% "sv, .cost = "COST "sv, .result = ""sv};
    if (fmt_ = options.format; fmt_ == format_aspcomp) {
        prefix_  = &asp_comp_prefix;
        fmtAtom_ = CatAtom::fromString("%0.");
        setResultString(res_sat, "");
        setResultString(res_unsat, "INCONSISTENT");
        setResultString(res_opt, "OPTIMUM");
        setModelQuiet(print_best);
        setOptQuiet(print_best);
    }
    else if (fmt_ == format_sat09 || fmt_ == format_pb09 || fmt_ == format_maxsat09) {
        prefix_ = &sat_prefix;
        if (fmt_ == format_maxsat09) {
            setResultString(res_sat, "UNKNOWN");
        }
        else if (fmt_ == format_pb09) {
            fmtAtom_ = CatAtom::fromString(":x%0");
            setModelQuiet(print_best);
        }
    }
    else {
        prefix_ = &asp_prefix;
    }
    if (options.catAtom) {
        fmtAtom_ = options.catAtom;
    }
    ifs_      = options.ifs;
    width_    = 13;
    progress_ = {};
}
TextOutput::~TextOutput() = default;
template <typename V, typename... Args>
auto TextOutput::printKeyValue(const TextStyle& st, Key k, const V& v, const Args&... args) -> std::size_t {
    Buffer buffer;
    if (k.ext == 0) {
        k.ext = width_;
    }
    openComment(buffer, st).append(k);
    auto vs = buffer.size();
    buffer.append(v);
    if constexpr (sizeof...(args)) {
        static_assert(not(std::is_same_v<Args, bool> || ...), "did you mean optkv?");
        auto sz = buffer.size();
        if (k.ext == width_) {
            buffer.append(8u - std::min(buffer.size() - vs, 8u), ' ');
        }
        buffer.append(" ("sv);
        if (auto ext = buffer.size(); buffer.appendSep(" "sv, args...).size() > ext) {
            buffer.push_back(')');
        }
        else {
            buffer.pop(ext - sz);
        }
    }
    return write(buffer.close());
}
template <typename... Args>
auto TextOutput::print(std::string_view prefix, const TextStyle& st, Term t, const Args&... args) -> std::size_t {
    Buffer buffer;
    buffer.append(prefix).open(st, t != Term{} ? static_cast<int>(t) : Buffer::eof);
    (buffer.append(args), ...);
    return write(buffer.close());
}
auto TextOutput::openComment(Buffer& buf, const TextStyle& st, char term) const -> Buffer& {
    return buf.append(prefix_->comment).open(st, term ? static_cast<int>(term) : Buffer::eof);
}
void TextOutput::setModelPrinter(ModelPrinter printer) { onModel_ = std::move(printer); }
void TextOutput::updateProgress(SolveProgress::Ev eventId, int nLines) {
    if (eventId >= 0 && (eventId != progress_.last || progress_.lines <= 0)) {
        auto eh = 1 + (static_cast<uint32_t>(eventId) == Event::eventId<LogEvent>());
        auto ph = header_.empty() ? 3 : static_cast<int>(header_.view().front());
        if (progress_.lines <= 0 || eh < ph || (eh != ph && progress_.lines < 10)) {
            if (eh != ph) {
                header_.clear();
                header_.push_back(static_cast<char>(eh));
                const auto& st = style().trace;
                openComment(header_, st).append(row_sep).close();
                openComment(header_, st).append(eh == 1 ? h1_ln1 : h2_ln1).close();
                if (eh == 1) {
                    openComment(header_, st).append(h1_ln2).close();
                }
                openComment(header_, st).append(row_sep).close();
            }
            write(header_.view().substr(1));
            progress_.lines = 20;
        }
        else {
            printComment(style().trace, row_sep);
        }
    }
    else if (progress_.last == SolveProgress::ev_none) {
        nLines  = 0;
        eventId = SolveProgress::ev_none;
    }
    else if (eventId == SolveProgress::ev_clear && progress_.last >= 0 && verbosity() > 1) {
        printComment(style().trace, row_sep);
    }
    progress_.last   = eventId;
    progress_.lines -= nLines;
}
// NOLINTBEGIN(readability-make-member-function-const,readability-convert-member-functions-to-static)
void TextOutput::printEnter(const char* message, Term term) {
    printComment(style().def, term, Key{message, width_});
    flush();
}
void TextOutput::printExit(ElapsedTime stateElapsed) {
    write(Buffer{}.open(style().def, '\n').append(stateElapsed).close());
}
void TextOutput::printMeta(const SharedContext& ctx, const Model& m) {
    if (m.consequences()) {
        auto [low, est] = m.numConsequences(ctx);
        printComment(optStyle(m.def || est == 0), "Consequences: ["sv, low, ';', low + est, ']');
    }
    if (m.hasCosts()) {
        auto key    = fmt_ == format_asp ? "Optimization: "sv : ""sv;
        auto prefix = prefix_->cost;
        print(prefix, optStyle(m.opt), Term{'\n'}, key, bounds({}, m.costs, ifs_, getIfsSuffix(prefix, ifs_)));
    }
}
void TextOutput::printPreproEvent(ElapsedTime stateTime, const Event& ev, ElapsedTime split) {
    using SatPreProgress = SatPreprocessor::Progress;
    if (const auto* sat = event_cast<SatPreProgress>(ev)) {
        progress_.last = sat->id;
        switch (static_cast<SatPreProgress::EventOp>(sat->op)) {
            default:
                printComment(style().def, Term{'\r'}, Key{sat_pre, width_}, static_cast<char>(sat->op), ": "sv,
                             Potassco::num<8>(sat->cur), '/', Potassco::num<-8>(sat->max));
                flush();
                break;
            case SatPreProgress::event_enter:
                printExit(stateTime);
                printEnter(sat_pre, Term{'\r'});
                splitStateTime();
                break;
            case SatPreProgress::event_exit:
                auto* p = sat->self;
                printKeyValue(sat_pre, split, keyed("ClRemoved", p->stats.clRemoved),
                              keyed("ClAdded", p->stats.clAdded), keyed("LitsStr", p->stats.litsRemoved));
                progress_.last = SolveProgress::ev_none;
                break;
        }
    }
}
void TextOutput::printSolveEvent(ElapsedTime elapsed, const Event& ev, ElapsedTime stateTime) {
    Buffer      line;
    const auto& ts      = style().def;
    auto        eventId = static_cast<int>(ev.id);
    if (const auto* be = event_cast<BasicSolveEvent>(ev)) {
        if ((verbosity() & 1) == 0) {
            return;
        }
        formatEvent(openComment(line, ts), *be);
    }
    else if (const auto* te = event_cast<SolveTestEvent>(ev)) {
        if ((verbosity() & 4) == 0) {
            return;
        }
        formatEvent(openComment(line, ts, te->result == -1 ? '\r' : '\n'), *te);
    }
#if CLASP_HAS_THREADS
    else if (const auto* me = event_cast<mt::MessageEvent>(ev)) {
        formatEvent(openComment(line, ts), *me);
        eventId = static_cast<int>(Event::eventId<LogEvent>());
    }
#endif
    else if (const auto* log = event_cast<LogEvent>(ev)) {
        openComment(line, ts);
        auto maxW = 37u + line.size();
        auto msg  = std::string_view{log->msg}.substr(0, 38);
        startSolverEvent(line, *log->solver, 'L').append(" [Solving+"sv).append(stateTime).append("]"sv);
        line.append(line.size() < maxW ? maxW - line.size() : 0u, ' ').append(Potassco::str<-38>(msg)).append(" |"sv);
    }
    if (line.empty()) {
        return;
    }
    line.append(" "sv).append(Potassco::elapsed<10>(elapsed)).append(" |").close();
    auto lock = lockSink();
    updateProgress(SolveProgress::Ev{eventId}, line.back() == '\n');
    write(line.view());
}
// NOLINTEND(readability-make-member-function-const,readability-convert-member-functions-to-static)
void TextOutput::doShutdown() {}
void TextOutput::doStart(std::string_view solver, std::string_view version, std::span<const std::string> input) {
    if (not solver.empty() && verbosity()) {
        printComment(style().warn, solver, " version "sv, version);
    }
    if (not input.empty() && verbosity()) {
        printComment(style().def, "Reading from "sv, Potassco::styled(prettify(input), style().info));
    }
}
void TextOutput::commit(Buffer& buf, bool force) {
    if (buf.size() >= 100 || force) {
        write(buf.view());
        buf.clear();
    }
}
void TextOutput::printSatModel(const SharedContext& ctx, const Model& m) {
    static constexpr auto prefix = "v "sv;
    Buffer                buffer;
    buffer.append(prefix);
    const auto ifs = ifs_ != '\n' ? std::string_view(&ifs_, 1) : "\nv ";
    m.visitWitness(
        ctx.output,
        [&, maxLine = 0u](OutputTable::Type, Literal lit, const char*) mutable {
            if (not maxLine) {
                maxLine = 70 + buffer.size();
            }
            else if (buffer.size() >= maxLine) {
                write(buffer.append("\n"sv).append(prefix).view());
                buffer.clear();
                maxLine = 70;
            }
            else {
                buffer.append(ifs);
            }
            fmtAtom_.formatTo(buffer, lit);
        },
        OutputTable::TypeSet{OutputTable::type_var});
    if (fmt_ != format_pb09) {
        auto termIfs = buffer.view() == prefix ? ""sv : ifs;
        buffer.append(termIfs).append("0"sv);
    }
    write(buffer.append('\n').view());
}
using ArgVec = amc::SmallVector<std::string_view, 4>;
static int popStep(std::string_view& args, Potassco::AtomArg arg) {
    auto r       = -1;
    auto matched = Potassco::popArg(args, arg, Potassco::AtomArgMode::unquote);
    return Potassco::matchNum(matched, nullptr, &r) ? r : -1;
}
void TextOutput::printAspModel(const SharedContext& ctx, const Model& m) {
    Buffer      buffer;
    std::string tmp[2];
    auto        lastPred  = predSep_ != ifs_ ? &tmp[0] : nullptr;
    auto        stepPred  = fmtStep_ && not m.consequences() ? &tmp[1] : nullptr;
    auto        lastStep  = -1;
    auto        splitAtom = lastPred || stepPred || fmtAssign_ || fmtCost_;
    auto        revisit   = OutputTable::TypeSet{};
    buffer.append(fmt_ == format_aspcomp ? "ANSWER\n"sv : ""sv);
    m.visitWitness(ctx.output, [&, first = true](OutputTable::Type symT, Literal lit, const char* name) mutable {
        auto [id, arity, args] = Potassco::atomSymbol(splitAtom && name ? name : "*");
        if (fmtAssign_.matches(id, arity) || fmtCost_.matches(id, arity)) {
            revisit.add(symT);
            return;
        }
        if (auto step = stepPred ? popStep(args, fmtStep_.stepArg()) : -1; step >= 0) {
            if (step > lastStep) {
                auto cap = fmtStep_.argName();
                buffer.append(lastStep >= 0 ? "\n"sv : ""sv);
                for (auto i = lastStep; i < step; ++i) {
                    buffer.open(style().trace, '\n')
                        .append(" "sv)
                        .append(cap)
                        .append(not cap.empty() ? " "sv : ""sv)
                        .append(i + 1)
                        .append(":"sv)
                        .close();
                }
                buffer.append("  "sv);
                lastStep = step;
                first    = true;
            }
            if (step == lastStep) {
                stepPred->assign(id).append(arity > 1, '(').append(args).append(arity > 1, ')');
                name = stepPred->c_str();
            }
            else {
                if (symT != OutputTable::type_theory) {
                    ctx.warn("output predicates are not ordered by solving step");
                }
                stepPred = nullptr;
            }
        }
        if (first) {
            stepPred  = name != nullptr ? stepPred : nullptr;
            lastPred  = lastPred ? &(*lastPred = id) : nullptr;
            splitAtom = lastPred || stepPred || fmtAssign_ || fmtCost_;
            first     = false;
        }
        else if (not lastPred || *lastPred == id) {
            buffer.append(ifs_);
        }
        else {
            buffer.append(predSep_).append(lastStep >= 0 && predSep_ == '\n' ? "  "sv : ""sv);
            *lastPred = id;
        }
        std::ignore = symT < OutputTable::type_term || buffer.open(style().trace).empty();
        name ? fmtAtom_.formatTo(buffer, name) : fmtAtom_.formatTo(buffer, lit);
        std::ignore = symT < OutputTable::type_term || buffer.close().empty();
        commit(buffer);
    });
    if (revisit.count() != 0) {
        Buffer costs;
        auto   getArgs = [](std::string_view args, uint32_t n, ArgVec& out) -> std::span<std::string_view> {
            out.clear();
            while (not args.empty() && n--) {
                out.emplace_back(Potassco::popArg(args, Potassco::AtomArg::first, Potassco::AtomArgMode::unquote));
            }
            return std::span{out};
        };
        if (fmtAssign_) {
            fmtAssign_.start(buffer.append('\n'), '\n', style().trace);
        }
        m.visitWitness(
            ctx.output,
            [&, sep = buffer.back(), argVec = ArgVec{}](OutputTable::Type, Literal, const char* name) mutable {
                if (auto [id, arity, args] = Potassco::atomSymbol(name); fmtAssign_.matches(id, arity)) {
                    if (buffer.empty() || buffer.back() != sep) {
                        buffer.push_back(ifs_);
                    }
                    commit(fmtAssign_.formatTo(buffer, getArgs(args, fmtAssign_.maxArg() + 1, argVec)));
                }
                else if (fmtCost_.matches(id, arity)) {
                    fmtCost_.formatTo(costs.append(not costs.empty(), ifs_),
                                      getArgs(args, fmtCost_.maxArg() + 1, argVec));
                }
            },
            revisit);
        if (not costs.empty()) {
            commit(fmtCost_.start(buffer.append('\n'), ' ', style().trace), true);
            write(costs.view());
        }
    }
    write(buffer.append('\n').view());
}
void TextOutput::printModelValues(const SharedContext& ctx, const Model& m) {
    switch (fmt_) {
        case format_asp     : [[fallthrough]];
        case format_aspcomp : return printAspModel(ctx, m);
        case format_sat09   : [[fallthrough]];
        case format_pb09    : [[fallthrough]];
        case format_maxsat09: return printSatModel(ctx, m);
    }
    POTASSCO_ASSERT_NOT_REACHED("invalid format");
}

void TextOutput::printModel(ElapsedTime elapsed, const SharedContext& ctx, const Model& m, ModelFlag flags) {
    POTASSCO_ASSERT(flags != model_quiet);
    auto        lock = lockSink();
    const char* type = not m.up ? "Answer" : "Update";
    updateProgress(SolveProgress::ev_clear, 3);
    if (verbosity()) {
        printKeyValue(style().info, Key{type, 1}, m.num, keyed("Time", elapsed));
    }
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
    if (auto lb = m.lower; m.lb && lb.active()) {
        updateProgress(SolveProgress::ev_clear, 1);
        auto ub  = m.costs.size() > lb.level ? m.costs[lb.level] : lb.bound;
        auto err = std::abs(static_cast<double>(ub - lb.bound) / static_cast<double>(lb.bound));
        printKeyValue(style().trace, Key{"Progression", 12}, bounds(lb, m.costs),
                      optkv(err > 0.0, "Error", Potassco::num<-6, 4>(err)), keyed("Time", elapsed));
    }
    if (m.num != 0 && m.up) {
        printMeta(ctx, m);
    }
}
void TextOutput::startStep(ElapsedTime, uint32_t step) {
    progress_ = {};
    if (callQ() != print_no && verbosity()) {
        printComment(style().trace, row_sep);
        if (verbosity() > 1u) {
            printKeyValue(style().info, "Call", step + 1);
        }
    }
}
void TextOutput::enterState(ElapsedTime, Event::Subsystem sys) {
    if (sys == Event::subsystem_load || sys == Event::subsystem_prepare) {
        const auto* activity = "Preprocessing";
        if (sys == Event::subsystem_load) {
            activity = mode() == mode_default ? "Reading" : "Grounding";
        }
        printEnter(activity);
        progress_.last = SolveProgress::ev_enter;
    }
    else if (sys == Event::subsystem_solve) {
        printComment(style().def, "Solving...");
        progress_ = {};
    }
}
void TextOutput::exitState(ElapsedTime, Event::Subsystem, ElapsedTime stateElapsed, ElapsedTime) {
    if (progress_.last != SolveProgress::ev_none) {
        if (progress_.last == SolveProgress::ev_enter) {
            printExit(stateElapsed);
        }
        else if (std::cmp_equal(progress_.last, Event::eventId<SatPreprocessor::Progress>())) {
            printKeyValue(sat_pre, stateElapsed, "unexpected state change - result unknown");
        }
        progress_ = {};
    }
}
void TextOutput::stopStep(ElapsedTime, ElapsedTime) {
    if (verbosity() >= 2u - (callQ() != print_no)) {
        printComment(style().trace, row_sep);
    }
}
void TextOutput::printProgress(ElapsedTime elapsed, const Event& ev, ElapsedTime stateElapsed, ElapsedTime split) {
    if (ev.system == Event::subsystem_prepare) {
        printPreproEvent(stateElapsed, ev, split);
    }
    else if (ev.system == Event::subsystem_solve) {
        printSolveEvent(elapsed, ev, stateElapsed);
    }
}
void TextOutput::printSummary(const ClaspFacade::Summary& run, bool final) {
    if (final && callQ() != print_no && verbosity()) {
        printComment(style().trace, acc_sep);
    }
    if (const auto* str = resultString(run); *str) {
        print(prefix_->result, optStyle(final), Term{'\n'}, str);
    }
    if (verbosity() || stats(run)) {
        br();
        if (run.result.interrupted()) {
            auto val     = run.result.signal != SIGALRM ? run.result.signal : 1;
            auto sigName = signal_names[std::min(run.result.signal, sig_max)];
            printKeyValue(style().err, interruptedString(run.result), val,
                          optkv(not sigName.empty(), "Signal", sigName),
                          optkv(run.killTime != 0.0, "Time", ElapsedTime{run.killTime}));
        }
        const auto& info = style().info;
        printKeyValue(info, "Models", models(run.numEnum, run.complete()));
        if (run.sat()) {
            if (run.consequences()) {
                printKeyValue(info, Key::indent(run.consequences()), run.complete() ? "yes" : "unknown");
            }
            if (run.hasCosts()) {
                printKeyValue(info, Key::indent("Optimum"), run.optimum() ? "yes" : "unknown");
            }
            if (run.optimize()) {
                if (run.optimal() > 1) {
                    printKeyValue(info, Key::indent("Optimal"), run.optimal());
                }
                printKeyValue(info, "Optimization", bounds(SumView{}, run.costs()));
            }
            if (run.consequences()) {
                printKeyValue(info, "Consequences",
                              models(run.model()->numConsequences(run.ctx()).first, run.complete()));
            }
        }
        if (run.hasLower() && not run.optimum()) {
            printKeyValue(info, "Bounds", bounds(run.lower(), run.costs()));
        }
        if (final) {
            printKeyValue(info, "Calls", run.step + 1);
        }
        printKeyValue(info, "Time", ElapsedTime{run.totalTime}, keyed("Solving", ElapsedTime{run.solveTime}),
                      keyed("1st Model", ElapsedTime{run.satTime}), keyed("Unsat", ElapsedTime{run.unsatTime}));
        printKeyValue(info, "CPU Time", ElapsedTime{run.cpuTime});
        if (run.ctx().concurrency() > 1) {
            printKeyValue(info, "Threads", run.ctx().concurrency(), keyed("Winner", run.ctx().winner()));
        }
    }
}
void TextOutput::enterStats(StatsKey t, const char* name, uint32_t n) {
    if (t == stats_stats) {
        accu_ = true;
        br();
    }
    else if (const auto& ts = style().trace; t == stats_threads || t == stats_tester) {
        accu_ = false;
        printComment(ts, "============ "sv, name, " Stats ==========="sv);
        br();
    }
    else if (t == stats_thread || t == stats_hcc) {
        printComment(ts, Key::array(name, n, ""));
        br();
    }
}
void TextOutput::printSolverStats(const SolverStats& stats) {
    using Potassco::num;
    if (not accu_ && stats.extra) {
        printKeyValue("CPU Time", ElapsedTime{stats.extra->cpuTime});
        printKeyValue("Models", stats.extra->models);
    }
    printKeyValue("Choices", stats.choices,
                  optkv(stats.extra && stats.extra->domChoices, "Domain", stats.extra->domChoices));
    printKeyValue("Conflicts", stats.conflicts, keyed("Analyzed", stats.backjumps()));
    if (auto k = "Restarts"; stats.restarts) {
        printKeyValue(k, stats.restarts, keyed("Average", num<0, 2>(stats.avgRestart())),
                      keyed("Last", stats.lastRestart), keyed("Blocked", stats.blRestarts));
    }
    else {
        printKeyValue(k, 0);
    }

    if (not stats.extra) {
        return;
    }
    const ExtendedStats& stx = *stats.extra;
    const JumpStats&     stj = stx.jumps;
    if (stx.hccTests) {
        printKeyValue("Stab. Tests", stx.hccTests, keyed("Full", stx.hccTests - stx.hccPartial),
                      keyed("Partial", stx.hccPartial));
    }
    if (stx.models) {
        printKeyValue("Model-Level", std::round(stx.avgModel() * 10.0) / 10.0);
    }
    printKeyValue("Problems", stx.gps, keyed("Average Length", num<0, 2>(stx.avgGp())), keyed("Splits", stx.splits));
    uint64_t sum = stx.lemmas();
    printKeyValue("Lemmas", sum, keyed("Deleted", stx.deleted));
    printKeyValue(Key::indent("Binary"), stx.binary, keyed("Ratio", pct(percent(stx.binary, sum))));
    printKeyValue(Key::indent("Ternary"), stx.ternary, keyed("Ratio", pct(percent(stx.ternary, sum))));
    const char* names[] = {"Conflict", "Loop", "Other"};
    for (auto i : irange(names)) {
        auto type = static_cast<ConstraintType>(i + 1);
        printKeyValue(Key::indent(names[i]), stx.lemmas(type), keyed("Average Length", num<6, 1>(stx.avgLen(type))),
                      keyed("Ratio", pct(percent(stx.lemmas(type), sum))));
    }
    if (stx.distributed || stx.integrated) {
        printKeyValue(Key::indent("Distributed"), stx.distributed, keyed("Ratio", pct(stx.distRatio() * 100.0)),
                      keyed("Average LBD", num<0, 2>(stx.avgDistLbd())));
        printKeyValue(Key::indent("Integrated"), stx.integrated, optkv(accu_, "Ratio", pct(stx.intRatio() * 100.0)),
                      keyed("Unit", stx.intImps), keyed("Average Jumps", num<0, 2>(stx.avgIntJump())));
    }
    printKeyValue("Backjumps", stj.jumps, Jumps{.avg = stj.avgJump(), .max = stj.maxJump, .sum = stj.jumpSum});
    printKeyValue(Key::indent("Executed"), stj.jumps - stj.bounded,
                  Jumps{stj.avgJumpEx(), stj.maxJumpEx, stj.jumped(), stj.jumpedRatio() * 100.0});
    printKeyValue(Key::indent("Bounded"), stj.bounded,
                  Jumps{stj.avgBound(), stj.maxBound, stj.boundSum, 100.0 - (stj.jumpedRatio() * 100.0)});
    br();
}
void TextOutput::printProblemStats(const ProblemStats& stats) {
    using Potassco::num;
    uint32_t sum = stats.numConstraints();
    printKeyValue("Variables", stats.vars.num, keyed("Eliminated", num<4>(stats.vars.eliminated)),
                  keyed("Frozen", num<4>(stats.vars.frozen)));
    printKeyValue("Constraints", sum, keyed("Binary", pct<6, 1>(percent(stats.constraints.binary, sum))),
                  keyed("Ternary", pct<6, 1>(percent(stats.constraints.ternary, sum))),
                  keyed("Other", pct<6, 1>(percent(stats.constraints.other, sum))));
    if (stats.acycEdges) {
        printKeyValue("Acyc-Edges", stats.acycEdges);
    }
    br();
}
void TextOutput::printLogicProgramStats(const Asp::LpStats& stats) {
    using namespace Asp;
    uint32_t rFinal = stats.rules[1].sum(), rOriginal = stats.rules[0].sum();
    printKeyValue("Rules", rFinal, optkv(rFinal != rOriginal, "Original", rOriginal));
    for (auto i : irange(RuleStats::numKeys())) {
        if (i == RuleStats::normal) {
            continue;
        }
        if (uint32_t r = stats.rules[0][i]) {
            printKeyValue(Key::indent(RuleStats::toStr(i)), stats.rules[1][i],
                          optkv(r != stats.rules[1][i], "Original", r));
        }
    }
    printKeyValue("Atoms", stats.atoms, optkv(stats.auxAtoms != 0, "Original", stats.atoms - stats.auxAtoms),
                  optkv(stats.auxAtoms != 0, "Auxiliary", stats.auxAtoms));
    if (stats.disjunctions[0]) {
        printKeyValue("Disjunctions", stats.disjunctions[1], keyed("Original", stats.disjunctions[0]));
    }
    uint32_t bFinal = stats.bodies[1].sum(), bOriginal = stats.bodies[0].sum();
    printKeyValue("Bodies", bFinal, optkv(bFinal != bOriginal, "Original", bOriginal));
    for (auto i : irange(1u, BodyStats::numKeys())) {
        if (uint32_t b = stats.bodies[0][i]) {
            printKeyValue(Key::indent(BodyStats::toStr(i)), stats.bodies[1][i],
                          optkv(b != stats.bodies[1][i], "Original", b));
        }
    }
    if (stats.eqs() > 0) {
        printKeyValue("Equivalences", stats.eqs(), keyed("Atom=Atom", stats.eqs(VarType::atom)),
                      keyed("Body=Body", stats.eqs(VarType::body)), keyed("Other", stats.eqs(VarType::hybrid)));
    }
    if (const char* tight = "Tight"; stats.sccs == 0) {
        printKeyValue(tight, "Yes");
    }
    else if (stats.sccs != PrgNode::scc_not_set) {
        printKeyValue(tight, "No", keyed("SCCs", stats.sccs), keyed("Non-Hcfs", stats.nonHcfs),
                      keyed("Nodes", stats.ufsNodes), keyed("Gammas", stats.gammas));
    }
    else {
        printKeyValue(tight, "N/A");
    }
}
void TextOutput::printUserStats(const StatisticObject& stats) { printChildren(stats); }
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
            auto k = not key.empty() ? Key{key, 0} : Key::array(prefix, i);
            k.ind  = static_cast<uint32_t>(std::min(level, 50) * 2);
            if (type == StatsType::value) {
                printKeyValue(k, child.value());
            }
            else {
                k.sep = {};
                printComment(style().def, k);
                printChildren(child, level + 1);
            }
        }
    }
}

} // namespace Clasp::Cli
