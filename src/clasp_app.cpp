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
#include <clasp/cli/clasp_app.h>

#include <clasp/clause.h>
#include <clasp/dependency_graph.h>
#include <clasp/parser.h>
#include <clasp/solver.h>

#include <potassco/aspif.h>
#include <potassco/error.h>
#include <potassco/format.h>
#include <potassco/reify.h>
#include <potassco/smodels.h>

#include <potassco/program_opts/errors.h>
#include <potassco/program_opts/string_convert.h>

POTASSCO_WARNING_IGNORE_MSVC(4996)

#if __has_include(<io.h>)
#include <io.h> // ::write
#endif

#if __has_include(<unistd.h>)
#include <unistd.h> // ::write
#endif

#include <climits>
#include <csignal>
#include <fstream>
#include <iostream>

namespace Clasp {
/////////////////////////////////////////////////////////////////////////////////////////
// Some helpers
/////////////////////////////////////////////////////////////////////////////////////////
static const std::string stdin_str  = "stdin";
static const std::string stdout_str = "stdout";
constexpr bool           isStdIn(std::string_view in) { return in == "-" || in == stdin_str; }
constexpr bool           isStdOut(std::string_view out) { return out == "-" || out == stdout_str; }
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspAppOptions
/////////////////////////////////////////////////////////////////////////////////////////
namespace Cli {
POTASSCO_SET_ENUM_ENTRIES(ClaspAppOptions::OutputFormat, {out_def, "text"sv}, {out_comp, "competition"sv},
                          {out_json, "json"sv}, {out_none, "no"sv});
POTASSCO_SET_ENUM_ENTRIES(ClaspAppOptions::PreFormat, {pre_aspif, "aspif"sv}, {pre_smodels, "smodels"sv},
                          {pre_reify, "reify"sv});
int exitCode(const ClaspFacade::Summary& run) {
    int ec = 0;
    if (run.sat()) {
        ec |= exit_sat;
    }
    if (run.complete()) {
        ec |= exit_exhaust;
    }
    if (run.result.interrupted()) {
        ec |= exit_interrupt;
    }
    return ec;
}
void ClaspAppOptions::initOptions(Potassco::ProgramOptions::OptionContext& root) {
    using namespace Potassco::ProgramOptions;
    OptionGroup basic("Basic Options");
    auto action = makeCustom([this](const Option& opt, std::string_view value) { return apply(opt.name(), value); });
    basic.addOptions()                                                                           //
        ("@1,print-portfolio", flag(printPort), "Print default portfolio and exit")              //
        ("-q,quiet", value(action).implicit("2,2,2").arg("<levels>"),                            //
         "Configure printing of models, costs, and calls\n"                                      //
         "      %A: <mod>[,<cost>][,<call>]\n"                                                   //
         "        <mod> : print {0=all|1=last|2=no} models\n"                                    //
         "        <cost>: print {0=all|1=last|2=no} optimize values [<mod>]\n"                   //
         "        <call>: print {0=all|1=last|2=no} call steps      [2]")                        //
        ("preprocess", value(action).implicit("aspif"),                                          //
         "Print simplified program and exit\n"                                                   //
         "      %A: <fmt {aspif|smodels|reify}>[,<opts>] (implicit: %I)\n"                       //
         "        aspif   : Print program in ASP intermediate format\n"                          //
         "        smodels : Print program in smodels format\n"                                   //
         "        reify   : Print program as reified facts with <opts>\n"                        //
         "          steps : Add step numbers\n"                                                  //
         "          sccs  : Compute and print SCCs\n")                                           //
        ("@1,outf", storeTo(outf).arg("<fmt>").defaultsTo("text", true),                         //
         "Use {text|competition|json|no} output [%D]")                                           //
        ("@1!,out-color", value(action).defaultsTo("auto", true),                                //
         "Colorize output if supported [%D]\n"                                                   //
         "      %A: {auto|<custom>}\n"                                                           //
         "        <custom>: colon-separated list of (ansi) color styles\n")                      //
        ("@2,out-atomf", value(action), "Set atom format string (<Pre>?%%0<Post>?)")             //
        ("@2,out-ifs", value(action), "Set internal field separator")                            //
        ("@1,out-hide-aux", flag(hideAux), "Hide auxiliary atoms in answers")                    //
        ("@1,lemma-in", storeTo(lemmaIn).arg("<file>"), "Read additional lemmas from %A")        //
        ("@1,lemma-out", storeTo(lemmaLog).arg("<file>"), "Log learnt lemmas to %A")             //
        ("@2,lemma-out-lbd", storeTo(lemma.lbdMax).arg("<n>"), "Only log lemmas with lbd <= %A") //
        ("@2,lemma-out-max", storeTo(lemma.logMax).arg("<n>"), "Stop logging after %A lemmas")   //
        ("@2,lemma-out-dom", value(action), "Log lemmas over <arg {input|output}> variables")    //
        ("@2,lemma-out-txt", flag(lemma.logText), "Log lemmas as ground integrity constraints")  //
        ("@2,hcc-out", storeTo(hccOut).arg("<file>"), "Write non-hcf programs to %A.#scc")       //
        ("@3-f+,file", storeTo(input), "Input files")                                            //
        ("@2,compute", storeTo(compute).arg("<lit>"), "Force given literal to true");            //
    root.add(std::move(basic));
}
bool ClaspAppOptions::apply(std::string_view name, std::string_view value) {
    using Potassco::extract;
    using Potassco::Parse::eqIgnoreCase;
    using namespace std::literals;
    namespace Parse = Potassco::Parse;
    if (name == "quiet"sv) {
        std::string_view in(value);
        uint32_t         q[3]    = {};
        auto             parsed  = 0u;
        auto             bracket = Parse::matchOpt(in, '[');
        while (Parse::ok(extract(in, q[parsed])) && ++parsed < std::size(q) && Parse::matchOpt(in, ',')) {}
        if (parsed && (not bracket || Parse::matchOpt(in, ']')) && in.empty()) {
            for (auto i : irange(parsed)) { quiet[i] = static_cast<uint8_t>(q[i]); }
            return true;
        }
    }
    else if (name == "lemma-out-dom"sv) {
        return (lemma.domOut = eqIgnoreCase(value, "output"sv)) == true || eqIgnoreCase(value, "input"sv);
    }
    else if (name == "preprocess"sv && Parse::ok(extract(value, pre))) {
        if (pre == pre_reify) {
            while (Parse::matchOpt(value, ',')) {
                if (auto key = "sccs"sv; eqIgnoreCase(value, key, key.size())) {
                    reify |= reify_scc;
                    value.remove_prefix(key.size());
                }
                else if (key = "steps"sv; eqIgnoreCase(value, key, key.size())) {
                    reify |= reify_step;
                    value.remove_prefix(key.size());
                }
                else {
                    break;
                }
            }
        }
        return value.empty();
    }
    else if (name == "out-ifs"sv && not value.empty() && value.size() == 1 + (value[0] == '\\')) {
        if (auto x = value.size() == 1 ? value[0] : [](char c) {
            switch (c) {
                case 't' : return '\t';
                case 'n' : return '\n';
                case 'v' : return '\v';
                case '\\': return '\\';
                default  : return static_cast<char>(0);
            }
        }(value[1]); x != 0) {
            ifs = x;
            return true;
        }
    }
    else if (name == "out-atomf"sv) {
        outAtom = TextOutput::CatAtom::fromString(value);
        return true;
    }
    else if (name == "out-color"sv) {
        color = value == "auto";
        if (color || Parse::ok(Potassco::stringTo(value, color))) {
            return true;
        }
        color     = true;
        colString = value;
        return true;
    }
    return false;
}
bool ClaspAppOptions::validateOptions(const Potassco::ProgramOptions::ParsedOptions&) {
    if (quiet[1] == static_cast<uint8_t>(UCHAR_MAX)) {
        quiet[1] = quiet[0];
    }
    return true;
}
auto ClaspAppOptions::createProgramWriter(std::ostream& os, Potassco::Atom_t falseAtom) const
    -> std::unique_ptr<Potassco::AbstractProgram> {
    switch (pre) {
        default         : [[fallthrough]];
        case pre_aspif  : return std::make_unique<Potassco::AspifOutput>(os);
        case pre_smodels: return std::make_unique<Potassco::SmodelsOutput>(os, true, falseAtom);
        case pre_reify:
            Potassco::Reifier::Options opts{};
            opts.reifyStep     = Potassco::test(reify, reify_step);
            opts.calculateSccs = Potassco::test(reify, reify_scc);
            return std::make_unique<Potassco::Reifier>(os, opts);
    }
}
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspAppBase
/////////////////////////////////////////////////////////////////////////////////////////
struct ClaspAppBase::LemmaReader {
    using Program = Potassco::AbstractProgram;
    LemmaReader(const std::string& fn, std::unique_ptr<Program> p) : input(*p), prg(std::move(p)) {
        if (not isStdIn(fn)) {
            file.open(fn.c_str());
        }
        std::istream& str = file.is_open() ? file : std::cin;
        POTASSCO_CHECK(input.accept(str), std::errc::operation_not_supported, "'lemma-in': invalid input file!");
    }
    void parse() { input.parse(); }

    Potassco::AspifInput     input;
    std::unique_ptr<Program> prg;
    std::ifstream            file;
};

ClaspAppBase::ClaspAppBase() {
    if (Potassco::enableAnsiColorSupport(stderr) == std::errc{}) {
        enableColoredMessages();
    }
}
ClaspAppBase::~ClaspAppBase() = default;
const int* ClaspAppBase::getSignals() const {
    static const int signals[] = {
        SIGINT,
        SIGTERM
#if !defined(_WIN32)
        ,
        SIGUSR1,
        SIGUSR2,
        SIGQUIT,
        SIGHUP,
        SIGXCPU,
        SIGXFSZ
#endif
        ,
        0,
    };
    return signals;
}
std::string_view ClaspAppBase::getPositional(std::string_view value) const {
    if (int num; Potassco::stringTo(value, num) == std::errc{}) {
        return "models";
    }
    return "file";
}
void ClaspAppBase::writeError(MessageType type, int signal, std::string_view message) const {
    Potassco::BasicCharBuffer buffer;
    buffer << Application::message(type, message);
    buffer.push_back('\n');

    auto err = buffer.view();
    if (not signal) {
        fwrite(err.data(), sizeof(char), err.size(), stderr);
        fflush(stderr);
    }
    else {
        for (auto fd = fileno(stderr); not err.empty();) {
            if (auto x = ::write(fd, err.data(), size32(err)); x >= 0) {
                err.remove_prefix(static_cast<std::size_t>(x));
            }
            else if (errno != EINTR) {
                break;
            }
        }
    }
}
void ClaspAppBase::initOptions(Potassco::ProgramOptions::OptionContext& root) {
    claspConfig_.addOptions(root);
    claspAppOpts_.initOptions(root);
}

void ClaspAppBase::validateOptions(const Potassco::ProgramOptions::OptionContext&,
                                   const Potassco::ProgramOptions::ParsedOptions& parsed) {
    if (claspAppOpts_.printPort) {
        printTemplate();
        stop(exit_unknown);
    }
    setExitCode(exit_no_run);
    try {
        POTASSCO_CHECK(claspAppOpts_.validateOptions(parsed), std::errc::invalid_argument,
                       "unexpected command-line error");
        ClaspAppOptions& app = claspAppOpts_;
        for (bool first = true; const auto& in : claspAppOpts_.input) {
            if (not first || not input_) {
                POTASSCO_CHECK(isStdIn(in) || std::ifstream(in).is_open(), std::errc::no_such_file_or_directory,
                               "'%s': could not open input file", in.c_str());
            }
            first = false;
        }
        auto pt = getProblemType();
        POTASSCO_CHECK(claspConfig_.finalize(parsed, pt, true), std::errc::invalid_argument, "command-line error");
        POTASSCO_CHECK(app.lemmaIn.empty() || isStdIn(app.lemmaIn) || std::ifstream(app.lemmaIn.c_str()).is_open(),
                       std::errc::no_such_file_or_directory, "'lemma-in': could not open '%s'", app.lemmaIn.c_str());
        POTASSCO_CHECK(app.lemmaLog.empty() || isStdOut(app.lemmaLog) ||
                           (not Clasp::contains(app.input, app.lemmaLog) && app.lemmaIn != app.lemmaLog),
                       std::errc::file_exists, "'lemma-out': cowardly refusing to overwrite input file");
        POTASSCO_CHECK(not app.pre || pt == ProblemType::asp, std::errc::operation_not_supported,
                       "Option '--preprocess' only supported for ASP");
    }
    catch (const Potassco::RuntimeError& error) {
        throw Potassco::ProgramOptions::Error(std::string(error.message()));
    }
    setExitCode(0);
}
void ClaspAppBase::setup() {
    auto pt  = getProblemType();
    clasp_   = std::make_unique<ClaspFacade>();
    fpuMode_ = Potassco::initFpuPrecision();
    if (fpuMode_ == UINT32_MAX) {
        writeError(message_warning, 0, "could not set fpu mode: results can be non-deterministic!");
    }
    if (claspConfig_.onlyPre = claspAppOpts_.pre != ClaspAppOptions::pre_no; not claspConfig_.onlyPre) {
        out_ = createOutput(pt, claspAppOpts_.outf);
        if (out_) {
            auto quiet = static_cast<uint8_t>(Output::print_no);
            if (auto q0 = claspAppOpts_.quiet[0]; q0 != ClaspAppOptions::q_def) {
                out_->setModelQuiet(static_cast<Output::PrintLevel>(std::min(quiet, q0)));
            }
            if (auto q1 = claspAppOpts_.quiet[1]; q1 != ClaspAppOptions::q_def) {
                out_->setOptQuiet(static_cast<Output::PrintLevel>(std::min(quiet, q1)));
            }
            if (auto q2 = claspAppOpts_.quiet[2]; q2 != ClaspAppOptions::q_def) {
                out_->setCallQuiet(static_cast<Output::PrintLevel>(std::min(quiet, q2)));
            }
            if (claspAppOpts_.color) {
                if (auto ec = out_->enableColor(true, claspAppOpts_.colString);
                    ec != std::errc{} && ec != std::errc::inappropriate_io_control_operation) {
                    writeError(message_warning, 0,
                               Potassco::BasicCharBuffer{}
                                   .append("could not enable color-mode: ")
                                   .append(std::strerror(static_cast<int>(ec)))
                                   .view());
                }
            }
            else {
                enableColoredMessages(false);
            }
        }
        if (claspAppOpts_.hideAux && clasp_.get()) {
            clasp_->ctx.output.setFilter('_');
        }
        auto verb = static_cast<Event::Verbosity>(std::min(getVerbose(), static_cast<uint32_t>(Event::verbosity_max)));
        if (out_.get() && out_->verbosity() < static_cast<uint32_t>(verb)) {
            verb = static_cast<Event::Verbosity>(out_->verbosity());
        }
        if (not claspAppOpts_.lemmaLog.empty()) {
            logger_ = std::make_unique<LemmaLogger>(claspAppOpts_.lemmaLog.c_str(), claspAppOpts_.lemma);
        }
        setVerbosity(Event::subsystem_facade, verb);
        setVerbosity(Event::subsystem_load, verb);
        setVerbosity(Event::subsystem_prepare, verb);
        setVerbosity(Event::subsystem_solve, verb);
    }
    clasp_->ctx.setEventHandler(this, logger_.get() == nullptr ? SharedContext::report_default
                                                               : SharedContext::report_conflict);
}

void ClaspAppBase::shutdown() {
    if (not clasp_.get()) {
        return;
    }
    if (logger_.get()) {
        logger_->close();
    }
    lemmaIn_           = nullptr;
    input_             = nullptr;
    const auto& result = clasp_->shutdown();
    if (out_.get()) {
        out_->shutdown(result);
    }
    setExitCode(getExitCode() | exitCode(result));
    if (auto mode = std::exchange(fpuMode_, 0u); mode != UINT32_MAX) {
        Potassco::restoreFpuPrecision(mode);
    }
}

void ClaspAppBase::run() {
    if (out_.get()) {
        auto in = not claspAppOpts_.input.empty() ? std::span(claspAppOpts_.input) : std::span(&stdin_str, 1);
        out_->start(getName(), getVersion(), in);
    }
    run(*clasp_);
}

bool ClaspAppBase::onSignal(int sig) {
    if (not clasp_.get() || not clasp_->interrupt(sig)) {
        writeError(message_info, sig, "INTERRUPTED by signal!");
        shutdown();
        stop(exit_interrupt);
    }
    else {
        // multiple threads are active - shutdown was initiated
        writeError(message_info, sig, "Sending shutdown signal...");
    }
    return false; // ignore all future signals
}

void ClaspAppBase::onEvent(const Event& ev) {
    if (const auto* log = event_cast<LogEvent>(ev); log && log->isWarning()) {
        writeError(message_warning, 0, log->msg);
    }
    else if (const auto* prepare = event_cast<ClaspFacade::Prepare>(ev)) {
        handlePrepareEvent(*prepare->facade);
    }
    else if (const auto* cfl = event_cast<NewConflictEvent>(ev)) {
        if (logger_.get()) {
            logger_->add(*cfl->solver, cfl->learnt, cfl->info);
        }
    }
    else if (out_.get()) {
        blockSignals();
        out_->event(ev);
        unblockSignals(true);
    }
}

bool ClaspAppBase::onModel(const Solver& s, const Model& m) {
    if (out_.get() && not out_->quiet()) {
        blockSignals();
        out_->model(s, m);
        unblockSignals(true);
    }
    return true;
}
bool ClaspAppBase::onUnsat(const Solver& s, const Model& m) {
    if (out_.get() && not out_->quiet()) {
        blockSignals();
        out_->unsat(s, m);
        unblockSignals(true);
    }
    return true;
}

void ClaspAppBase::printTemplate() {
    printf("# clasp %s configuration file\n"
           "# A configuration file contains a (possibly empty) list of configurations.\n"
           "# Each of which must have the following format:\n"
           "#   <name>[(<base>)]: <cmd>\n"
           "# where\n"
           "# <name> is an alphanumeric identifier optionally enclosed in brackets,\n"
           "# <base> is the name of one of clasp's default configs and optional, and\n"
           "# <cmd>  is a command-line string of clasp options in long-format, e.g.\n"
           "# ('--heuristic=vsids --restarts=L,100').\n"
           "#\n"
           "# SEE: clasp --help=3\n"
           "#\n"
           "# NOTE: The options '--configuration' and '--tester' must not occur in a\n"
           "#       configuration file. All other global options are ignored unless\n"
           "#       explicitly given in the very first configuration after the colon.\n"
           "#       In particular, global options from base configurations are ignored.\n"
           "#\n"
           "# NOTE: Options given on the command-line are added to all configurations in a\n"
           "#       configuration file. If an option is given both on the command-line and\n"
           "#       in a configuration file, the one from the command-line is preferred.\n"
           "#\n"
           "# NOTE: If, after adding command-line options, a configuration\n"
           "#       contains mutually exclusive options an error is raised.\n"
           "#\n"
           "# EXAMPLE: To create a new config based on clasp's inbuilt tweety configuration\n"
           "#          with global options but a different heuristic one could write:\n"
           "#\n"
           "#            'Config1(tweety): --eq=3 --trans-ext=dynamic --heuristic=domain'\n"
           "#\n"
           "#          'Config1' is the purely descriptive name of the configuration and could\n"
           "#          also be written as '[Config1]'. The following '(tweety)' indicates that\n"
           "#          our configuration should be based on clasp's tweety configuration. Finally,\n"
           "#          since global options from base configurations are ignored, we explicitly add\n"
           "#          tweety's global options '--eq=3 --trans-ext=dynamic' after the colon.\n"
           "#\n",
           CLASP_VERSION);
    for (auto it = ClaspCliConfig::getConfig(config_many); it.valid(); it.next()) {
        printf("%s: %s\n", it.name(), it.args());
    }
}

void ClaspAppBase::onVersion(const std::string& version) {
    puts(version.c_str());
    printLibClaspVersion();
    printLicense();
}
void ClaspAppBase::printLicense() { printf("License: The MIT License <https://opensource.org/licenses/MIT>\n"); }
void ClaspAppBase::printLibClaspVersion() {
    printf("libclasp version %s (libpotassco version %s)\n", CLASP_VERSION, LIB_POTASSCO_VERSION);
    printf("Configuration: WITH_THREADS=%d\n", CLASP_HAS_THREADS);
    puts(CLASP_LEGAL);
}

void ClaspAppBase::onHelp(const std::string& help, Potassco::ProgramOptions::DescriptionLevel level) {
    puts(help.c_str());
    if (level >= Potassco::ProgramOptions::desc_level_e1) {
        printf("[asp] %s\n", ClaspCliConfig::getDefaults(ProblemType::asp));
        printf("[cnf] %s\n", ClaspCliConfig::getDefaults(ProblemType::sat));
        printf("[opb] %s\n", ClaspCliConfig::getDefaults(ProblemType::pb));
    }
    if (level >= Potassco::ProgramOptions::desc_level_e2) {
        puts("\nDefault configurations:");
        printDefaultConfigs();
    }
    else {
        auto        name    = getName();
        auto        em      = hasColoredMessages() && claspAppOpts_.color ? col_em : Potassco::TextStyle();
        const char* ht      = "\nType";
        const char* what[2] = {"more options and defaults", "all options and configurations."};
        for (auto i = static_cast<int>(level); i != Potassco::ProgramOptions::desc_level_e2; ++i) {
            auto buf = Potassco::BasicCharBuffer{};
            buf.open(em).append(name).append(" --help=").append(i + 2).close();
            printf("%s '%s' for %s\n", ht, buf.c_str(), what[i]);
            ht = "and ";
        }
    }
}
void ClaspAppBase::flush() {
    fflush(stdout);
    fflush(stderr);
}

void ClaspAppBase::printConfig(ConfigKey k) {
    uint32_t   minW = 2, maxW = 80;
    ConfigIter it = ClaspCliConfig::getConfig(k);
    printf("%s:\n%*c", it.name(), minW - 1, ' ');
    const char* opts = it.args();
    for (std::size_t size = std::strlen(opts), n = maxW - minW; n < size;) {
        while (n && opts[n] != ' ') { --n; }
        if (not n) {
            break;
        }
        printf("%.*s\n%*c", static_cast<int>(n), opts, static_cast<int>(minW - 1), ' ');
        size -= n + 1;
        opts += n + 1;
        n     = (maxW - minW);
    }
    puts(opts);
}
void ClaspAppBase::printDefaultConfigs() {
    for (int i = config_default + 1; i != config_default_max_value; ++i) { printConfig(static_cast<ConfigKey>(i)); }
}
void ClaspAppBase::writeNonHcfs(const PrgDepGraph& graph) const {
    for (auto* component : graph.nonHcfs()) {
        WriteCnf cnf(claspAppOpts_.hccOut + '.' + std::to_string(component->id()));
        if (const SharedContext& ctx = component->ctx(); ctx.master()->clearAssumptions()) {
            cnf.writeHeader(ctx.numVars(), ctx.numConstraints());
            cnf.write(ctx.numVars(), ctx.shortImplications());
            for (auto* c : ctx.master()->constraints()) {
                if (ClauseHead* x = c->clause()) {
                    cnf.write(x->toLits());
                }
            }
            for (auto lit : ctx.master()->trailView()) { cnf.write(lit); }
        }
        else {
            cnf.writeHeader(0, 1);
            cnf.write(ClauseHead::View());
        }
        cnf.close();
    }
}
auto ClaspAppBase::input() const -> ClaspAppOptions::StringSeq { return claspAppOpts_.input; }
auto ClaspAppBase::detectProblemType() -> ProblemType { return ClaspFacade::detectProblemType(ensureInput()); }
auto ClaspAppBase::ensureInput() -> std::istream& {
    if (not input_) {
        if (claspAppOpts_.input.empty() || isStdIn(claspAppOpts_.input[0])) {
            input_ = InputPtr(&std::cin, +[](std::istream*) {});
        }
        else {
            auto file = std::make_unique<std::ifstream>(claspAppOpts_.input[0].c_str());
            POTASSCO_CHECK(file->is_open(), std::errc::no_such_file_or_directory, "Can not read from '%s'",
                           claspAppOpts_.input[0].c_str());
            input_ = InputPtr(
                file.release(),
                +[](std::istream* f) { std::default_delete<std::ifstream>{}(static_cast<std::ifstream*>(f)); });
        }
    }
    return *input_;
}

// Creates output object suitable for given input format
auto ClaspAppBase::createOutput(ProblemType f, ClaspAppOptions::OutputFormat outf) -> std::unique_ptr<Output> {
    switch (outf) {
        case ClaspAppOptions::out_none: return nullptr;
        case ClaspAppOptions::out_json: return createJsonOutput();
        default                       : return createTextOutput(f);
    }
}
auto ClaspAppBase::createTextOutput(ProblemType f) const -> std::unique_ptr<TextOutput> {
    auto textFormat = [&](ProblemType p) {
        switch (p) {
            case ProblemType::sat:
                return not claspConfig_.parse.isEnabled(ParserOptions::parse_maxsat) ? TextOutput::format_sat09
                                                                                     : TextOutput::format_maxsat09;
            case ProblemType::pb: return TextOutput::format_pb09;
            case ProblemType::asp:
                return claspAppOpts_.outf == ClaspAppOptions::out_comp ? TextOutput::format_aspcomp
                                                                       : TextOutput::format_asp;
            default: POTASSCO_ASSERT_NOT_REACHED("unknown problem type");
        }
    };
    auto opts = TextOutput::Options{
        .catAtom   = claspAppOpts_.outAtom,
        .format    = textFormat(f),
        .verbosity = getVerbose(),
        .ifs       = claspAppOpts_.ifs,
    };
    return std::make_unique<TextOutput>(stdout, opts);
}

auto ClaspAppBase::createJsonOutput() const -> std::unique_ptr<JsonOutput> {
    return std::make_unique<JsonOutput>(stdout, getVerbose());
}

void ClaspAppBase::handlePrepareEvent(ClaspFacade& clasp) {
    if (auto* asp = clasp.asp(); claspConfig_.onlyPre) {
        if (asp) {
            asp->endProgram();
            if (const char* err; not asp->supportsSmodels(&err) && claspAppOpts_.pre == ClaspAppOptions::pre_smodels) {
                fail(exit_error, "Option '--preprocess': unsupported input format!",
                     std::string(err).append(
                         " directive not supported!\nTry '--preprocess=aspif' to print in 'aspif' format"));
            }
            auto out = claspAppOpts_.createProgramWriter(std::cout, asp->falseAtom());
            asp->accept(*out, true);
        }
        else {
            fail(exit_error, "Option '--preprocess': unsupported input format!");
        }
    }
    else {
        if (asp && claspAppOpts_.compute) {
            auto lit = Potassco::neg(claspAppOpts_.compute);
            asp->addRule(Potassco::HeadType::disjunctive, {}, {&lit, 1});
        }
        if (auto* prg = clasp.program()) {
            if (not lemmaIn_ && not claspAppOpts_.lemmaIn.empty()) {
                std::unique_ptr<Potassco::AbstractProgram> prgTemp;
                if (asp) {
                    prgTemp = std::make_unique<Asp::LogicProgramAdapter>(*asp);
                }
                else {
                    prgTemp = std::make_unique<BasicProgramAdapter>(*prg);
                }
                lemmaIn_ = std::make_unique<LemmaReader>(claspAppOpts_.lemmaIn, std::move(prgTemp));
            }
            if (lemmaIn_) {
                lemmaIn_->parse();
            }
            if (logger_) {
                logger_->startStep(clasp.ctx, prg->endProgram() ? asp : nullptr, clasp.incremental());
            }
            if (not claspAppOpts_.hccOut.empty() && prg->endProgram() && clasp.ctx.sccGraph.get()) {
                writeNonHcfs(*clasp.ctx.sccGraph);
            }
        }
    }
}
void ClaspAppBase::run(ClaspFacade& clasp) {
    clasp.start(claspConfig_, ensureInput());
    if (not clasp.incremental()) {
        claspConfig_.releaseOptions();
    }
    while (clasp.read()) {
        if (clasp.prepare()) {
            clasp.solve();
        }
    }
}
bool ClaspAppBase::onUnhandledException(const std::exception_ptr&, std::string_view msg) noexcept {
    flush();
    setExitCode(msg.find(std::bad_alloc().what()) != std::string_view::npos ? exit_memory : exit_error);
    fprintf(stderr, "%" PRIsv "\n", PRI_SV(msg));
    return false;
}
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspApp
/////////////////////////////////////////////////////////////////////////////////////////
ClaspApp::ClaspApp() = default;
void ClaspApp::validateOptions(const Potassco::ProgramOptions::OptionContext& root,
                               const Potassco::ProgramOptions::ParsedOptions& parsed) {
    if (input().size() > 1) {
        throw Potassco::ProgramOptions::Error(std::string("'").append(input()[1]).append("': Too many input files"));
    }
    ClaspAppBase::validateOptions(root, parsed);
}
ProblemType ClaspApp::getProblemType() { return detectProblemType(); }

void ClaspApp::run(ClaspFacade& clasp) { ClaspAppBase::run(clasp); }

void ClaspApp::onHelp(const std::string& help, Potassco::ProgramOptions::DescriptionLevel level) {
    ClaspAppBase::onHelp(help, level);
    printf("\nclasp is part of Potassco: %s\n", "https://potassco.org/clasp");
    printf("Get help/report bugs via : %s\n", "https://potassco.org/support\n");
}
/////////////////////////////////////////////////////////////////////////////////////////
// LemmaLogger
/////////////////////////////////////////////////////////////////////////////////////////
LemmaLogger::LemmaLogger(const std::string& to, const Options& o)
    : str_(isStdOut(to) ? stdout : fopen(to.c_str(), "w"))
    , asp_(false)
    , options_(o)
    , step_(0) {
    POTASSCO_CHECK(str_, std::errc::no_such_file_or_directory, "Could not open lemma log file '%s'!", to.c_str());
}
LemmaLogger::~LemmaLogger() { close(); }
void LemmaLogger::startStep(const SharedContext& ctx, Asp::LogicProgram* asp, bool inc) {
    logged_.store(0);
    ++step_;
    if (not options_.logText) {
        if (step_ == 1) {
            fprintf(str_, "asp 1 0 0%s\n", inc ? " incremental" : "");
        }
        else {
            fprintf(str_, "0\n");
        }
    }
    asp_ = asp != nullptr;
    if (asp) {
        // create solver variable to potassco literal mapping
        for (auto a : irange(asp->startAtom(), asp->startAuxAtom())) {
            Literal sLit = asp->getLiteral(a);
            if (sLit.var() >= solver2Asp_.size()) {
                solver2Asp_.resize(sLit.var() + 1, 0);
            }
            Potassco::Lit_t& p = solver2Asp_[sLit.var()];
            if (not p || (not sLit.sign() && p < 0)) {
                p = not sLit.sign() ? Potassco::lit(a) : Potassco::neg(a);
            }
        }
    }
    solver2NameIdx_.clear();
    if (options_.logText) {
        unsigned idx = 0;
        for (const auto& pred : ctx.output.pred_range()) {
            auto v = pred.cond.var();
            if (ctx.varInfo(v).output()) {
                if (solver2NameIdx_.size() <= v) {
                    solver2NameIdx_.resize(v + 1, UINT32_MAX);
                }
                solver2NameIdx_[v] = idx;
            }
            ++idx;
        }
    }
}
void LemmaLogger::add(const Solver& s, LitView cc, const ConstraintInfo& info) {
    LitVec temp;
    auto   lbd = info.lbd();
    if (lbd > options_.lbdMax || logged_ >= options_.logMax) {
        return;
    }
    if (info.aux() || options_.domOut || not std::ranges::all_of(cc, [&s](Literal p) { return s.inputVar(p); })) {
        uint8_t vf = options_.domOut ? VarInfo::flag_input | VarInfo::flag_output : VarInfo::flag_input;
        if (not s.resolveToFlagged(cc, vf, temp, lbd) || lbd > options_.lbdMax) {
            return;
        }
        cc = temp;
    }
    Potassco::BasicCharBufferT<1024> buf;
    bool                             log;
    if (options_.logText) {
        log = formatText(cc, s.sharedContext()->output, lbd, buf);
    }
    else {
        log = formatAspif(cc, lbd, buf);
    }
    if (log) {
        buf.push_back('\n');
        fwrite(buf.data(), sizeof(char), buf.size(), str_);
        logged_.add(1);
    }
}
template <typename S>
bool LemmaLogger::formatAspif(LitView cc, uint32_t, S& out) const {
    using namespace std::literals;
    out.append("1 0 0 0 "sv).append(cc.size());
    for (auto lit : cc) {
        Literal         sLit = ~lit; // clause -> constraint
        Potassco::Lit_t a    = toInt(sLit);
        if (asp_) {
            a = sLit.var() < solver2Asp_.size() ? solver2Asp_[sLit.var()] : 0;
            if (not a) {
                return false;
            }
            if (sLit.sign() != (a < 0)) {
                a = -a;
            }
        }
        out.append(" "sv).append(a);
    }
    return true;
}
template <typename S>
bool LemmaLogger::formatText(LitView cc, const OutputTable& tab, uint32_t lbd, S& out) const {
    using namespace std::literals;
    out.append(":-"sv);
    const char* sep   = " ";
    auto        preds = tab.pred_range();
    for (auto lit : cc) {
        Literal  sLit = ~lit; // clause -> constraint
        uint32_t idx  = sLit.var() < solver2NameIdx_.size() ? solver2NameIdx_[sLit.var()] : UINT32_MAX;
        if (idx != UINT32_MAX) {
            const OutputTable::PredType& p = preds[idx];
            assert(sLit.var() == p.cond.var());
            out.append(sep).append(sLit.sign() != p.cond.sign() ? "not "sv : ""sv).append(p.name.view());
        }
        else {
            if (asp_) {
                Potassco::Lit_t a = sLit.var() < solver2Asp_.size() ? solver2Asp_[sLit.var()] : 0;
                if (not a) {
                    return false;
                }
                if (sLit.sign() != (a < 0)) {
                    a = -a;
                }
                sLit = Literal(Potassco::atom(a), a < 0);
            }
            out.append(sep).append(sLit.sign() ? "not "sv : ""sv).append("__atom("sv).append(sLit.var()).append(")"sv);
        }
        sep = ", ";
    }
    out.append(". %lbd = "sv).append(lbd);
    return true;
}
void LemmaLogger::close() {
    if (not str_) {
        return;
    }
    if (not options_.logText) {
        fprintf(str_, "0\n");
    }
    fflush(str_);
    if (str_ != stdout) {
        fclose(str_);
    }
    str_ = nullptr;
    solver2Asp_.clear();
}
/////////////////////////////////////////////////////////////////////////////////////////
// WriteCnf
/////////////////////////////////////////////////////////////////////////////////////////
WriteCnf::WriteCnf(const std::string& outFile) : str_(fopen(outFile.c_str(), "w")) {
    POTASSCO_CHECK(str_, std::errc::no_such_file_or_directory, "Could not open cnf file '%s'!", outFile.c_str());
}
WriteCnf::~WriteCnf() { close(); }
void WriteCnf::writeHeader(uint32_t numVars, uint32_t numCons) { fprintf(str_, "p cnf %u %u\n", numVars, numCons); }
void WriteCnf::write(const ClauseHead::View& lits) {
    for (auto lit : lits) { fprintf(str_, "%d ", toInt(lit)); }
    fprintf(str_, "%d\n", 0);
}
void WriteCnf::write(Var_t maxVar, const ShortImplicationsGraph& g) {
    auto op = [this](Literal p, Literal q, Literal r = lit_false) {
        return r == lit_false ? unary(p, q) : binary(p, q, r);
    };
    for (auto v : irange(1u, maxVar + 1)) {
        g.forEach(posLit(v), op);
        g.forEach(negLit(v), op);
    }
}
void WriteCnf::write(Literal u) { fprintf(str_, "%d 0\n", toInt(u)); }

bool WriteCnf::unary(Literal p, Literal x) const {
    return p.rep() >= x.rep() || fprintf(str_, "%d %d 0\n", toInt(~p), toInt(x)) > 0;
}
bool WriteCnf::binary(Literal p, Literal x, Literal y) const {
    return p.rep() >= x.rep() || p.rep() >= y.rep() || fprintf(str_, "%d %d %d 0\n", toInt(~p), toInt(x), toInt(y)) > 0;
}
void WriteCnf::close() {
    if (str_) {
        fflush(str_);
        fclose(str_);
        str_ = nullptr;
    }
}

} // namespace Cli
} // namespace Clasp
