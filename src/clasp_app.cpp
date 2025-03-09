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
#include <clasp/util/timer.h>

#include <potassco/aspif.h>
#include <potassco/error.h>
#include <potassco/program_opts/string_convert.h>

POTASSCO_WARNING_BEGIN_RELAXED
#include <amc/vector.hpp>
POTASSCO_WARNING_END_RELAXED

POTASSCO_WARNING_IGNORE_MSVC(4996)

#if __has_include(<io.h>)
#include <io.h>
#endif

#if __has_include(<unistd.h>)
#include <unistd.h>
#endif

#include <climits>
#include <csignal>
#include <fstream>
#include <iostream>

namespace Clasp {
/////////////////////////////////////////////////////////////////////////////////////////
// Some helpers
/////////////////////////////////////////////////////////////////////////////////////////
#define WRITE_STDERR(TYPE, MSG, ...)                                                                                   \
    do {                                                                                                               \
        char buffer[256];                                                                                              \
        auto len = formatMessage(buffer, Potassco::Application::TYPE, (MSG) POTASSCO_OPTARGS(__VA_ARGS__));            \
        fwrite(buffer, sizeof(char), len, stderr);                                                                     \
        fflush(stderr);                                                                                                \
    } while (0)
static double            g_shutdownTime;
static const std::string stdin_str  = "stdin";
static const std::string stdout_str = "stdout";
inline bool              isStdIn(const std::string& in) { return in == "-" || in == stdin_str; }
inline bool              isStdOut(const std::string& out) { return out == "-" || out == stdout_str; }
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspAppOptions
/////////////////////////////////////////////////////////////////////////////////////////
namespace Cli {
void ClaspAppOptions::initOptions(Potassco::ProgramOptions::OptionContext& root) {
    using namespace Potassco::ProgramOptions;
    OptionGroup basic("Basic Options");
    auto        applyOpt = [this](const std::string& name, const std::string& value) { return apply(name, value); };
    basic.addOptions()                                                                                        //
        ("print-portfolio,@1", flag(printPort), "Print default portfolio and exit")                           //
        ("quiet,q", parse(applyOpt)->implicit("2,2,2")->arg("<levels>"),                                      //
         "Configure printing of models, costs, and calls\n"                                                   //
         "      %A: <mod>[,<cost>][,<call>]\n"                                                                //
         "        <mod> : print {0=all|1=last|2=no} models\n"                                                 //
         "        <cost>: print {0=all|1=last|2=no} optimize values [<mod>]\n"                                //
         "        <call>: print {0=all|1=last|2=no} call steps      [2]")                                     //
        ("pre", parse(applyOpt)->arg("<fmt>")->implicit("aspif"),                                             //
         "Print simplified program and exit\n"                                                                //
         "      %A: Set output format to {aspif|smodels} (implicit: %I)")                                     //
        ("outf,@1", storeTo(outf)->arg("<n>"), "Use {0=default|1=competition|2=JSON|3=no} output")            //
        ("out-atomf,@2", storeTo(outAtom), "Set atom format string (<Pre>?%%0<Post>?)")                       //
        ("out-ifs,@2", parse(applyOpt),                                                                       //
         "Set internal field separator")("out-hide-aux,@1", flag(hideAux), "Hide auxiliary atoms in answers") //
        ("lemma-in,@1", storeTo(lemmaIn)->arg("<file>"),                                                      //
         "Read additional lemmas from %A")                                                                    //
        ("lemma-out,@1", storeTo(lemmaLog)->arg("<file>"), "Log learnt lemmas to %A")                         //
        ("lemma-out-lbd,@2", storeTo(lemma.lbdMax)->arg("<n>"), "Only log lemmas with lbd <= %A")             //
        ("lemma-out-max,@2", storeTo(lemma.logMax)->arg("<n>"), "Stop logging after %A lemmas")               //
        ("lemma-out-dom,@2", parse(applyOpt),                                                                 //
         "Log lemmas over <arg {input|output}> variables")                                                    //
        ("lemma-out-txt,@2", flag(lemma.logText), "Log lemmas as ground integrity constraints")               //
        ("hcc-out,@2", storeTo(hccOut)->arg("<file>"), "Write non-hcf programs to %A.#scc")                   //
        ("file,f,@3", storeTo(input)->composing(), "Input files")                                             //
        ("compute,@2", storeTo(compute)->arg("<lit>"), "Force given literal to true");                        //
    root.add(basic);
}
bool ClaspAppOptions::apply(const std::string& name, const std::string& value) {
    using Potassco::extract;
    using Potassco::Parse::eqIgnoreCase;
    if (name == "quiet") {
        namespace Parse = Potassco::Parse;
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
    else if (name == "lemma-out-dom") {
        return (lemma.domOut = eqIgnoreCase(value.c_str(), "output")) == true || eqIgnoreCase(value.c_str(), "input");
    }
    else if (name == "pre") {
        if (eqIgnoreCase(value.c_str(), "aspif")) {
            onlyPre = static_cast<int8_t>(AspParser::format_aspif);
            return true;
        }
        if (eqIgnoreCase(value.c_str(), "smodels")) {
            onlyPre = static_cast<int8_t>(AspParser::format_smodels);
            return true;
        }
    }
    else if (name == "out-ifs" && not value.empty() && value.size() == 1 + (value[0] == '\\')) {
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
    return false;
}
bool ClaspAppOptions::validateOptions(const Potassco::ProgramOptions::ParsedOptions&) {
    if (quiet[1] == static_cast<uint8_t>(UCHAR_MAX)) {
        quiet[1] = quiet[0];
    }
    return true;
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

ClaspAppBase::ClaspAppBase()  = default;
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
const char* ClaspAppBase::getPositional(const std::string& value) const {
    if (int num; Potassco::stringTo(value, num) == std::errc{}) {
        return "number";
    }
    return "file";
}

void ClaspAppBase::initOptions(Potassco::ProgramOptions::OptionContext& root) {
    claspConfig_.addOptions(root);
    claspAppOpts_.initOptions(root);
    root.find("verbose")->get()->value()->defaultsTo("1");
}

void ClaspAppBase::validateOptions(const Potassco::ProgramOptions::OptionContext&,
                                   const Potassco::ProgramOptions::ParsedOptions& parsed,
                                   const Potassco::ProgramOptions::ParsedValues&  values) {
    if (claspAppOpts_.printPort) {
        printTemplate();
        exit(exit_unknown);
    }
    setExitCode(exit_no_run);
    auto pt = getProblemType();
    POTASSCO_CHECK(claspAppOpts_.validateOptions(parsed) && claspConfig_.finalize(parsed, pt, true),
                   std::errc::invalid_argument, "command-line error!");
    ClaspAppOptions& app = claspAppOpts_;
    POTASSCO_CHECK(app.lemmaLog.empty() || isStdOut(app.lemmaLog) ||
                       (not Clasp::contains(app.input, app.lemmaLog) && app.lemmaIn != app.lemmaLog),
                   std::errc::file_exists, "'lemma-out': cowardly refusing to overwrite input file!");
    POTASSCO_CHECK(app.lemmaIn.empty() || isStdIn(app.lemmaIn) || std::ifstream(app.lemmaIn.c_str()).is_open(),
                   std::errc::no_such_file_or_directory, "'lemma-in': could not open file!");
    for (std::size_t i = 1; i < app.input.size(); ++i) {
        POTASSCO_CHECK(isStdIn(app.input[i]) || std::ifstream(app.input[i].c_str()).is_open(),
                       std::errc::no_such_file_or_directory, "'%s': could not open input file!", app.input[i].c_str());
    }
    POTASSCO_CHECK(not app.onlyPre || pt == ProblemType::asp, std::errc::operation_not_supported,
                   "Option '--pre' only supported for ASP!");
    setExitCode(0);
    storeCommandArgs(values);
}
void ClaspAppBase::setup() {
    auto pt  = getProblemType();
    clasp_   = std::make_unique<ClaspFacade>();
    fpuMode_ = Potassco::initFpuPrecision();
    if (fpuMode_ == UINT32_MAX) {
        WRITE_STDERR(message_warning, "could not set fpu mode: results can be non-deterministic!\n");
    }
    if (not claspAppOpts_.onlyPre) {
        out_.reset(createOutput(pt));
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
        clasp_->ctx.setEventHandler(this, logger_.get() == nullptr ? SharedContext::report_default
                                                                   : SharedContext::report_conflict);
    }
}

void ClaspAppBase::shutdown() {
    if (not clasp_.get()) {
        return;
    }
    if (logger_.get()) {
        logger_->close();
    }
    lemmaIn_                           = nullptr;
    const ClaspFacade::Summary& result = clasp_->shutdown();
    if (g_shutdownTime != 0.0) {
        g_shutdownTime += RealTime::getTime();
        WRITE_STDERR(message_info, "Shutdown completed in %.3f seconds\n", g_shutdownTime);
    }
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
        out_->run(getName(), getVersion(), in.data(), in.data() + in.size());
    }
    run(*clasp_);
}

static void writeSigMessage(std::string_view message) { // async signal safe
    for (auto fd = fileno(stderr); not message.empty();) {
        if (auto x = write(fd, message.data(), size32(message)); x >= 0) {
            message.remove_prefix(static_cast<std::size_t>(x));
        }
        else if (errno != EINTR) {
            break;
        }
    }
}

bool ClaspAppBase::onSignal(int sig) {
    char message[80];
    if (not clasp_.get() || not clasp_->interrupt(sig)) {
        auto len = formatMessage(message, message_info, "INTERRUPTED by signal!\n");
        writeSigMessage({message, len});
        setExitCode(exit_interrupt);
        shutdown();
        exit(getExitCode());
    }
    else {
        // multiple threads are active - shutdown was initiated
        g_shutdownTime = -RealTime::getTime();
        auto len       = formatMessage(message, message_info, "Sending shutdown signal...\n");
        writeSigMessage({message, len});
    }
    return false; // ignore all future signals
}

void ClaspAppBase::onEvent(const Event& ev) {
    if (const auto* log = event_cast<LogEvent>(ev); log && log->isWarning()) {
        WRITE_STDERR(message_warning, "%s\n", log->msg);
    }
    else if (const auto* cfl = event_cast<NewConflictEvent>(ev)) {
        if (logger_.get()) {
            logger_->add(*cfl->solver, cfl->learnt, cfl->info);
        }
    }
    else if (out_.get()) {
        blockSignals();
        out_->onEvent(ev);
        unblockSignals(true);
    }
}

bool ClaspAppBase::onModel(const Solver& s, const Model& m) {
    bool ret = true;
    if (out_.get() && not out_->quiet()) {
        blockSignals();
        ret = out_->onModel(s, m);
        unblockSignals(true);
    }
    return ret;
}
bool ClaspAppBase::onUnsat(const Solver& s, const Model& m) {
    bool ret = true;
    if (out_.get() && not out_->quiet()) {
        blockSignals();
        ret = out_->onUnsat(s, m);
        unblockSignals(true);
    }
    return ret;
}

int ClaspAppBase::exitCode(const RunSummary& run) {
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
    for (auto it = ClaspCliConfig::getConfig(Clasp::Cli::config_many); it.valid(); it.next()) {
        printf("%s: %s\n", it.name(), it.args());
    }
}

void ClaspAppBase::onVersion(const std::string& version) {
    printf("%s\n", version.c_str());
    printLibClaspVersion();
    printLicense();
}
void ClaspAppBase::printLicense() { printf("License: The MIT License <https://opensource.org/licenses/MIT>\n"); }
void ClaspAppBase::printLibClaspVersion() {
    printf("libclasp version %s (libpotassco version %s)\n", CLASP_VERSION, LIB_POTASSCO_VERSION);
    printf("Configuration: WITH_THREADS=%d\n", CLASP_HAS_THREADS);
    printf("%s\n", CLASP_LEGAL);
}

void ClaspAppBase::onHelp(const std::string& help, Potassco::ProgramOptions::DescriptionLevel level) {
    printf("%s\n", help.c_str());
    if (level >= Potassco::ProgramOptions::desc_level_e1) {
        printf("[asp] %s\n", ClaspCliConfig::getDefaults(ProblemType::asp));
        printf("[cnf] %s\n", ClaspCliConfig::getDefaults(ProblemType::sat));
        printf("[opb] %s\n", ClaspCliConfig::getDefaults(ProblemType::pb));
    }
    if (level >= Potassco::ProgramOptions::desc_level_e2) {
        printf("\nDefault configurations:\n");
        printDefaultConfigs();
    }
    else {
        const char* ht3 = "\nType ";
        if (level == Potassco::ProgramOptions::desc_level_default) {
            printf("\nType '%s --help=2' for more options and defaults\n", getName());
            ht3 = "and ";
        }
        printf("%s '%s --help=3' for all options and configurations.\n", ht3, getName());
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
    printf("%s\n", opts);
}
void ClaspAppBase::printDefaultConfigs() {
    for (int i = config_default + 1; i != config_default_max_value; ++i) { printConfig(static_cast<ConfigKey>(i)); }
}
void ClaspAppBase::writeNonHcfs(const PrgDepGraph& graph) const {
    for (auto* component : graph.nonHcfs()) {
        WriteCnf             cnf(claspAppOpts_.hccOut + '.' + std::to_string(component->id()));
        const SharedContext& ctx = component->ctx();
        cnf.writeHeader(ctx.numVars(), ctx.numConstraints());
        cnf.write(ctx.numVars(), ctx.shortImplications());
        Solver::DBRef db = ctx.master()->constraints();
        for (auto* c : db) {
            if (ClauseHead* x = c->clause()) {
                cnf.write(x);
            }
        }
        for (auto lit : ctx.master()->trailView()) { cnf.write(lit); }
        cnf.close();
    }
}
std::istream& ClaspAppBase::getStream(bool reopen) const {
    static std::ifstream file;
    static bool          isOpen = false;
    if (not isOpen || reopen) {
        file.close();
        isOpen = true;
        if (not claspAppOpts_.input.empty() && not isStdIn(claspAppOpts_.input[0])) {
            file.open(claspAppOpts_.input[0].c_str());
            POTASSCO_CHECK(file.is_open(), std::errc::no_such_file_or_directory, "Can not read from '%s'!",
                           claspAppOpts_.input[0].c_str());
        }
    }
    return file.is_open() ? file : std::cin;
}

// Creates output object suitable for given input format
Output* ClaspAppBase::createOutput(ProblemType f) {
    std::unique_ptr<Output> out;
    if (claspAppOpts_.outf == ClaspAppOptions::out_none) {
        return nullptr;
    }
    if (claspAppOpts_.outf != ClaspAppOptions::out_json || claspAppOpts_.onlyPre) {
        out.reset(createTextOutput({.format =
                                        [](ProblemType t, bool comp) {
                                            switch (t) {
                                                case ProblemType::sat: return TextOutput::format_sat09;
                                                case ProblemType::pb : return TextOutput::format_pb09;
                                                default:
                                                    return not comp ? TextOutput::format_asp
                                                                    : TextOutput::format_aspcomp;
                                            }
                                        }(f, claspAppOpts_.outf == ClaspAppOptions::out_comp),
                                    .verbosity = getVerbose(),
                                    .catAtom   = claspAppOpts_.outAtom.c_str(),
                                    .ifs       = claspAppOpts_.ifs}));

        if (auto* textOut = dynamic_cast<TextOutput*>(out.get());
            textOut && claspConfig_.parse.isEnabled(ParserOptions::parse_maxsat) && f == ProblemType::sat) {
            textOut->result[TextOutput::res_sat] = "UNKNOWN";
        }
    }
    else {
        out.reset(createJsonOutput(getVerbose()));
    }

    if (out) {
        auto quiet = static_cast<uint8_t>(Output::print_no);
        if (auto q0 = claspAppOpts_.quiet[0]; q0 != ClaspAppOptions::q_def) {
            out->setModelQuiet(static_cast<Output::PrintLevel>(std::min(quiet, q0)));
        }
        if (auto q1 = claspAppOpts_.quiet[1]; q1 != ClaspAppOptions::q_def) {
            out->setOptQuiet(static_cast<Output::PrintLevel>(std::min(quiet, q1)));
        }
        if (auto q2 = claspAppOpts_.quiet[2]; q2 != ClaspAppOptions::q_def) {
            out->setCallQuiet(static_cast<Output::PrintLevel>(std::min(quiet, q2)));
        }
    }
    if (claspAppOpts_.hideAux && clasp_.get()) {
        clasp_->ctx.output.setFilter('_');
    }
    return out.release();
}

Output* ClaspAppBase::createTextOutput(const TextOptions& options) {
    return new TextOutput(options.verbosity, options.format, options.catAtom, options.ifs);
}

Output* ClaspAppBase::createJsonOutput(unsigned verbosity) { return new JsonOutput(verbosity); }

void ClaspAppBase::storeCommandArgs(const Potassco::ProgramOptions::ParsedValues&) { /* We don't need the values */ }
void ClaspAppBase::handleStartOptions(ClaspFacade& clasp) {
    if (not clasp.incremental()) {
        claspConfig_.releaseOptions();
    }
    if (auto* p = clasp.asp(); p && claspAppOpts_.compute) {
        auto lit = Potassco::neg(claspAppOpts_.compute);
        p->addRule(Potassco::HeadType::disjunctive, {}, {&lit, 1});
    }
    if (not claspAppOpts_.lemmaIn.empty()) {
        std::unique_ptr<Potassco::AbstractProgram> prgTemp;
        if (auto* p = clasp.asp()) {
            prgTemp = std::make_unique<Asp::LogicProgramAdapter>(*p);
        }
        else {
            prgTemp = std::make_unique<BasicProgramAdapter>(*clasp.program());
        }
        lemmaIn_ = std::make_unique<LemmaReader>(claspAppOpts_.lemmaIn, std::move(prgTemp));
    }
}
bool ClaspAppBase::handlePostGroundOptions(ClaspFacade& clasp) {
    if (not claspAppOpts_.onlyPre) {
        if (lemmaIn_) {
            lemmaIn_->parse();
        }
        if (logger_.get() && clasp.program()) {
            logger_->startStep(clasp.ctx, clasp.program()->endProgram() ? clasp.asp() : nullptr, clasp.incremental());
        }
        return clasp.ok();
    }
    if (auto* asp = clasp.asp()) {
        asp->endProgram();
        auto        outf = static_cast<AspParser::Format>(claspAppOpts_.onlyPre);
        const char* err;
        if (outf == AspParser::format_smodels && not asp->supportsSmodels(&err)) {
            fail(exit_error, "Option '--pre': unsupported input format!",
                 std::string(err).append(" directive not supported!\nTry '--pre=aspif' to print in 'aspif' format"));
        }
        AspParser::write(*asp, std::cout, outf);
    }
    else {
        fail(exit_error, "Option '--pre': unsupported input format!");
    }
    return false;
}
bool ClaspAppBase::handlePreSolveOptions(ClaspFacade& clasp) {
    if (not claspAppOpts_.hccOut.empty() && clasp.ctx.sccGraph.get()) {
        writeNonHcfs(*clasp.ctx.sccGraph);
    }
    return true;
}
void ClaspAppBase::run(ClaspFacade& clasp) {
    clasp.start(claspConfig_, getStream());
    handleStartOptions(clasp);
    while (clasp.read()) {
        if (handlePostGroundOptions(clasp)) {
            clasp.prepare();
            if (handlePreSolveOptions(clasp)) {
                clasp.solve();
            }
        }
    }
}
bool ClaspAppBase::onUnhandledException(const char* msg) {
    setExitCode(std::strstr(msg, std::bad_alloc().what()) ? exit_memory : exit_error);
    fprintf(stderr, "%s\n", msg);
    return false;
}
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspApp
/////////////////////////////////////////////////////////////////////////////////////////
ClaspApp::ClaspApp() = default;

ProblemType ClaspApp::getProblemType() { return ClaspFacade::detectProblemType(getStream()); }

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
    struct B {
        B& append(const std::string_view& data) {
            str.insert(str.end(), data.begin(), data.end());
            return *this;
        }
        void push_back(char c) { str.push_back(c); }

        amc::SmallVector<char, 1024> str;
    } buf;
    bool log;
    if (options_.logText) {
        log = formatText(cc, s.sharedContext()->output, lbd, buf);
    }
    else {
        log = formatAspif(cc, lbd, buf);
    }
    if (log) {
        buf.str.push_back('\n');
        fwrite(buf.str.data(), sizeof(char), buf.str.size(), str_);
        logged_.add(1);
    }
}
template <typename S>
bool LemmaLogger::formatAspif(LitView cc, uint32_t, S& out) const {
    using namespace std::literals;
    out.append("1 0 0 0 "sv);
    Potassco::toChars(out, cc.size());
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
        out.push_back(' ');
        Potassco::toChars(out, a);
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
            out.append(sep).append(sLit.sign() ? "not "sv : ""sv).append("__atom("sv);
            Potassco::toChars(out, sLit.var());
            out.push_back(')');
        }
        sep = ", ";
    }
    out.append(".  %lbd = "sv);
    Potassco::toChars(out, lbd);
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
void WriteCnf::write(const ClauseHead* h) {
    lits_.clear();
    h->toLits(lits_);
    for (auto lit : lits_) { fprintf(str_, "%d ", toInt(lit)); }
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
