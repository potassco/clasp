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
#pragma once

#include <clasp/cli/clasp_options.h>
#include <clasp/cli/clasp_output.h>

#include <potassco/application.h>
#include <potassco/program_opts/typed_value.h>

#include <iosfwd>
#include <memory>
#include <string>
#include <vector>

namespace Clasp::Cli {
/////////////////////////////////////////////////////////////////////////////////////////
// clasp exit codes
/////////////////////////////////////////////////////////////////////////////////////////
enum ExitCode {
    exit_unknown   = 0,  //!< Satisfiability of problem not known; search not started.
    exit_interrupt = 1,  //!< Run was interrupted.
    exit_sat       = 10, //!< At least one model was found.
    exit_exhaust   = 20, //!< Search-space was completely examined.
    exit_memory    = 33, //!< Run was interrupted by out of memory exception.
    exit_error     = 65, //!< Run was interrupted by internal error.
    exit_no_run    = 128 //!< Search not started because of syntax or command line error.
};
[[nodiscard]] int exitCode(const ClaspFacade::Summary& run);
/////////////////////////////////////////////////////////////////////////////////////////
// clasp app helpers
/////////////////////////////////////////////////////////////////////////////////////////
class WriteCnf {
public:
    explicit WriteCnf(const std::string& outFile);
    ~WriteCnf();
    WriteCnf(WriteCnf&&) = delete;
    void writeHeader(uint32_t numVars, uint32_t numCons);
    void write(Var_t maxVar, const ShortImplicationsGraph& g);
    void write(const ClauseHead::View& lits);
    void write(Literal unit);
    void close();

private:
    [[nodiscard]] bool unary(Literal, Literal) const;
    [[nodiscard]] bool binary(Literal, Literal, Literal) const;

    FILE* str_;
};
class LemmaLogger {
public:
    struct Options {
        uint32_t logMax  = UINT32_MAX; // log at most logMax lemmas
        uint32_t lbdMax  = UINT32_MAX; // only log lemmas with lbd <= lbdMax
        bool     domOut  = false;      // only log lemmas that can be expressed over out variables
        bool     logText = false;      // log lemmas in ground lp format
    };
    LemmaLogger(const std::string& outFile, const Options& opts);
    ~LemmaLogger();
    LemmaLogger(LemmaLogger&&) = delete;
    void startStep(const SharedContext& ctx, Asp::LogicProgram* prg, bool inc);
    void add(const Solver& s, LitView cc, const ConstraintInfo& info);
    void close();

private:
    using Var2Idx = PodVector_t<uint32_t>;
    using Counter = mt::ThreadSafe<uint32_t>;
    template <typename S>
    bool formatAspif(LitView cc, uint32_t lbd, S& out) const;
    template <typename S>
    bool             formatText(LitView cc, const OutputTable& tab, uint32_t lbd, S& out) const;
    FILE*            str_;
    Potassco::LitVec solver2Asp_;
    Var2Idx          solver2NameIdx_;
    bool             asp_;
    Options          options_;
    int              step_;
    Counter          logged_;
};
/////////////////////////////////////////////////////////////////////////////////////////
// clasp specific application options
/////////////////////////////////////////////////////////////////////////////////////////
struct ClaspAppOptions {
    static constexpr uint8_t q_def = UINT8_MAX;
    enum OutputFormat { out_def = 0, out_comp = 1, out_json = 2, out_none = 3 };
    enum PreFormat : uint8_t { pre_no, pre_aspif, pre_smodels, pre_reify };
    enum ReifyFlag : uint8_t { reify_scc = 1u, reify_step = 2u };
    POTASSCO_ENABLE_BIT_OPS(ReifyFlag, friend);
    static constexpr bool isTextOutput(OutputFormat f) { return f == out_def || f == out_comp; }
    using LogOptions = LemmaLogger::Options;
    using StringSeq  = std::vector<std::string>;
    using CatAtom    = TextOutput::CatAtom;
    using CatAssign  = TextOutput::CatAssign;
    using CatCost    = TextOutput::CatCost;
    using StepArg    = TextOutput::TimeStep;
    bool         apply(std::string_view, std::string_view);
    void         initOptions(Potassco::ProgramOptions::OptionContext& root);
    bool         validateOptions(const Potassco::ProgramOptions::ParsedOptions& parsed);
    auto         createProgramWriter(std::ostream&,
                                     Potassco::Atom_t falseAtom) const -> std::unique_ptr<Potassco::AbstractProgram>;
    StringSeq    input;                            // list of input files - only first used!
    std::string  lemmaLog;                         // optional file name for writing learnt lemmas
    std::string  lemmaIn;                          // optional file name for reading learnt lemmas
    std::string  hccOut;                           // optional file name for writing scc programs
    CatAtom      outAtom;                          // optional format string for atoms
    CatAssign    outAssign;                        // optional format template for printing theory assignment
    CatCost      outCost;                          // optional format template for printing theory costs
    std::string  colString;                        // optional color style string
    OutputFormat outf    = out_def;                // output format
    int          compute = 0;                      // force literal `compute` to true
    LogOptions   lemma;                            // options for lemma logging
    uint8_t      quiet[3] = {q_def, q_def, q_def}; // configure printing of models, optimization values, and call steps
    PreFormat    pre{};                            // run preprocessor and exit
    ReifyFlag    reify     = {};                   // reification flags
    char         ifs       = ' ';                  // output field separator
    char         predSep   = 0;                    // output predicate separator
    StepArg      stepArg   = StepArg::step_none;   // output step argument
    bool         hideAux   = false;                // output aux atoms?
    bool         printPort = false;                // print portfolio and exit
    bool         color     = {true};               // colorize output?
};
/////////////////////////////////////////////////////////////////////////////////////////
// clasp application base
/////////////////////////////////////////////////////////////////////////////////////////
// Base class for applications using the clasp library.
class ClaspAppBase
    : public Potassco::Application
    , public EventHandler {
protected:
    using Potassco::Application::run;
    ClaspAppBase();
    ~ClaspAppBase() override;
    // -------------------------------------------------------------------------------------------
    // Functions to be implemented/used by subclasses
    virtual auto getProblemType() -> ProblemType                                             = 0;
    virtual void run(ClaspFacade& clasp)                                                     = 0;
    virtual auto createOutput(OutputSink sink, ProblemType f,
                              ClaspAppOptions::OutputFormat outf) -> std::unique_ptr<Output> = 0;

    virtual auto       createOutputSink(bool& color) -> OutputSink;
    [[nodiscard]] auto createOutput(OutputSink sink, ProblemType f, ClaspAppOptions::OutputFormat outf,
                                    Output::Mode mode) -> std::unique_ptr<Output>;
    [[nodiscard]] auto createTextOutput(OutputSink sink, ProblemType f,
                                        Output::Mode mode) const -> std::unique_ptr<TextOutput>;
    [[nodiscard]] auto createJsonOutput(OutputSink sink, Output::Mode mode) const -> std::unique_ptr<JsonOutput>;
    // Application functions
    [[nodiscard]] auto getSignals() const -> std::span<const int> override;
    [[nodiscard]] auto getHelpOption() const -> HelpOpt override {
        return {"Print {1=basic|2=more|3=full} help and exit", 3};
    }
    [[nodiscard]] auto getVerboseOption() const -> VerboseOpt override { return {"1"}; }
    [[nodiscard]] auto getPositional(std::string_view value) const -> std::string_view override;

    void initOptions(Potassco::ProgramOptions::OptionContext& root) override;
    void validateOptions(const Potassco::ProgramOptions::OptionContext& root,
                         const Potassco::ProgramOptions::ParsedOptions& parsed) override;
    void setup() override;
    void run() override;
    void shutdown() override;
    bool onSignal(int) override;
    void flush() override;
    void onHelp(const std::string& help, Potassco::ProgramOptions::DescriptionLevel level) override;
    void onVersion(const std::string& version) override;
    bool onUnhandledException(const std::exception_ptr&, std::string_view) noexcept override;
    // -------------------------------------------------------------------------------------------
    // Event handler
    void onEvent(const Event& ev) override;
    bool onModel(const Solver& s, const Model& m) override;
    bool onUnsat(const Solver& s, const Model& m) override;
    // -------------------------------------------------------------------------------------------
    // Config
    [[nodiscard]] auto detectProblemType() -> ProblemType;
    [[nodiscard]] auto input() const -> ClaspAppOptions::StringSeq;
    [[nodiscard]] auto config() const -> const ClaspCliConfig& { return claspConfig_; }
    auto               config() -> ClaspCliConfig& { return claspConfig_; }
    // -------------------------------------------------------------------------------------------
    // Status information & output
    static void printTemplate();
    static void printDefaultConfigs();
    static void printConfig(ConfigKey k);
    static void printLibClaspVersion();
    static void printLicense();
    // -------------------------------------------------------------------------------------------
    void writeNonHcfs(const PrgDepGraph& graph) const;
    void handlePrepareEvent(ClaspFacade& clasp);
    void writeError(MessageType type, int signal, std::string_view message) const;

private:
    struct LemmaReader;
    using OutPtr   = std::unique_ptr<Output>;
    using ClaspPtr = std::unique_ptr<ClaspFacade>;
    using LogPtr   = std::unique_ptr<LemmaLogger>;
    using LemmaPtr = std::unique_ptr<LemmaReader>;
    using InputPtr = std::unique_ptr<std::istream, void (*)(std::istream*)>;
    auto ensureInput() -> std::istream&;

    ClaspCliConfig  claspConfig_;
    ClaspAppOptions claspAppOpts_;
    ClaspPtr        clasp_;
    OutPtr          out_;
    LogPtr          logger_;
    LemmaPtr        lemmaIn_;
    InputPtr        input_{nullptr, nullptr};
    unsigned        fpuMode_{};
};
/////////////////////////////////////////////////////////////////////////////////////////
// clasp application
/////////////////////////////////////////////////////////////////////////////////////////
// Standalone clasp application.
class ClaspApp : public ClaspAppBase {
public:
    ClaspApp();
    [[nodiscard]] std::string_view getName() const override { return "clasp"; }
    [[nodiscard]] std::string_view getVersion() const override { return CLASP_VERSION; }
    [[nodiscard]] std::string_view getUsage() const override {
        return "[number] [options] [file]\n"
               "Compute at most <number> models (0=all) of the instance given in <file>";
    }

protected:
    using ClaspAppBase::run;
    void        validateOptions(const Potassco::ProgramOptions::OptionContext& root,
                                const Potassco::ProgramOptions::ParsedOptions& parsed) override;
    ProblemType getProblemType() override;
    void        run(ClaspFacade& clasp) override;
    auto        createOutput(OutputSink sink, ProblemType f,
                             ClaspAppOptions::OutputFormat outf) -> std::unique_ptr<Output> override;
    void        onHelp(const std::string& help, Potassco::ProgramOptions::DescriptionLevel level) override;
};
} // namespace Clasp::Cli
