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
    exit_unknown   = 0,  /*!< Satisfiability of problem not known; search not started.   */
    exit_interrupt = 1,  /*!< Run was interrupted.                                       */
    exit_sat       = 10, /*!< At least one model was found.                              */
    exit_exhaust   = 20, /*!< Search-space was completely examined.                      */
    exit_memory    = 33, /*!< Run was interrupted by out of memory exception.            */
    exit_error     = 65, /*!< Run was interrupted by internal error.                     */
    exit_no_run    = 128 /*!< Search not started because of syntax or command line error.*/
};
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
    void write(const ClauseHead* h);
    void write(Literal unit);
    void close();

private:
    [[nodiscard]] bool unary(Literal, Literal) const;
    [[nodiscard]] bool binary(Literal, Literal, Literal) const;

    FILE*  str_;
    LitVec lits_;
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
    enum OutputFormat { out_def = 0, out_comp = 1, out_json = 2, out_none = 3 };
    static constexpr uint8_t q_def = UINT8_MAX;
    using LogOptions               = LemmaLogger::Options;
    using StringSeq                = std::vector<std::string>;
    bool        apply(const std::string&, const std::string&);
    void        initOptions(Potassco::ProgramOptions::OptionContext& root);
    bool        validateOptions(const Potassco::ProgramOptions::ParsedOptions& parsed);
    StringSeq   input;                             // list of input files - only first used!
    std::string lemmaLog;                          // optional file name for writing learnt lemmas
    std::string lemmaIn;                           // optional file name for reading learnt lemmas
    std::string hccOut;                            // optional file name for writing scc programs
    std::string outAtom;                           // optional format string for atoms
    uint32_t    outf    = out_def;                 // output format
    int         compute = 0;                       // force literal compute to true
    LogOptions  lemma;                             // options for lemma logging
    uint8_t     quiet[3]  = {q_def, q_def, q_def}; // configure printing of models, optimization values, and call steps
    int8_t      onlyPre   = 0;                     // run preprocessor and exit
    char        ifs       = ' ';                   // output field separator
    bool        hideAux   = false;                 // output aux atoms?
    bool        printPort = false;                 // print portfolio and exit
};
/////////////////////////////////////////////////////////////////////////////////////////
// clasp application base
/////////////////////////////////////////////////////////////////////////////////////////
// Base class for applications using the clasp library.
class ClaspAppBase
    : public Potassco::Application
    , public EventHandler {
public:
    using RunSummary = ClaspFacade::Summary;

protected:
    struct TextOptions {
        TextOutput::Format format;
        unsigned           verbosity;
        const char*        catAtom;
        char               ifs;
    };
    using Potassco::Application::run;
    ClaspAppBase();
    ~ClaspAppBase() override;
    // -------------------------------------------------------------------------------------------
    // Functions to be implemented by subclasses
    virtual ProblemType getProblemType()        = 0;
    virtual void        run(ClaspFacade& clasp) = 0;
    virtual void        storeCommandArgs(const Potassco::ProgramOptions::ParsedValues& values);
    virtual Output*     createOutput(ProblemType f);
    virtual Output*     createTextOutput(const TextOptions& options);
    virtual Output*     createJsonOutput(unsigned verbosity);
    // -------------------------------------------------------------------------------------------
    // Helper functions that subclasses might call during run
    void handleStartOptions(ClaspFacade& clasp);
    bool handlePostGroundOptions(ClaspFacade& clasp);
    bool handlePreSolveOptions(ClaspFacade& clasp);
    // -------------------------------------------------------------------------------------------
    // Application functions
    [[nodiscard]] const int* getSignals() const override;
    [[nodiscard]] HelpOpt getHelpOption() const override { return {"Print {1=basic|2=more|3=full} help and exit", 3}; }
    [[nodiscard]] const char* getPositional(const std::string& value) const override;

    void initOptions(Potassco::ProgramOptions::OptionContext& root) override;
    void validateOptions(const Potassco::ProgramOptions::OptionContext& root,
                         const Potassco::ProgramOptions::ParsedOptions& parsed,
                         const Potassco::ProgramOptions::ParsedValues&  values) override;
    void setup() override;
    void run() override;
    void shutdown() override;
    bool onSignal(int) override;
    void flush() override;
    void onHelp(const std::string& help, Potassco::ProgramOptions::DescriptionLevel level) override;
    void onVersion(const std::string& version) override;
    bool onUnhandledException(const char*) override;
    // -------------------------------------------------------------------------------------------
    // Event handler
    void onEvent(const Event& ev) override;
    bool onModel(const Solver& s, const Model& m) override;
    bool onUnsat(const Solver& s, const Model& m) override;
    // -------------------------------------------------------------------------------------------
    // Status information & output
    [[nodiscard]] static int    exitCode(const RunSummary& run);
    static void                 printTemplate();
    static void                 printDefaultConfigs();
    static void                 printConfig(ConfigKey k);
    static void                 printLibClaspVersion();
    static void                 printLicense();
    [[nodiscard]] std::istream& getStream(bool reopen = false) const;
    // -------------------------------------------------------------------------------------------
    // Functions called in handlePreSolveOptions()
    void writeNonHcfs(const PrgDepGraph& graph) const;
    struct LemmaReader;
    using OutPtr   = std::unique_ptr<Output>;
    using ClaspPtr = std::unique_ptr<ClaspFacade>;
    using LogPtr   = std::unique_ptr<LemmaLogger>;
    using LemmaPtr = std::unique_ptr<LemmaReader>;
    ClaspCliConfig  claspConfig_;
    ClaspAppOptions claspAppOpts_;
    ClaspPtr        clasp_;
    OutPtr          out_;
    LogPtr          logger_;
    LemmaPtr        lemmaIn_;
    unsigned        fpuMode_{};
};
/////////////////////////////////////////////////////////////////////////////////////////
// clasp application
/////////////////////////////////////////////////////////////////////////////////////////
// Standalone clasp application.
class ClaspApp : public ClaspAppBase {
public:
    ClaspApp();
    [[nodiscard]] const char* getName() const override { return "clasp"; }
    [[nodiscard]] const char* getVersion() const override { return CLASP_VERSION; }
    [[nodiscard]] const char* getUsage() const override {
        return "[number] [options] [file]\n"
               "Compute at most <number> models (0=all) of the instance given in <file>";
    }

protected:
    using ClaspAppBase::run;
    ProblemType getProblemType() override;
    void        run(ClaspFacade& clasp) override;
    void        onHelp(const std::string& help, Potassco::ProgramOptions::DescriptionLevel level) override;
};
} // namespace Clasp::Cli
