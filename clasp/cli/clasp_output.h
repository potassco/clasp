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
#pragma once

#include <clasp/clasp_facade.h>
#include <clasp/dependency_graph.h>
#include <clasp/solver_types.h>

#include <string>

namespace Clasp::Cli {

/*!
 * \addtogroup cli
 * @{ */
/*!
 * \brief Interface for printing status and input format dependent information,
 * like models, optimization values, and summaries.
 */
class Output {
public:
    //! Supported levels for printing models, optimize values, and individual calls.
    enum PrintLevel {
        print_all  = 0, //!< Print all models, optimize values, or calls.
        print_best = 1, //!< Only print last model, optimize value, or call.
        print_no   = 2, //!< Do not print any models, optimize values, or calls.
    };
    explicit Output(uint32_t verb = 1);
    virtual ~Output();
    Output(Output&&) = delete;
    //! Active verbosity level.
    [[nodiscard]] uint32_t verbosity() const { return verbose_; }
    //! Do not output any models?
    [[nodiscard]] bool quiet() const { return modelQ() == 2 && optQ() == 2; }
    //! Print level for models.
    [[nodiscard]] int modelQ() const { return quiet_[0]; }
    //! Print level for optimization values.
    [[nodiscard]] int optQ() const { return quiet_[1]; }
    //! Print level for individual (solve) calls.
    [[nodiscard]] int callQ() const { return quiet_[2]; }

    void setVerbosity(uint32_t verb);
    void setModelQuiet(PrintLevel model);
    void setOptQuiet(PrintLevel opt);
    void setCallQuiet(PrintLevel call);

    //! Shall be called once on startup.
    void start(std::string_view solver, std::string_view version, std::span<const std::string> input);
    //! Shall be called once on shutdown with the final solve summary.
    void shutdown(const ClaspFacade::Summary& summary);
    //! Shall be called whenever a solver found a model.
    void model(const Solver& s, const Model& m);
    //! Shall be called whenever a solver found an unsatisfiable path.
    void unsat(const Solver& s, const Model& m);
    //! Shall be called for each event.
    void event(const Event& event);

protected:
    class WitnessGenerator {
    public:
        struct promise_type;
        using value_type = std::pair<Literal, const char*>;
        explicit WitnessGenerator(const SharedContext& ctx, const Model& model);
        WitnessGenerator(WitnessGenerator&&) = delete;
        explicit   operator bool();
        value_type operator()() const;

    private:
        bool accept(bool showNeg, Literal p, bool onlyD) const;

        const SharedContext& ctx_;
        const Model&         m_;
        value_type           curr_;
        alignas(void*) char buffer_[sizeof(void*) * 2]{};
        int  state_{0};
        bool def_{true};
    };
    enum ModelFlag : uint32_t { model_quiet = 0u, model_values = 1u, model_meta = 2u, model_both = 3u };
    POTASSCO_ENABLE_BIT_OPS(ModelFlag, friend);
    enum StatsKey { stats_stats, stats_threads, stats_tester, stats_hccs, stats_thread, stats_hcc };
    static auto makeWitness(const SharedContext& ctx, const Model& model) -> WitnessGenerator;
    void        resetStateTime();

private:
    //! Called once on startup.
    virtual void doStart(std::string_view solver, std::string_view version, std::span<const std::string> input) = 0;
    //! Called when a new solving step is started.
    virtual void startStep(double elapsed, uint32_t step) = 0;
    //! Called after the active solving step has been solved.
    virtual void stopStep(double elapsed, double stepElapsed) = 0;
    //! Called on entering a new subsystem state.
    /*!
     * \note The function is only called for states whose verbosity level is `<= verbosity()`.
     */
    virtual void enterState(double elapsed, Event::Subsystem sys, const char* activity);
    //! Called on exiting the previously entered subsystem state.
    virtual void exitState(double elapsed, Event::Subsystem sys, double stateElapsed);
    //! Called on model that should be printed.
    virtual void printModel(double elapsed, const SharedContext& ctx, const Model& m, ModelFlag flags) = 0;
    //! Called on unsat.
    virtual void printUnsat(double elapsed, const SharedContext& ctx, const Model& m) = 0;
    //! Called for relevant progress events from the last started subsystem state.
    virtual void printProgress(double elapsed, const Event&, double stateElapsed);
    //! Called after a solving step has stopped with the summary of the step or an accumulation.
    virtual void printSummary(const ClaspFacade::Summary& summary, bool final) = 0;
    //! Called from printStats() when entering a new stats type.
    virtual void enterStats(StatsKey t, const char* name, uint32_t n);
    //! Called from printStats().
    virtual void printLogicProgramStats(const Asp::LpStats& stats);
    //! Called from printStats().
    virtual void printProblemStats(const ProblemStats& stats);
    //! Called from printStats().
    virtual void printSolverStats(const SolverStats& stats);
    //! Called from printStats().
    virtual void printUserStats(const StatisticObject& object);
    //! Called from printStats() when leaving the current stats type.
    virtual void exitStats(StatsKey t);
    //! Called once on shutdown.
    virtual void doShutdown() = 0;

    [[nodiscard]] double elapsedTime() const;
    [[nodiscard]] auto   flags(const Model& m, PrintLevel level) const -> ModelFlag;
    void                 transition(double elapsed, Event::Subsystem to, const char* message);
    void                 summary(const ClaspFacade::Summary& summary, bool final);
    void                 visitStats(const ClaspFacade::Summary& summary);

    using SumPtr = const ClaspFacade::Summary*;
    using State  = Event::Subsystem;
    double   start_{-1.0};      // time on start
    double   model_{-1.0};      // elapsed time on last model
    double   step_{-1.0};       // time on step enter
    double   enter_{-1.0};      // time on state enter
    SumPtr   summary_{nullptr}; // summary of last step
    State    state_{};          // current state
    uint32_t verbose_{0};       // verbosity level
    uint8_t  quiet_[3]{};       // quiet levels for models, optimize, calls
    bool     last_ = false;     // print last model on summary
};

//! Prints models and solving statistics in Json-format to stdout.
class JsonOutput final : public Output {
public:
    explicit JsonOutput(uint32_t verb);
    ~JsonOutput() override;

private:
    enum ObjType { type_object, type_array };
    // Output interface
    void doStart(std::string_view solver, std::string_view version, std::span<const std::string> input) override;
    void startStep(double elapsed, uint32_t step) override;
    void stopStep(double elapsed, double stepElapsed) override;
    void printModel(double elapsed, const SharedContext& ctx, const Model& m, ModelFlag flags) override;
    void printUnsat(double elapsed, const SharedContext& out, const Model& m) override;
    void printSummary(const ClaspFacade::Summary& summary, bool final) override;
    void enterStats(StatsKey t, const char* name, uint32_t n) override;
    void printLogicProgramStats(const Asp::LpStats& lp) override;
    void printProblemStats(const ProblemStats& p) override;
    void printSolverStats(const SolverStats& stats) override;
    void printUserStats(const StatisticObject& object) override;
    void exitStats(StatsKey t) override;
    void doShutdown() override;

    // Implementation
    [[nodiscard]] uint32_t indent() const { return size32(objStack_) * 2; }

    void pushObject(const char* k = nullptr, ObjType t = type_object, bool startIndent = false);
    char popObject();
    void startWitness(double time);
    void endWitness();
    void popUntil(uint32_t sz);
    void printKeyValue(const char* k, const char* v);
    void printKeyValue(const char* k, uint64_t v);
    void printKeyValue(const char* k, uint32_t v);
    void printKeyValue(const char* k, double d, bool fmtG = false);
    void printString(const char* s, const char* sep);
    void printSum(const char* name, SumView sum, const Wsum_t* last = nullptr);
    void printCosts(SumView costs, const char* name = "Costs");
    void printCons(const SharedContext& ctx, const Model& m);
    void printTime(const char* name, double t);
    void printCoreStats(const CoreStats&);
    void printExtStats(const ExtendedStats&, bool generator);
    void printJumpStats(const JumpStats&);

    const char* open_;
    std::string objStack_;
};

//! Default clasp format printer.
/*!
 * Prints all output to stdout in given format:
 * - format_asp prints in clasp's default asp format
 * - format_aspcomp prints in ASP competition format
 * - format_sat09 prints in SAT-competition format
 * - format_pb09 in PB-competition format
 * .
 * \see https://www.mat.unical.it/aspcomp2013/
 * \see https://web.archive.org/web/20170809225851/https://www.satcompetition.org/2009/format-solvers2009.html
 * \see https://www.cril.univ-artois.fr/PB09/solver_req.html
 *
 */
class TextOutput : public Output {
public:
    using ModelPrinter = std::function<void(TextOutput&, const SharedContext&, const Model&)>;

    //! Supported text formats.
    enum Format { format_asp, format_aspcomp, format_sat09, format_pb09 };
    TextOutput(uint32_t verbosity, Format fmt, const char* catAtom = nullptr, char ifs = ' ');
    ~TextOutput() override;

    void configureMaxsat();
    void setModelPrinter(ModelPrinter printer);
    void printModelValues(const SharedContext& ctx, const Model& m);

private:
    enum ResultStr { res_unknown = 0, res_sat = 1, res_unsat = 2, res_opt = 3, num_str };
    enum CategoryKey {
        cat_comment,
        cat_value,
        cat_objective,
        cat_result,
        cat_value_term,
        cat_atom_name,
        cat_atom_var,
        num_cat
    };
    struct SolveProgress {
        int lines{0};
        int last{-1};
    };
    // Output interface
    void doStart(std::string_view solver, std::string_view version, std::span<const std::string> input) override;
    void startStep(double elapsed, uint32_t step) override;
    void stopStep(double elapsed, double stepElapsed) override;
    void enterState(double elapsed, Event::Subsystem sys, const char* activity) override;
    void exitState(double elapsed, Event::Subsystem sys, double stateElapsed) override;
    void printModel(double elapsed, const SharedContext& ctx, const Model& m, ModelFlag flags) override;
    void printUnsat(double elapsed, const SharedContext& ctx, const Model& m) override;
    void printProgress(double elapsed, const Event&, double stateElapsed) override;
    void printSummary(const ClaspFacade::Summary& run, bool final) override;
    void enterStats(StatsKey t, const char* name, uint32_t n) override;
    void printLogicProgramStats(const Asp::LpStats& stats) override;
    void printProblemStats(const ProblemStats& stats) override;
    void printSolverStats(const SolverStats& stats) override;
    void printUserStats(const StatisticObject& object) override;
    void doShutdown() override;

    // implementation
    [[nodiscard]] const char* fieldSeparator() const;
    [[nodiscard]] const char* getIfsSuffix(char ifs, CategoryKey cat) const;
    [[nodiscard]] const char* getIfsSuffix(CategoryKey cat) const;
    [[nodiscard]] static auto indent(const char* key) { return std::pair{key, 2}; }

    void printEnter(const char* message, const char* suffix);
    void printExit(double stateElapsed);
    void printMeta(const SharedContext& ctx, const Model& m);
    void printCosts(SumView, char ifs, const char* ifsSuffix = "");
    void printCosts(SumView);
    void printBounds(SumView lower, SumView upper);
    void printSolveEvent(double elapsed, const Event& ev, double stateTime);
    void printPreproEvent(double stateTime, const Event& ev);
    void printChildren(const StatisticObject& s, int level = 0, const char* prefix = "");
    void clearProgress(int nLines);
    void startSection(const char* section) const;
    void startObject(const char* object, uint32_t n) const;

    ModelPrinter  onModel_;
    const char*   result_[num_str]; //!< Default result strings.
    const char*   format_[num_cat]; //!< Format strings.
    std::string   fmt_;
    SolveProgress progress_{}; // for printing solve progress
    int           width_{0};   // output width
    char          ifs_[2]{};   // field separator
    bool          accu_{false};
};
//@}

} // namespace Clasp::Cli
