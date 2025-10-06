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

#include <potassco/format.h>

#include <chrono>
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
    using ElapsedTime = std::chrono::duration<double>;
    //! Supported levels for printing models, optimize values, and individual calls.
    enum PrintLevel {
        print_all  = 0, //!< Print all models, optimize values, or calls.
        print_best = 1, //!< Only print last model, optimize value, or call.
        print_no   = 2, //!< Do not print any models, optimize values, or calls.
    };
    explicit Output(FILE* sink, uint32_t verb = 1);
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
    //! Enable/Disable colorized output if supported.
    /*!
     * \şee enableAnsiColorSupport
     * \throw std::invalid_argument if style is invalid
     */
    auto enableColor(bool enable, std::string_view style = {}) -> std::errc;

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
    using Buffer    = Potassco::BasicCharBuffer;
    using TextStyle = Potassco::TextStyle;
    using FileLock  = std::unique_ptr<FILE, void (*)(FILE*)>;
    enum ModelFlag : uint32_t { model_quiet = 0u, model_values = 1u, model_meta = 2u, model_both = 3u };
    POTASSCO_ENABLE_BIT_OPS(ModelFlag, friend);
    enum StatsKey { stats_stats, stats_threads, stats_tester, stats_hccs, stats_thread, stats_hcc };
    enum ResultStr { res_unknown = 0, res_sat = 1, res_unsat = 2, res_opt = 3, num_str };
    struct ColorStyle {
        TextStyle trace;
        TextStyle info;
        TextStyle note;
        TextStyle warn;
        TextStyle err;
        TextStyle def;
    };
    [[nodiscard]] auto resultString(const ClaspFacade::Summary& summary) -> const char*;
    [[nodiscard]] auto style() const -> const ColorStyle& { return style_; }
    [[nodiscard]] auto optStyle(bool final) const -> TextStyle { return final ? style().warn : style().note; }
    void               setResultString(ResultStr r, const char* str);
    auto               write(std::string_view s) -> std::size_t;
    void               flush();

    // Prints shown symbols in model.
    // The function prints:
    // - true literals in definite answer, followed by
    // - true literals in current estimate if m.consequences()
    template <typename P>
    void printWitness(const SharedContext& ctx, const Model& model, P printer) {
        const auto& out = ctx.output;
        for (const auto& theory : out.theory_range()) {
            for (const char* x = theory->first(model); x; x = theory->next()) { printer(lit_true, x); }
        }
        const bool onlyD = model.type != Model::cautious || model.def;
        for (bool def = true;; def = not def) {
            for (const auto& pred : out.pred_range()) {
                if (model.isTrue(pred.cond) && (onlyD || model.isDef(pred.cond) == def)) {
                    printer(lit_true, pred.name.c_str());
                }
            }
            if (not out.vars_range().empty()) {
                const bool showNeg = not model.consequences();
                if (out.projectMode() == ProjectMode::output || not out.filter("_")) {
                    for (auto v : out.vars_range()) {
                        Literal p = posLit(v);
                        if ((showNeg || model.isTrue(p)) && (onlyD || model.isDef(p) == def)) {
                            printer(model.isTrue(p) ? p : ~p, nullptr);
                        }
                    }
                }
                else {
                    for (auto lit : out.proj_range()) {
                        if ((showNeg || model.isTrue(lit)) && (onlyD || model.isDef(lit) == def)) {
                            printer(model.isTrue(lit) ? lit : ~lit, nullptr);
                        }
                    }
                }
            }
            if (def == onlyD) {
                return;
            }
        }
    }
    void resetStateTime();
    auto lockSink() -> FileLock;

private:
    //! Called when color output is enabled/disabled.
    virtual void doEnableColor(bool);
    //! Called once on startup.
    virtual void doStart(std::string_view solver, std::string_view version, std::span<const std::string> input) = 0;
    //! Called when a new solving step is started.
    virtual void startStep(ElapsedTime elapsed, uint32_t step) = 0;
    //! Called after the active solving step has been solved.
    virtual void stopStep(ElapsedTime elapsed, ElapsedTime stepElapsed) = 0;
    //! Called on entering a new subsystem state.
    /*!
     * \note The function is only called for states whose verbosity level is `<= verbosity()`.
     */
    virtual void enterState(ElapsedTime elapsed, Event::Subsystem sys, const char* activity);
    //! Called on exiting the previously entered subsystem state.
    virtual void exitState(ElapsedTime elapsed, Event::Subsystem sys, ElapsedTime stateElapsed);
    //! Called on model that should be printed.
    virtual void printModel(ElapsedTime elapsed, const SharedContext& ctx, const Model& m, ModelFlag flags) = 0;
    //! Called on unsat.
    virtual void printUnsat(ElapsedTime elapsed, const SharedContext& ctx, const Model& m) = 0;
    //! Called for relevant progress events from the last started subsystem state.
    virtual void printProgress(ElapsedTime elapsed, const Event&, ElapsedTime stateElapsed);
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

    [[nodiscard]] static auto diffTime(double end, double start) -> ElapsedTime;

    [[nodiscard]] auto elapsedTime() const -> ElapsedTime;
    [[nodiscard]] auto flags(const Model& m, PrintLevel level) const -> ModelFlag;
    void               transition(ElapsedTime elapsed, Event::Subsystem to, const char* message);
    void               summary(const ClaspFacade::Summary& summary, bool final);
    void               visitStats(const ClaspFacade::Summary& summary);

    using SumPtr = const ClaspFacade::Summary*;
    using State  = Event::Subsystem;
    FILE*       sink_;              // output sink to write to
    const char* result_[num_str]{}; // result strings
    ColorStyle  style_;
    struct {
        double      start{}; // time on start
        double      step{};  // time on step enter
        double      enter{}; // time on state enter
        ElapsedTime model{}; // elapsed time on last model
    } time_;                 // timing information
    State    state_{};       // current state
    uint32_t verbose_{0};    // verbosity level
    uint8_t  quiet_[3]{};    // quiet levels for models, optimize, calls
    uint8_t  lastM_ : 1 {0}; // print last model on summary
    uint8_t  lastC_ : 1 {0}; // print last call summary
};

//! Prints models and solving statistics in Json-format to stdout.
class JsonOutput final : public Output {
public:
    explicit JsonOutput(FILE* sink, uint32_t verb);
    ~JsonOutput() override;

private:
    enum ObjType { type_object, type_array };
    struct JString;
    // Output interface
    void doStart(std::string_view solver, std::string_view version, std::span<const std::string> input) override;
    void startStep(ElapsedTime elapsed, uint32_t step) override;
    void stopStep(ElapsedTime elapsed, ElapsedTime stepElapsed) override;
    void printModel(ElapsedTime elapsed, const SharedContext& ctx, const Model& m, ModelFlag flags) override;
    void printUnsat(ElapsedTime elapsed, const SharedContext& out, const Model& m) override;
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
    [[nodiscard]] JString  jString(std::string_view s) const;

    void pushObject(std::string_view k = {}, ObjType t = type_object, bool startIndent = false);
    char popObject();
    void startWitness(ElapsedTime time);
    void endWitness();
    void popUntil(uint32_t sz);
    auto appendKey(Buffer& buffer, std::string_view key) -> Buffer&;
    template <typename T>
    void printKeyValue(std::string_view k, const T& v, const TextStyle* valStyle = nullptr);
    void printKeyValue(std::string_view k, ElapsedTime v) { printKeyValue(k, v.count(), &style().trace); }
    void printSum(std::string_view name, SumView sum, const Wsum_t* last = nullptr);
    void printCosts(SumView costs, std::string_view name = "Costs");
    void printCons(const SharedContext& ctx, const Model& m);
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
 * - format_maxsat prints in MaxSAT-competition format
 * .
 * \see https://www.mat.unical.it/aspcomp2013/
 * \see https://web.archive.org/web/20170809225851/https://www.satcompetition.org/2009/format-solvers2009.html
 * \see https://www.cril.univ-artois.fr/PB09/solver_req.html
 * \see http://www.maxsat.udl.cat/09/index.php?disp=requirements
 *
 */
class TextOutput : public Output {
public:
    using ModelPrinter = std::function<void(TextOutput&, const SharedContext&, const Model&)>;
    //! Custom atom format.
    class CatAtom {
    public:
        CatAtom() = default;
        /*!
         * <fmt> := <g-fmt> | <atom-fmt>:[<var-fmt>] | :<var-fmt>
         */
        static CatAtom     fromString(std::string_view fmt);
        [[nodiscard]] auto hasAtom() const -> bool;
        [[nodiscard]] auto hasVar() const -> bool;

        void formatTo(Buffer& buf, std::string_view atom) const;
        void formatTo(Buffer& buf, Literal lit) const;

    private:
        void        formatTo(Buffer& buf, const auto& v, uint32_t s, uint32_t m, uint32_t e) const;
        std::string buffer_;
        uint32_t    atomSep_{UINT32_MAX};
        uint32_t    varStart_{UINT32_MAX};
        uint32_t    varSep_{UINT32_MAX};
    };

    //! Supported text formats.
    enum Format : uint8_t { format_asp, format_aspcomp, format_sat09, format_pb09, format_maxsat09 };
    struct Options {
        CatAtom  catAtom;
        Format   format{format_asp};
        unsigned verbosity{0};
        char     ifs{' '};
    };
    TextOutput(FILE* sink, const Options& options);
    ~TextOutput() override;

    void setModelPrinter(ModelPrinter printer);
    void printModelValues(const SharedContext& ctx, const Model& m);

private:
    enum class Term : char {};
    struct Key;
    enum CategoryKey { cat_comment, cat_value, cat_objective, cat_result, cat_value_term, num_cat };
    struct SolveProgress {
        enum Ev : int { ev_enter = -3, ev_clear = -2, ev_none = -1 };
        int lines{0};
        int last{ev_none};
    };
    // Output interface
    void doStart(std::string_view solver, std::string_view version, std::span<const std::string> input) override;
    void startStep(ElapsedTime elapsed, uint32_t step) override;
    void stopStep(ElapsedTime elapsed, ElapsedTime stepElapsed) override;
    void enterState(ElapsedTime elapsed, Event::Subsystem sys, const char* activity) override;
    void exitState(ElapsedTime elapsed, Event::Subsystem sys, ElapsedTime stateElapsed) override;
    void printModel(ElapsedTime elapsed, const SharedContext& ctx, const Model& m, ModelFlag flags) override;
    void printUnsat(ElapsedTime elapsed, const SharedContext& ctx, const Model& m) override;
    void printProgress(ElapsedTime elapsed, const Event&, ElapsedTime stateElapsed) override;
    void printSummary(const ClaspFacade::Summary& run, bool final) override;
    void enterStats(StatsKey t, const char* name, uint32_t n) override;
    void printLogicProgramStats(const Asp::LpStats& stats) override;
    void printProblemStats(const ProblemStats& stats) override;
    void printSolverStats(const SolverStats& stats) override;
    void printUserStats(const StatisticObject& object) override;
    void doShutdown() override;

    // implementation
    [[nodiscard]] auto getIfsSuffix(char ifs, CategoryKey cat) const -> const char*;
    [[nodiscard]] auto getIfsSuffix(CategoryKey cat) const -> const char*;
    template <typename... Args>
    std::size_t print(std::string_view prefix, const TextStyle& st, Term t, const Args&... args);
    template <typename V, typename... Args>
    std::size_t printKeyValue(const TextStyle& st, Key k, const V& v, const Args&... args);
    std::size_t printComment(const TextStyle& st, Term t, const auto&... args) {
        return print(format_[cat_comment], st, t, args...);
    }
    std::size_t printComment(const TextStyle& st, const auto&... args) { return printComment(st, Term{'\n'}, args...); }
    std::size_t printKeyValue(const Key& k, const auto& v, const auto&... args) {
        return printKeyValue(style().def, k, v, args...);
    }
    void printEnter(const char* message, Term term = {});
    void printExit(ElapsedTime stateElapsed);
    void printMeta(const SharedContext& ctx, const Model& m);
    void printSolveEvent(ElapsedTime elapsed, const Event& ev, ElapsedTime stateTime);
    void printPreproEvent(ElapsedTime stateTime, const Event& ev);
    void printChildren(const StatisticObject& s, int level = 0, std::string_view prefix = {});
    void updateProgress(SolveProgress::Ev eventId, int nLines);
    auto br() -> std::size_t { return printComment(style().def); }
    auto openComment(Buffer& buf, const TextStyle& st, char term = '\n') const -> Buffer&;

    ModelPrinter  onModel_;           // (optional) custom model printer
    const char*   format_[num_cat]{}; // format strings
    CatAtom       fmtAtom_;           // custom atom format
    Buffer        header_;            // progress header
    SolveProgress progress_{};        // for printing solve progress
    uint32_t      width_{0};          // output width
    char          ifs_{' '};          // field separator
    Format        fmt_{format_asp};   // output format
    bool          accu_{false};
};
//@}

} // namespace Clasp::Cli
