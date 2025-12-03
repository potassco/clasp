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
class OutputSink {
public:
    //! Creates an output sink that writes to the given FILE object.
    explicit(false) OutputSink(FILE* file);
    //! Creates an output sink that writes to the given std::ostream.
    explicit(false) OutputSink(std::ostream& os);
    //! Creates an output sink that appends to the given character buffer.
    template <Potassco::CharBuffer C>
    explicit(false) OutputSink(C& buffer) {
        static auto vtab = VTable{
            .write = +[](void* o, std::string_view s) { return static_cast<C*>(o)->append(s), s.size(); },
            .flush = &noFlush,
            .file  = &noFile,
        };
        vptr_ = &vtab;
        impl_ = &buffer;
    }
    //! Returns the associated FILE object or nullptr if the sink is not directly connected to a FILE.
    [[nodiscard]] auto file() const -> FILE* { return vptr_->file(impl_); }
    //! Writes the given string to the associated sink.
    auto write(std::string_view s) -> std::size_t { return vptr_->write(impl_, s); } // NOLINT
    //! Flushes the associated sink.
    void flush() { return vptr_->flush(impl_); } // NOLINT

private:
    static void noFlush(void*) {}
    static auto noFile(void*) -> FILE* { return nullptr; }
    struct VTable {
        auto (*write)(void*, std::string_view) -> std::size_t;
        void (*flush)(void*);
        auto (*file)(void*) -> FILE*;
    };
    VTable* vptr_;
    void*   impl_;
};

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
    //! Supported output modes.
    /*!
     * Output mode `mode_clingo` enables output more tailored to clingo.
     */
    enum Mode : uint8_t { mode_default, mode_clingo };
    explicit Output(OutputSink sink, uint32_t verb = 1, Mode mode = mode_default);
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
    //! Active output mode.
    [[nodiscard]] Mode mode() const { return static_cast<Mode>(mode_); }

    void setVerbosity(uint32_t verb);
    void setModelQuiet(PrintLevel model);
    void setOptQuiet(PrintLevel opt);
    void setCallQuiet(PrintLevel call);
    void setMode(Mode mode);
    //! Enable ansi colors in output
    /*!
     * If enabled, output written to the output sink is embellished with ansi color codes.
     * \throw std::invalid_argument if style is invalid
     */
    void enableColor(bool enable, std::string_view style = {});

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
    using SinkLock  = std::unique_ptr<void, void (*)(void*)>;
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
    //
    void setResultString(ResultStr r, const char* str);
    auto lockSink() -> SinkLock;
    auto write(std::string_view s) -> std::size_t;
    void flush();
    void splitStateTime();

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
    virtual void enterState(ElapsedTime elapsed, Event::Subsystem sys);
    //! Called on exiting the previously entered subsystem state.
    virtual void exitState(ElapsedTime elapsed, Event::Subsystem sys, ElapsedTime stateElapsed, ElapsedTime stateSplit);
    //! Called on model that should be printed.
    virtual void printModel(ElapsedTime elapsed, const SharedContext& ctx, const Model& m, ModelFlag flags) = 0;
    //! Called on unsat.
    virtual void printUnsat(ElapsedTime elapsed, const SharedContext& ctx, const Model& m) = 0;
    //! Called for relevant progress events from the last started subsystem state.
    virtual void printProgress(ElapsedTime elapsed, const Event&, ElapsedTime stateElapsed, ElapsedTime stateSplit);
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
    void               transition(ElapsedTime elapsed, Event::Subsystem to);
    void               summary(const ClaspFacade::Summary& summary, bool final);
    void               visitStats(const ClaspFacade::Summary& summary);

    using SumPtr = const ClaspFacade::Summary*;
    using State  = Event::Subsystem;
    OutputSink  sink_;              // output sink to write to
    const char* result_[num_str]{}; // result strings
    ColorStyle  style_;
    struct {
        double      start{}; // time on start
        double      step{};  // time on step enter
        double      enter{}; // time on state enter
        double      split{}; // time on last split
        ElapsedTime model{}; // elapsed time on last model
    } time_;                 // timing information
    State    state_{};       // current state
    uint32_t verbose_{0};    // verbosity level
    uint8_t  quiet_[3]{};    // quiet levels for models, optimize, calls
    uint8_t  lastM_ : 1 {0}; // print last model on summary
    uint8_t  lastC_ : 1 {0}; // print last call summary
    uint8_t  mode_  : 1 {0}; // output mode
};

//! Prints models and solving statistics in Json-format to the given sink.
class JsonOutput final : public Output {
public:
    explicit JsonOutput(OutputSink sink, uint32_t verb, Mode mode = mode_default);
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
 * Prints all output to the given sink in given format:
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
    //! Custom atom format template.
    class CatAtom {
    public:
        //! Creates a default (empty) template that does not apply any additional formatting.
        /*!
         * \note The empty template is conceptually equivalent to `%0`.
         */
        CatAtom() = default;
        //! Creates a template from the given string.
        /*!
         * \param fmt String to parse - in the format `<atom-fmt>[:<var-fmt>]`, where both <atom-fmt> and <var-fmt> are
         *            (possibly empty) format strings containing a single argument `%0`.
         * \throw std::invalid_argument if `fmt` is not well-formed.
         * \note If the optional part is not given, `<atom-fmt>` is used for both atom and variable output.
         */
        static CatAtom fromString(std::string_view fmt);

        //! Returns `hasAtom()` || `hasVar()`.
        explicit           operator bool() const noexcept;
        [[nodiscard]] auto hasAtom() const -> bool;
        [[nodiscard]] auto hasVar() const -> bool;

        //! Writes the (atom) format template replacing `%0` with `atom`.
        void formatTo(Buffer& buf, std::string_view atom) const;
        //! Writes the (var) format template replacing `%0` with `lit.var()`.
        /*!
         * \note If `lit.sign()` is true, output is preceded by a `-`.
         */
        void formatTo(Buffer& buf, Literal lit) const;

    private:
        void        formatTo(Buffer& buf, const auto& v, uint32_t s, uint32_t m, uint32_t e) const;
        std::string buffer_;
        uint32_t    atomSep_{UINT32_MAX};
        uint32_t    varStart_{UINT32_MAX};
        uint32_t    varSep_{UINT32_MAX};
    };
    //! Template for extracting a theory assignment from theory atoms.
    class CatAssign {
    public:
        //! Creates an empty template that matches nothing.
        CatAssign() = default;
        //! Creates a template from the given parameters.
        /*!
         * \param id    Predicate id to match.
         * \param arity Predicate arity in the range [0;255].
         * \param args  Key and value arguments to extract from a matching atom in the range [0;arity).
         * \param sep   Key/value separator to use when printing a match.
         * \throw std::invalid_argument if arity or arguments are out of range.
         */
        CatAssign(std::string_view id, uint32_t arity, std::pair<uint32_t, uint32_t> args = {0, 1}, char sep = '=');
        //! Creates a template from the given string.
        /*!
         * \param str String to parse - must be in the format `<id>/<arity>` or `<id>/<arity>:%<x><sep>%<y>`
         * \throw std::invalid_argument if the string is not well-formed.
         * \return `CatAssign(<id>,<arity>)` or `CatAssign(<id>,<arity>,{<x>,<y>}, <sep>)` depending on the input.
         */
        static CatAssign fromString(std::string_view str);

        explicit           operator bool() const noexcept;
        [[nodiscard]] auto id() const -> std::string_view { return name_; }
        [[nodiscard]] auto arity() const noexcept -> uint8_t { return arity_; }
        [[nodiscard]] auto keyArg() const noexcept -> uint8_t { return keyArg_; }
        [[nodiscard]] auto valArg() const noexcept -> uint8_t { return valArg_; }
        [[nodiscard]] auto sep() const noexcept -> char { return sep_; }

        bool operator==(const CatAssign&) const noexcept = default;

    private:
        std::string name_;
        uint8_t     arity_{0};
        uint8_t     keyArg_{0};
        uint8_t     valArg_{0};
        char        sep_{0};
    };
    //! Template for extracting theory costs from theory atoms.
    class CatCost {
    public:
        //! Creates an empty template that matches nothing.
        CatCost() = default;
        //! Creates a template from the given parameters.
        /*!
         * \param id    Predicate id to match.
         * \param arity Predicate arity in the range [0;255].
         * \param fmtStr Format string to apply to matched atom - may contain argument references `%[0-arity)`.
         * \throw std::invalid_argument if arity or arguments in format string are out of range.
         */
        CatCost(std::string_view id, uint32_t arity, std::string_view fmtStr);
        //! Creates a template from the given string.
        /*!
         * \param str String to parse - must be in the format `<id>/<arity>:<fmt-str>`
         * \throw std::invalid_argument if the string is not well-formed.
         * \return `CatCost(<id>,<arity>,<fmt-str>)`.
         */
        static CatCost fromString(std::string_view str);

        explicit           operator bool() const noexcept;
        [[nodiscard]] auto id() const -> std::string_view { return std::string_view{template_}.substr(0, nameLen_); }
        [[nodiscard]] auto arity() const noexcept -> uint8_t { return arity_; }
        [[nodiscard]] auto fmtString() const noexcept -> std::string_view {
            return std::string_view{template_}.substr(nameLen_);
        }
        //! Formats the cost template replacing argument placeholders with the corresponding arguments from `args`.
        [[nodiscard]] auto format(std::span<std::string_view> args) const -> std::string;

        bool operator==(const CatCost&) const noexcept = default;

    private:
        std::string template_;
        std::size_t nameLen_{0};
        uint8_t     arity_{0};
    };
    //! Template for configuring time-step separated output.
    class CatStep {
    public:
        enum Arg : uint8_t { step_first, step_last };
        CatStep() = default;
        explicit CatStep(Arg timeArg, std::string_view stepCaption);
        //! Creates a template from the given string.
        /*!
         * \param str String to parse - must be in the format `{first,last}[:<name>]`
         * \throw std::invalid_argument if the string is not well-formed.
         * \return `CatStep{step_first|step_last,<name> or "State" if <name> is not given}`.
         */
        static CatStep fromString(std::string_view str);

        explicit operator bool() const noexcept;
        bool     operator==(const CatStep&) const noexcept = default;
        //! Returns the position of the time-step argument in output predicates.
        [[nodiscard]] auto stepArg() const -> Arg { return arg_; }
        //! Returns whether the time-step argument is the last argument of output predicates.
        [[nodiscard]] auto argLast() const -> bool { return arg_ == step_last; }
        //! Returns the name of the time-step argument, i.e. the caption to use for grouping predicates of a step.
        [[nodiscard]] auto argName() const -> std::string_view { return caption_; }

    private:
        std::string caption_;
        Arg         arg_{step_last};
        bool        active_{false};
    };

    //! Supported text formats.
    enum Format : uint8_t { format_asp, format_aspcomp, format_sat09, format_pb09, format_maxsat09 };

    struct Options {
        CatAtom   catAtom;
        CatAssign catAssign;
        CatCost   catCosts;
        CatStep   catStep;
        unsigned  verbosity{0};
        Format    format{format_asp};
        Mode      mode = mode_default;
        char      ifs{' '};
        char      predSep{' '};
    };
    TextOutput(OutputSink sink, const Options& options);
    ~TextOutput() override;

    void setModelPrinter(ModelPrinter printer);
    void printModelValues(const SharedContext& ctx, const Model& m);

private:
    struct Prefix {
        std::string_view comment;
        std::string_view cost;
        std::string_view result;
    };
    enum class Term : char {};
    struct Key;
    struct SolveProgress {
        enum Ev : int { ev_enter = -3, ev_clear = -2, ev_none = -1 };
        int lines{0};
        int last{ev_none};
    };
    // Output interface
    void doStart(std::string_view solver, std::string_view version, std::span<const std::string> input) override;
    void startStep(ElapsedTime elapsed, uint32_t step) override;
    void stopStep(ElapsedTime elapsed, ElapsedTime stepElapsed) override;
    void enterState(ElapsedTime elapsed, Event::Subsystem sys) override;
    void exitState(ElapsedTime elapsed, Event::Subsystem sys, ElapsedTime stateElapsed, ElapsedTime split) override;
    void printModel(ElapsedTime elapsed, const SharedContext& ctx, const Model& m, ModelFlag flags) override;
    void printUnsat(ElapsedTime elapsed, const SharedContext& ctx, const Model& m) override;
    void printProgress(ElapsedTime elapsed, const Event&, ElapsedTime stateElapsed, ElapsedTime split) override;
    void printSummary(const ClaspFacade::Summary& run, bool final) override;
    void enterStats(StatsKey t, const char* name, uint32_t n) override;
    void printLogicProgramStats(const Asp::LpStats& stats) override;
    void printProblemStats(const ProblemStats& stats) override;
    void printSolverStats(const SolverStats& stats) override;
    void printUserStats(const StatisticObject& object) override;
    void doShutdown() override;

    // implementation
    template <typename... Args>
    std::size_t print(std::string_view prefix, const TextStyle& st, Term t, const Args&... args);
    template <typename V, typename... Args>
    std::size_t printKeyValue(const TextStyle& st, Key k, const V& v, const Args&... args);
    std::size_t printComment(const TextStyle& st, Term t, const auto&... args) {
        return print(prefix_->comment, st, t, args...);
    }
    std::size_t printComment(const TextStyle& st, const auto&... args) { return printComment(st, Term{'\n'}, args...); }
    std::size_t printKeyValue(const Key& k, const auto& v, const auto&... args) {
        return printKeyValue(style().def, k, v, args...);
    }
    void printEnter(const char* message, Term term = {});
    void printExit(ElapsedTime stateElapsed);
    void printMeta(const SharedContext& ctx, const Model& m);
    void printSolveEvent(ElapsedTime elapsed, const Event& ev, ElapsedTime stateTime);
    void printPreproEvent(ElapsedTime stateTime, const Event& ev, ElapsedTime split);
    void printChildren(const StatisticObject& s, int level = 0, std::string_view prefix = {});
    void printAspModel(const SharedContext& ctx, const Model& m);
    void printSatModel(const SharedContext& ctx, const Model& m);
    void updateProgress(SolveProgress::Ev eventId, int nLines);
    auto br() -> std::size_t { return printComment(style().def); }
    auto openComment(Buffer& buf, const TextStyle& st, char term = '\n') const -> Buffer&;

    ModelPrinter  onModel_;         // (optional) custom model printer
    const Prefix* prefix_{nullptr}; // format prefixes
    CatAtom       fmtAtom_;         // custom atom format
    CatAssign     fmtAssign_;       // custom theory assignment format
    CatCost       fmtCost_;         // custom theory costs format
    CatStep       fmtStep_;         // group atoms by step?
    Buffer        header_;          // progress header
    SolveProgress progress_{};      // for printing solve progress
    uint32_t      width_{0};        // output width
    char          ifs_{' '};        // field separator
    char          predSep_{' '};    // predicate separator
    Format        fmt_{format_asp}; // output format
    bool          accu_{false};
};
//@}

} // namespace Clasp::Cli
