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
class Output : public EventHandler {
public:
    //! Supported levels for printing models, optimize values, and individual calls.
    enum PrintLevel {
        print_all  = 0, //!< Print all models, optimize values, or calls.
        print_best = 1, //!< Only print last model, optimize value, or call.
        print_no   = 2, //!< Do not print any models, optimize values, or calls.
    };
    explicit Output(uint32_t verb = 1);
    ~Output() override;
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

    using EventHandler::setVerbosity;
    void setVerbosity(uint32_t verb);
    void setModelQuiet(PrintLevel model);
    void setOptQuiet(PrintLevel opt);
    void setCallQuiet(PrintLevel call);

    //! Shall be called once on startup.
    virtual void run(const char* solver, const char* version, const std::string* begInput,
                     const std::string* endInput) = 0;
    //! Shall be called once on shutdown.
    virtual void shutdown(const ClaspFacade::Summary& summary);
    virtual void shutdown() = 0;
    //! Handles ClaspFacade events by forwarding calls to startStep() and stopStep().
    void onEvent(const Event& ev) override;
    //! Checks quiet-levels and forwards to printModel() if appropriate.
    bool onModel(const Solver& s, const Model& m) override;
    //! Checks quiet-levels and forwards to printLower() if appropriate.
    bool onUnsat(const Solver& s, const Model& m) override;
    //! Shall print the given model.
    virtual void printModel(const OutputTable& out, const Model& m, PrintLevel x) = 0;
    //! Called on unsat - may print new info.
    virtual void printUnsat(const OutputTable& out, const LowerBound* lower, const Model* prevModel);
    //! A solving step has started.
    virtual void startStep(const ClaspFacade&);
    //! A solving step has stopped.
    virtual void stopStep(const ClaspFacade::Summary& summary);
    //! Shall print the given summary.
    virtual void printSummary(const ClaspFacade::Summary& summary, bool final) = 0;
    //! Shall print the given statistics.
    virtual void printStatistics(const ClaspFacade::Summary& summary, bool final) = 0;

protected:
    using OutPair = std::pair<const char*, Literal>;
    using UPtr    = uintptr_t;
    using UPair   = std::pair<uint32_t, uint32_t>;
    void                       printWitness(const OutputTable& out, const Model& m, UPtr data);
    virtual UPtr               doPrint(const OutPair& out, uintptr_t data);
    [[nodiscard]] static UPair numCons(const OutputTable& out, const Model& m);
    [[nodiscard]] static bool  stats(const ClaspFacade::Summary& summary);
    [[nodiscard]] double       elapsedTime() const;
    [[nodiscard]] double       modelTime() const;

private:
    using SumPtr = const ClaspFacade::Summary*;
    double   time_;             // time of first event
    double   model_;            // elapsed time on last model
    SumPtr   summary_{nullptr}; // summary of last step
    uint32_t verbose_{0};       // verbosity level
    uint8_t  quiet_[3]{};       // quiet levels for models, optimize, calls
    bool     last_ = false;     // print last model on summary
};

//! Prints models and solving statistics in Json-format to stdout.
class JsonOutput
    : public Output
    , private StatsVisitor {
public:
    explicit JsonOutput(uint32_t verb);
    ~JsonOutput() override;
    void run(const char* solver, const char* version, const std::string* begInput,
             const std::string* endInput) override;
    using Output::shutdown;
    void shutdown() override;
    void printSummary(const ClaspFacade::Summary& summary, bool final) override;
    void printStatistics(const ClaspFacade::Summary& summary, bool final) override;

private:
    enum ObjType { type_object, type_array };
    void startStep(const ClaspFacade&) override;
    void stopStep(const ClaspFacade::Summary& summary) override;
    void printModel(const OutputTable& out, const Model& m, PrintLevel x) override;
    void printUnsat(const OutputTable& out, const LowerBound* lower, const Model* prevModel) override;
    bool visitThreads(Operation op) override;
    bool visitTester(Operation op) override;
    bool visitHccs(Operation op) override;
    void visitThread(uint32_t, const SolverStats& stats) override;
    void visitHcc(uint32_t, const ProblemStats& p, const SolverStats& s) override;
    void visitLogicProgramStats(const Asp::LpStats& stats) override;
    void visitProblemStats(const ProblemStats& stats) override;
    void visitSolverStats(const SolverStats& stats) override;
    void visitExternalStats(const StatisticObject& stats) override;
    UPtr doPrint(const OutPair& out, UPtr data) override;

    [[nodiscard]] bool     hasWitnesses() const { return objStack_.size() > 2 && *objStack_.rbegin() == '['; }
    [[nodiscard]] uint32_t indent() const { return size32(objStack_) * 2; }

    void printChildren(const StatisticObject& s);
    void pushObject(const char* k = nullptr, ObjType t = type_object, bool startIndent = false);
    char popObject();
    void printKeyValue(const char* k, const char* v);
    void printKeyValue(const char* k, uint64_t v);
    void printKeyValue(const char* k, uint32_t v);
    void printKeyValue(const char* k, double d);
    void printKeyValue(const char* k, const StatisticObject& o);
    void printString(const char* s, const char* sep);
    void printKey(const char* k);
    void printCosts(SumView costs, const char* name = "Costs");
    void printSum(const char* name, SumView sum, const Wsum_t* last = nullptr);
    void printCons(const UPair& cons);
    void printCoreStats(const CoreStats&);
    void printExtStats(const ExtendedStats&, bool generator);
    void printJumpStats(const JumpStats&);
    void printTime(const char* name, double t);
    void startWitness(double time);
    void endWitness();
    void popUntil(uint32_t sz);

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
class TextOutput
    : public Output
    , private StatsVisitor {
public:
    //! Supported text formats.
    enum Format { format_asp, format_aspcomp, format_sat09, format_pb09 };
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

    const char* result[num_str]; //!< Default result strings.
    const char* format[num_cat]; //!< Format strings.

    TextOutput(uint32_t verbosity, Format fmt, const char* catAtom = nullptr, char ifs = ' ');
    ~TextOutput() override;

    //! Prints a (comment) message containing the given solver and input.
    void run(const char* solver, const char* version, const std::string* begInput,
             const std::string* endInput) override;
    using Output::shutdown;
    void shutdown() override;
    //! Prints the given model.
    /*!
     * Prints format[cat_value] followed by the elements of the model. Individual
     * elements e are printed as format[cat_atom] and separated by the internal field separator.
     */
    void printModel(const OutputTable& out, const Model& m, PrintLevel x) override;
    //! Prints the given lower bound and upper bounds that are known to be optimal.
    void printUnsat(const OutputTable& out, const LowerBound* lower, const Model* prevModel) override;
    //! Called once a solving step has completed.
    /*!
     * Always prints "format[cat_result] result[s.result()]".
     * Furthermore, if verbosity() > 0, prints a summary consisting of
     *   - the number of computed models m and whether the search space was exhausted
     *   - the number of enumerated models e if e != m
     *   - the state of any optimization and whether the last model was optimal
     *   - the state of consequence computation and whether the last model corresponded to the consequences
     *   - timing information
     *   .
     */
    void printSummary(const ClaspFacade::Summary& s, bool final) override;
    void printStatistics(const ClaspFacade::Summary& s, bool final) override;
    //! Prints progress events (preprocessing/solving) if verbosity() > 1.
    void onEvent(const Event& ev) override;
    //! A solving step has started.
    void startStep(const ClaspFacade&) override;
    //! A solving step has finished.
    void stopStep(const ClaspFacade::Summary& s) override;
    //! Prints a comment message.
    void comment(uint32_t v, const char* fmt, ...) const;

protected:
    //! Called on each model to be printed.
    /*!
     * The default implementation calls printValues().
     */
    virtual void printModelValues(const OutputTable& out, const Model& m);

    bool visitThreads(Operation op) override;
    bool visitTester(Operation op) override;

    void visitThread(uint32_t, const SolverStats& stats) override;
    void visitHcc(uint32_t, const ProblemStats& p, const SolverStats& s) override;
    void visitLogicProgramStats(const Asp::LpStats& stats) override;
    void visitProblemStats(const ProblemStats& stats) override;
    void visitSolverStats(const SolverStats& stats) override;
    void visitExternalStats(const StatisticObject& stats) override;

    UPtr                      doPrint(const OutPair& out, UPtr data) override;
    [[nodiscard]] const char* fieldSeparator() const;
    [[nodiscard]] int         printSep(CategoryKey c) const;
    void                      printCosts(SumView) const;
    void                      printBounds(SumView lower, SumView upper) const;
    void                      printStats(const SolverStats& stats) const;
    void                      printJumps(const JumpStats&) const;
    bool                      startSection(const char* n) const;
    void                      startObject(const char* n, uint32_t i) const;
    void                      setState(uint32_t state, uint32_t verb, const char* st);
    void                      printSolveProgress(const Event& ev);
    void                      printValues(const OutputTable& out, const Model& m);
    void                      printMeta(const OutputTable& out, const Model& m);
    void                      printChildren(const StatisticObject& s, unsigned level = 0, const char* prefix = nullptr);
    int printChildKey(unsigned level, const char* key, uint32_t idx, const char* prefix = nullptr) const;

private:
    void                      printCostsImpl(SumView, char ifs, const char* ifsSuffix = "") const;
    [[nodiscard]] const char* getIfsSuffix(char ifs, CategoryKey cat) const;
    [[nodiscard]] const char* getIfsSuffix(CategoryKey cat) const;
    bool                      clearProgress(int nLines);
    struct SolveProgress {
        int  lines;
        int  last;
        void clear() {
            lines = 0;
            last  = -1;
        }
    };
    std::string   fmt_;
    double        stTime_{};   // time on state enter
    SolveProgress progress_{}; // for printing solve progress
    int           width_{0};   // output width
    uint32_t      state_{0};   // active state
    char          ifs_[2]{};   // field separator
    bool          accu_{false};
};
//@}

} // namespace Clasp::Cli
