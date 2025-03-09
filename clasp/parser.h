//
// Copyright (c) 2014-present Benjamin Kaufmann
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

#include <clasp/claspfwd.h>
#include <clasp/literal.h>

#include <potassco/match_basic_types.h>

/*!
 * \file
 * \brief Defines parsers for supported input formats.
 */
namespace Clasp {
/////////////////////////////////////////////////////////////////////////////////////////
// PARSING BASE
/////////////////////////////////////////////////////////////////////////////////////////
/*!
 * \addtogroup problem
 */
//@{

//! Auto-detect type of program given in prg.
ProblemType detectProblemType(std::istream& prg);

//! Parse additional information in symbol table/comments.
struct ParserOptions {
    //! Supported parser extensions.
    enum Extension : uint8_t {
        parse_heuristic = 1u,  //!< Parse heuristic info in smodels, dimacs, and pb format.
        parse_acyc_edge = 2u,  //!< Parse acyc info in smodels, dimacs, and pb format.
        parse_minimize  = 4u,  //!< Parse cost function in dimacs format.
        parse_project   = 8u,  //!< Parse project directive in dimacs and pb format.
        parse_assume    = 16u, //!< Parse assumption directive in dimacs and pb format.
        parse_output    = 32u, //!< Parse output directive in dimacs and pb format.
        parse_full      = 63u,
        parse_maxsat    = 128u //!< Parse dimacs as MaxSAT problem
    };
    constexpr ParserOptions() = default;
    [[nodiscard]] bool isEnabled(Extension e) const { return Potassco::test_mask(set, Potassco::to_underlying(e)); }
    [[nodiscard]] bool anyOf(uint8_t f) const { return Potassco::test_any(set, f); }

    ParserOptions& enableHeuristic() { return enable(parse_heuristic); }
    ParserOptions& enableAcycEdges() { return enable(parse_acyc_edge); }
    ParserOptions& enableMinimize() { return enable(parse_minimize); }
    ParserOptions& enableProject() { return enable(parse_project); }
    ParserOptions& enableAssume() { return enable(parse_assume); }
    ParserOptions& enableOutput() { return enable(parse_output); }
    ParserOptions& assign(uint8_t f, bool b) {
        b ? Potassco::store_set_mask(set, f) : Potassco::store_clear_mask(set, f);
        return *this;
    }
    ParserOptions& enable(Extension e) {
        Potassco::store_set_mask(set, Potassco::to_underlying(e));
        return *this;
    }
    uint8_t set{0};
};
//! Base class for parsers.
class ProgramParser {
public:
    using StrategyType = Potassco::ProgramReader;
    ProgramParser();
    virtual ~ProgramParser();
    bool               accept(std::istream& str, const ParserOptions& o = ParserOptions());
    [[nodiscard]] bool incremental() const;
    [[nodiscard]] bool isOpen() const;
    bool               parse();
    bool               more();
    void               reset();

private:
    virtual StrategyType* doAccept(std::istream& str, const ParserOptions& o) = 0;
    StrategyType*         strat_;
};

//! Parser for logic programs in smodels-internal or aspif format.
class AspParser final : public ProgramParser {
public:
    static bool accept(char c);
    explicit AspParser(Asp::LogicProgram& prg);
    enum Format { format_smodels = -1, format_aspif = 1 };
    static void write(Asp::LogicProgram& prg, std::ostream& os);
    static void write(Asp::LogicProgram& prg, std::ostream& os, Format f);

private:
    StrategyType* doAccept(std::istream& str, const ParserOptions& o) override;

    Asp::LogicProgram*                         lp_;
    std::unique_ptr<StrategyType>              in_;
    std::unique_ptr<Potassco::AbstractProgram> out_;
};
/////////////////////////////////////////////////////////////////////////////////////////
// SAT parsing
/////////////////////////////////////////////////////////////////////////////////////////
//! Base class for dimacs and opb parser.
class SatReader : public Potassco::ProgramReader {
public:
    SatReader();
    ParserOptions options;

protected:
    bool         skipLines(char start);
    bool         skipMatch(const std::string_view& word);
    void         parseExt(const char* pre, SharedContext& ctx);
    Wsum_t       matchWeightSum(Wsum_t min, const char* what);
    virtual void addObjective(WeightLitView) = 0;
    virtual void addAssumption(Literal x)    = 0;

private:
    // <project> ::= { <var> } <EOL>
    void parseProject(SharedContext& ctx);
    // <assume> ::= { <literal> } <EOL>
    void parseAssume();
    // <heuristic> ::= <type> <var> <bias> <prio> <literal_condition>
    void parseHeuristic(SharedContext& ctx);
    // <output> ::= "range" <var_lo> <var_hi>
    //           |  <literal_condition> <string> <EOL>
    void    parseOutput(SharedContext& ctx);
    void    parseGraph(const char* pre, ExtDepGraph& graph);
    Literal matchExtLit();
};
//! Parser for (extended) dimacs format.
class DimacsReader final : public SatReader {
public:
    static bool accept(char c) { return c == 'c' || c == 'p'; }
    explicit DimacsReader(SatBuilder&);

private:
    bool doAttach(bool& inc) override;
    bool doParse() override;
    void addObjective(WeightLitView) override;
    void addAssumption(Literal x) override;
    void parsePbConstraint(WeightLitVec& scratch);
    void parseConstraintRhs(WeightLitVec& lhs);
    void parseAtLeastK(WeightLitVec& scratch);

    SatBuilder* program_{nullptr};
    Var_t       numVar_{0};
    bool        wcnf_{false};
    bool        plus_{false};
};
//! Parser for opb format.
class OpbReader final : public SatReader {
public:
    explicit OpbReader(PBBuilder&);
    static bool accept(char c) { return c == '*'; }

private:
    bool doAttach(bool& inc) override;
    bool doParse() override;
    void addObjective(WeightLitView vec) override;
    void addAssumption(Literal x) override;
    void parseOptObjective();
    void parseConstraint();
    void parseSum();
    void parseTerm();

    PBBuilder* program_{nullptr};
    Weight_t   minCost_{0};
    Weight_t   maxCost_{0};
    struct Temp {
        WeightLitVec lits;
        LitVec       term;
        Weight_t     bound;
        bool         eq;
    } active_{};
};
//! Parser for SAT or PB problems.
class SatParser : public ProgramParser {
public:
    explicit SatParser(SatBuilder& prg);
    explicit SatParser(PBBuilder& prg);

protected:
    StrategyType* doAccept(std::istream& str, const ParserOptions& o) override;

private:
    std::unique_ptr<SatReader> reader_;
};
//@}

} // namespace Clasp
