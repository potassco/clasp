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
#include <clasp/parser.h>

#include <clasp/dependency_graph.h>
#include <clasp/logic_program.h>
#include <clasp/minimize_constraint.h>
#include <clasp/program_builder.h>
#include <clasp/shared_context.h>
#include <clasp/solver.h>

#include <potassco/aspif.h>
#include <potassco/smodels.h>
#include <potassco/theory_data.h>

#include <climits>
#include <istream>
#include <string>
#include <unordered_map>

namespace Clasp {
static_assert(std::is_same_v<Weight_t, Potassco::Weight_t>, "unexpected weight type");

ProblemType detectProblemType(std::istream& in) {
    for (std::istream::int_type x, line = 1, pos = 1; (x = in.peek()) != std::char_traits<char>::eof();) {
        char c = static_cast<char>(x);
        if (c == ' ' || c == '\t') {
            in.get();
            ++pos;
            continue;
        }
        if (AspParser::accept(c)) {
            return ProblemType::asp;
        }
        if (DimacsReader::accept(c)) {
            return ProblemType::sat;
        }
        if (OpbReader::accept(c)) {
            return ProblemType::pb;
        }
        POTASSCO_CHECK(c == '\n', std::errc::not_supported,
                       "parse error in line %d:%d: '%c': unrecognized input format", (int) line, (int) pos, c);
        in.get();
        ++line;
    }
    POTASSCO_ASSERT_NOT_REACHED("bad input stream");
}
/////////////////////////////////////////////////////////////////////////////////////////
// ProgramParser
/////////////////////////////////////////////////////////////////////////////////////////
ProgramParser::ProgramParser() : strat_(nullptr) {}
ProgramParser::~ProgramParser() = default;
bool ProgramParser::accept(std::istream& str, const ParserOptions& o) {
    if (strat_ = doAccept(str, o); strat_ != nullptr) {
        return true;
    }
    return false;
}
bool ProgramParser::isOpen() const { return strat_ != nullptr; }
bool ProgramParser::incremental() const { return strat_ && strat_->incremental(); }
bool ProgramParser::parse() { return strat_ && strat_->parse(); }
bool ProgramParser::more() { return strat_ && strat_->more(); }
void ProgramParser::reset() {
    if (strat_) {
        strat_->reset();
    }
    strat_ = nullptr;
}
/////////////////////////////////////////////////////////////////////////////////////////
// AspParser
/////////////////////////////////////////////////////////////////////////////////////////
AspParser::AspParser(Asp::LogicProgram& prg) : lp_(&prg), in_(nullptr), out_(nullptr) {}
bool AspParser::accept(char c) { return Potassco::BufferedStream::isDigit(c) || c == 'a'; }

AspParser::StrategyType* AspParser::doAccept(std::istream& str, const ParserOptions& o) {
    in_.reset();
    out_.reset();
    if (Potassco::BufferedStream::isDigit(static_cast<char>(str.peek()))) {
        Potassco::SmodelsInput::Options inOpts;
        inOpts.enableClaspExt();
        Asp::LogicProgramAdapter::Options lpOpts{};
        lpOpts.removeMinimize = true;
        if (o.isEnabled(ParserOptions::parse_acyc_edge)) {
            inOpts.convertEdges();
        }
        if (o.isEnabled(ParserOptions::parse_heuristic)) {
            inOpts.convertHeuristic();
        }
        out_ = std::make_unique<Asp::LogicProgramAdapter>(*lp_, lpOpts);
        in_  = std::make_unique<Potassco::SmodelsInput>(*out_, inOpts);
    }
    else {
        out_ = std::make_unique<Asp::LogicProgramAdapter>(*lp_);
        in_  = std::make_unique<Potassco::AspifInput>(*out_);
    }
    in_->setMaxVar(var_max - 1);
    return in_->accept(str) ? in_.get() : nullptr;
}

void AspParser::write(Asp::LogicProgram& prg, std::ostream& os) {
    write(prg, os, prg.supportsSmodels() ? format_smodels : format_aspif);
}
void AspParser::write(Asp::LogicProgram& prg, std::ostream& os, Format f) {
    using namespace Potassco;
    std::unique_ptr<AbstractProgram> out;
    if (f == format_aspif) {
        out = std::make_unique<AspifOutput>(os);
    }
    else {
        out = std::make_unique<SmodelsOutput>(os, true, prg.falseAtom());
    }
    if (prg.startAtom() == 1) {
        out->initProgram(prg.isIncremental());
    }
    out->beginStep();
    prg.accept(*out);
    out->endStep();
}
/////////////////////////////////////////////////////////////////////////////////////////
// clasp specific extensions for Dimacs/OPB
/////////////////////////////////////////////////////////////////////////////////////////
SatReader::SatReader() = default;
bool SatReader::skipLines(char c) {
    while (skipWs() == c) { skipLine(); }
    return true;
}
bool SatReader::skipMatch(const std::string_view& word) { return skipWs() && match(word); }

Wsum_t SatReader::matchWeightSum(Wsum_t min, const char* what) {
    return matchNum(min, std::numeric_limits<Wsum_t>::max(), what);
}

Literal SatReader::matchExtLit() {
    for (char c; (c = peek()) == ' ' || c == '\t';) { get(); }
    bool sign = peek() == '-';
    if (sign) {
        get();
    }
    if (peek() == 'x') {
        get();
    }
    return {matchAtomOrZero("identifier expected"), sign};
}

void SatReader::parseGraph(const char* pre, ExtDepGraph& graph) {
    auto maxNode = matchUint("graph: positive number of nodes expected");
    while (skipMatch(pre)) {
        if (skipMatch("node ")) {
            skipLine();
        }
        else if (skipMatch("arc ")) {
            auto lit = matchExtLit();
            auto beg = matchUint(0u, maxNode, "graph: invalid start node");
            auto end = matchUint(0u, maxNode, "graph: invalid end node");
            graph.addEdge(lit, beg, end);
        }
        else if (skipMatch("endgraph")) {
            return;
        }
        else {
            break;
        }
    }
    require(false, "graph: endgraph expected");
}
void SatReader::parseProject(SharedContext& ctx) {
    for (auto n = this->line(); (skipWs(), this->line() == n);) {
        auto x = matchExtLit();
        if (x == lit_true) {
            break;
        }
        require(not x.sign(), "project: positive literal expected");
        ctx.output.addProject(x);
    }
}
void SatReader::parseAssume() {
    for (auto n = this->line(); (skipWs(), this->line() == n);) {
        auto x = matchExtLit();
        if (x == lit_true) {
            break;
        }
        addAssumption(x);
    }
}
void SatReader::parseHeuristic(SharedContext& ctx) {
    using Potassco::DomModifier;
    auto type = matchEnum<DomModifier>("heuristic: modifier expected");
    auto atom = matchExtLit();
    require(not atom.sign(), "heuristic: positive literal expected");
    auto bias = static_cast<int16_t>(matchInt(INT16_MIN, INT16_MAX, "heuristic: bias expected"));
    auto prio = static_cast<uint16_t>(matchUint(0u, UINT16_MAX, "heuristic: priority expected"));
    ctx.heuristic.add(atom.var(), type, bias, prio, matchExtLit());
}
void SatReader::parseOutput(SharedContext& ctx) {
    if (skipMatch("range ")) {
        auto lo = matchExtLit();
        auto hi = matchExtLit();
        require(lo.var() <= hi.var(), "output: invalid range");
        ctx.output.setVarRange(Range32(lo.var(), hi.var() + 1));
    }
    else {
        auto cond = matchExtLit();
        while (peek() == ' ') { get(); }
        std::string name;
        for (char c; (c = get()) != '\n' && c;) { name += c; }
        name.erase(name.find_last_not_of(" \t") + 1);
        ctx.output.add(Potassco::ConstString(name, Potassco::ConstString::create_shared), cond);
    }
}
void SatReader::parseExt(const char* pre, SharedContext& ctx) {
    const bool acyc = options.isEnabled(ParserOptions::parse_acyc_edge);
    const bool minw = options.isEnabled(ParserOptions::parse_minimize);
    const bool proj = options.isEnabled(ParserOptions::parse_project);
    const bool heur = options.isEnabled(ParserOptions::parse_heuristic);
    const bool assu = options.isEnabled(ParserOptions::parse_assume);
    uint32_t   outp = options.isEnabled(ParserOptions::parse_output);
    for (ExtDepGraph* g = nullptr; skipMatch(pre);) {
        if (acyc && skipMatch("graph ")) {
            require(g == nullptr, "graph: only one graph supported");
            if (not ctx.extGraph.get()) {
                ctx.extGraph = std::make_unique<ExtDepGraph>();
            }
            else {
                ctx.extGraph->update();
            }
            g = ctx.extGraph.get();
            parseGraph(pre, *g);
            g->finalize(ctx);
        }
        else if (minw && skipMatch("minweight ")) {
            WeightLitVec min;
            for (unsigned n = this->line(); (skipWs(), this->line() == n);) {
                auto lit = matchExtLit();
                if (lit == lit_true) {
                    skipLine();
                    break;
                }
                min.push_back(WeightLiteral{lit, matchWeight(false, "minweight: weight expected")});
            }
            addObjective(min);
        }
        else if (proj && skipMatch("project ")) {
            parseProject(ctx);
        }
        else if (heur && skipMatch("heuristic ")) {
            parseHeuristic(ctx);
        }
        else if (assu && skipMatch("assume ")) {
            parseAssume();
        }
        else if (outp && skipMatch("output ")) {
            if (outp++ == 1) {
                ctx.output.setVarRange(Range32(0, 0));
            }
            parseOutput(ctx);
        }
        else {
            skipLine();
        }
    }
}

SatParser::SatParser(SatBuilder& prg) : reader_(std::make_unique<DimacsReader>(prg)) {}
SatParser::SatParser(PBBuilder& prg) : reader_(std::make_unique<OpbReader>(prg)) {}
ProgramParser::StrategyType* SatParser::doAccept(std::istream& str, const ParserOptions& o) {
    reader_->options = o;
    return reader_->accept(str) ? reader_.get() : nullptr;
}
/////////////////////////////////////////////////////////////////////////////////////////
// DimacsReader
/////////////////////////////////////////////////////////////////////////////////////////
DimacsReader::DimacsReader(SatBuilder& prg) : program_(&prg) {}

// Parses the p line: p [w]cnf[+] #vars #clauses [max clause weight]
bool DimacsReader::doAttach(bool& inc) {
    inc = false;
    if (not accept(peek())) {
        return false;
    }
    skipLines('c');
    require(skipMatch("p "), "missing problem line");
    auto knf = match("knf");
    wcnf_    = not knf && match("w");
    require(knf || match("cnf"), "unrecognized format, [w]cnf expected");
    plus_ = not knf && match("+");
    require(get() == ' ', "invalid problem line: expected ' ' after format");
    numVar_     = matchUint(0u, Clasp::var_max - 1, "#vars expected");
    auto   numC = matchUint("#clauses expected");
    Wsum_t cw   = 0;
    while (peek() == ' ') { get(); }
    if (wcnf_ && peek() != '\n') {
        cw = matchWeightSum(0, "wcnf: max clause weight expected");
    }
    while (peek() == ' ') { get(); }
    require(get() == '\n', "invalid extra characters in problem line");
    setMaxVar(numVar_);
    program_->prepareProblem(numVar_, cw, numC);
    if (options.anyOf(ParserOptions::parse_full)) {
        parseExt("c ", *program_->ctx());
    }
    return true;
}
bool DimacsReader::doParse() {
    LitVec       cc;
    WeightLitVec wlc;
    const bool   wcnf   = wcnf_;
    const bool   card   = plus_;
    const auto   minLit = -static_cast<int64_t>(numVar_), maxLit = static_cast<int64_t>(numVar_);
    setMaxVar(numVar_);
    for (int64_t cw = options.isEnabled(ParserOptions::parse_maxsat); skipLines('c') && skipWs(); cc.clear()) {
        if (wcnf) {
            cw = matchWeightSum(1, "wcnf: positive clause weight expected");
            skipWs();
        }
        if (not card || peek() != 'w') {
            int64_t lit = -1;
            while (stream()->readInt(lit) && lit != 0) {
                require(lit >= minLit && lit <= maxLit, "invalid variable in clause");
                cc.push_back(toLit(static_cast<int32_t>(lit)));
            }
            if (lit == 0) {
                program_->addClause(cc, cw);
            }
            else if (card) {
                wlc.clear();
                for (auto p : cc) { wlc.push_back(WeightLiteral{p, 1}); }
                parseConstraintRhs(wlc);
            }
            else {
                require(cc.empty() && !wcnf_ && match("k "), "invalid character in clause - '0' expected");
                parseAtLeastK(wlc);
            }
        }
        else {
            parsePbConstraint(wlc);
        }
    }
    require(not more(), "unrecognized format");
    return true;
}
void DimacsReader::addObjective(WeightLitView vec) { program_->addObjective(vec); }
void DimacsReader::addAssumption(Literal x) { program_->addAssumption(x); }
void DimacsReader::parseConstraintRhs(WeightLitVec& lhs) {
    auto c = get();
    require((c == '<' || c == '>') && match("= "), "constraint operator '<=' or '>=' expected");
    auto bound = matchWeight(false, "constraint bound expected");
    if (c == '<') {
        bound *= -1;
        for (auto& wl : lhs) { wl.weight *= -1; }
    }
    program_->addConstraint(lhs, bound);
}
void DimacsReader::parsePbConstraint(WeightLitVec& constraint) {
    constraint.clear();
    require(skipMatch("w"), "'w' expected");
    constexpr auto stop = std::string_view{"<>", 2};
    do {
        auto w = matchWeight(false, "invalid constraint weight");
        skipMatch("*");
        auto l = matchLit();
        constraint.push_back({toLit(l), w});
    } while (stop.find(skipWs()) == std::string_view::npos);
    parseConstraintRhs(constraint);
}
void DimacsReader::parseAtLeastK(WeightLitVec& scratch) {
    static_assert(sizeof(int) >= sizeof(Var_t));
    scratch.clear();
    const auto minLit = -static_cast<int>(numVar_), maxLit = static_cast<int>(numVar_);
    for (auto k = matchWeight(true, "invalid at-least-k constraint");;) {
        auto lit = matchInt(minLit, maxLit, "invalid variable in at-least-k constraint");
        if (lit == 0) {
            program_->addConstraint(scratch, k);
            return;
        }
        scratch.push_back({toLit(lit), 1});
    }
}
/////////////////////////////////////////////////////////////////////////////////////////
// OpbReader
/////////////////////////////////////////////////////////////////////////////////////////
OpbReader::OpbReader(PBBuilder& prg) : program_(&prg) {}

void OpbReader::addObjective(WeightLitView vec) { program_->addObjective(vec); }
void OpbReader::addAssumption(Literal x) { program_->addAssumption(x); }

// * #variable= int #constraint= int [#product= int sizeproduct= int] [#soft= int mincost= int maxcost= int sumcost=
// int] where [] indicate optional parts, i.e.
//  LIN-PBO: * #variable= int #constraint= int
//  NLC-PBO: * #variable= int #constraint= int #product= int sizeproduct= int
//  LIN-WBO: * #variable= int #constraint= int #soft= int mincost= int maxcost= int sumcost= int
//  NLC-WBO: * #variable= int #constraint= int #product= int sizeproduct= int #soft= int mincost= int maxcost= int
//  sumcost= int
bool OpbReader::doAttach(bool& inc) {
    inc = false;
    if (not accept(peek())) {
        return false;
    }
    require(skipMatch("* #variable="), "missing problem line '* #variable='");
    auto numV = matchUint(0u, Clasp::var_max - 1, "number of vars expected");
    require(skipMatch("#constraint="), "bad problem line: missing '#constraint='");
    auto     numC    = matchUint("number of constraints expected");
    unsigned numProd = 0, numSoft = 0;
    minCost_ = 0, maxCost_ = 0;
    if (skipMatch("#product=")) {
        // NLC instance
        numProd = matchUint();
        require(skipMatch("sizeproduct="), "'sizeproduct=' expected");
        std::ignore = matchUint();
    }
    if (skipMatch("#soft=")) { // WBO instance
        numSoft = matchUint();
        require(skipMatch("mincost="), "'mincost=' expected");
        minCost_ = matchWeight(true, "invalid min costs");
        require(skipMatch("maxcost="), "'maxcost=' expected");
        maxCost_ = matchWeight(true, "invalid max costs");
        require(skipMatch("sumcost="), "'sumcost=' expected");
        std::ignore = matchWeightSum(1, "positive integer expected");
    }
    setMaxVar(numV);
    program_->prepareProblem(numV, numProd, numSoft, numC);
    return true;
}
bool OpbReader::doParse() {
    if (options.anyOf(ParserOptions::parse_full - ParserOptions::parse_minimize)) {
        options.assign(ParserOptions::parse_minimize, false);
        parseExt("* ", *program_->ctx());
    }
    skipLines('*');
    parseOptObjective();
    for (;;) {
        skipLines('*');
        if (not more()) {
            return true;
        }
        parseConstraint();
    }
}
// <objective>::= "min:" <zeroOrMoreSpace> <sum>  ";"
// OR
// <softobj>  ::= "soft:" [<unsigned_integer>] ";"
void OpbReader::parseOptObjective() {
    if (skipMatch("min:")) {
        parseSum();
        program_->addObjective(active_.lits);
    }
    else if (skipMatch("soft:")) {
        auto softCost = matchWeightSum(1, "positive integer expected");
        require(skipMatch(";"), "semicolon missing after constraint");
        program_->setSoftBound(softCost);
    }
}

// <constraint>::= <sum> <relational_operator> <zeroOrMoreSpace> <integer> <zeroOrMoreSpace> ";"
// OR
// <softconstr>::= "[" <zeroOrMoreSpace> <unsigned_integer> <zeroOrMoreSpace> "]" <constraint>
void OpbReader::parseConstraint() {
    Weight_t cost = 0;
    if (skipMatch("[")) {
        cost = matchInt(minCost_, maxCost_, "invalid soft constraint cost");
        require(skipMatch("]"), "invalid soft constraint");
    }
    parseSum();
    active_.eq = skipMatch("=");
    require(active_.eq || match(">="), "relational operator expected");
    active_.bound = matchWeight(false, "invalid coefficient on rhs of constraint");
    require(skipMatch(";"), "semicolon missing after constraint");
    program_->addConstraint(active_.lits, active_.bound, active_.eq, cost);
}

// <sum>::= <weightedterm> | <weightedterm> <sum>
// <weightedterm>::= <integer> <oneOrMoreSpace> <term> <oneOrMoreSpace>
void OpbReader::parseSum() {
    active_.lits.clear();
    while (not skipMatch(";")) {
        auto coeff = matchInt(INT_MIN + 1, INT_MAX, "coefficient expected");
        parseTerm();
        Literal x = active_.term.size() == 1 ? active_.term[0] : program_->addProduct(active_.term);
        active_.lits.push_back(WeightLiteral{x, coeff});
        if (auto p = skipWs(); p == '>' || p == '=') {
            break;
        }
    }
}
// <term>::=<variablename>
// OR
// <term>::= <literal> | <literal> <space>+ <term>
void OpbReader::parseTerm() {
    active_.term.clear();
    char peek;
    do {
        skipMatch("*");             // optionally
        bool sign = skipMatch("~"); // optionally
        require(skipMatch("x"), "identifier expected");
        active_.term.push_back(Literal(matchAtom(), sign));
        peek = skipWs();
    } while (peek == '*' || peek == '~' || peek == 'x');
}

} // namespace Clasp
