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
#include "lpcompare.h"
#include <clasp/parser.h>

#include <clasp/minimize_constraint.h>
#include <clasp/solver.h>

#include <potassco/aspif.h>
#include <potassco/smodels.h>
#include <potassco/theory_data.h>

#include <catch2/catch_test_macros.hpp>

namespace Clasp::Test {

template <class Api>
static bool parse(Api& api, std::istream& str, const ParserOptions& opts = ParserOptions()) {
    ProgramParser& p = api.parser();
    return p.accept(str, opts) && p.parse();
}

static bool isEq(const std::ranges::iota_view<unsigned int, unsigned int>& lhs,
                 const std::ranges::iota_view<unsigned int, unsigned int>& rhs) {
    return lhs.begin() == rhs.begin() && lhs.end() == rhs.end();
}

using Potassco::AspifOutput;
using Potassco::SmodelsOutput;
namespace {
struct Input {
    std::stringstream prg;
    void              toSmodels(const char* txt, Var_t falseAt = 0) {
        prg.clear();
        prg.str("");
        SmodelsOutput            sm(prg, true, falseAt);
        Potassco::AspifTextInput x(&sm);
        std::stringstream        temp;
        temp << txt;
        REQUIRE(Potassco::readProgram(temp, x) == 0);
    }
    void toAspif(const char* txt) {
        std::stringstream temp;
        temp << txt;
        toAspif(temp);
    }
    void toAspif(std::istream& str) {
        prg.clear();
        prg.str("");
        AspifOutput              aspif(prg);
        Potassco::AspifTextInput x(&aspif);
        REQUIRE(Potassco::readProgram(str, x) == 0);
    }
    operator std::stringstream&() { return prg; }
};
struct NullBuilder final : ProgramBuilder {
    explicit NullBuilder(ProblemType type) : pt(static_cast<int>(type)) {}
    bool              doStartProgram() override { return true; }
    bool              doUpdateProgram() override { return true; }
    bool              doEndProgram() override { return true; }
    void              doGetAssumptions(LitVec&) const override {}
    [[nodiscard]] int doType() const override { return pt; }
    ProgramParser*    doCreateParser() override { return nullptr; }
    int               pt;
};
} // namespace
TEST_CASE("Smodels parser", "[parser][asp]") {
    SharedContext     ctx;
    Input             in;
    Asp::LogicProgram api;
    api.start(ctx, Asp::LogicProgram::AspOptions().noScc());
    SECTION("testEmptySmodels") {
        in.toSmodels("");
        REQUIRE(parse(api, in));
        api.endProgram();
        std::stringstream empty;
        REQUIRE(compareSmodels(empty, api));
    }
    SECTION("testSingleFact") {
        in.toSmodels("x1.");
        REQUIRE(parse(api, in));
        api.endProgram();
        REQUIRE(0u == ctx.numVars());
    }
    SECTION("testComputeStatementAssumptions") {
        in.toSmodels("x1 :- not x2.\n"
                     "x2 :- not x3.\n"
                     "x3 :- not x4.\n"
                     "x4 :- not x3.\n"
                     ":- x2.\n",
                     2);
        REQUIRE(parse(api, in));
        api.endProgram() && ctx.endInit();
        REQUIRE(ctx.master()->isTrue(api.getLiteral(3)));
        REQUIRE(ctx.master()->isTrue(api.getLiteral(1)));
        REQUIRE(ctx.master()->isFalse(api.getLiteral(2)));
        REQUIRE(ctx.master()->isFalse(api.getLiteral(4)));
    }
    SECTION("testTransformSimpleConstraintRule") {
        in.toSmodels("x1 :- 2{not x3, x2, x4}.\n"
                     "x2 :- not x3.\n"
                     "x3 :- not x2.\n"
                     "x4 :- not x3.\n");
        api.setExtendedRuleMode(Asp::LogicProgram::mode_transform_weight);
        REQUIRE(parse(api, in));
        REQUIRE(api.endProgram());
        REQUIRE(api.getLiteral(2) == api.getLiteral(1));
        REQUIRE(api.getLiteral(4) == api.getLiteral(1));
        in.toSmodels("x1 :- not x3.\n"
                     "x3 :-not x1.\n"
                     "x2 :- x1.\n"
                     "x4 :- x1.\n");
        REQUIRE(compareSmodels(in, api));
    }
    SECTION("testTransformSimpleWeightRule") {
        in.toSmodels("x1 :- 2 {x2=1, not x3=2, x4=3}.\n"
                     "x2 :- not x3.\n"
                     "x3 :- not x2.\n"
                     "x4 :-not x3.");
        api.setExtendedRuleMode(Asp::LogicProgram::mode_transform_weight);
        REQUIRE(parse(api, in));
        REQUIRE(api.endProgram());
        REQUIRE(1u == ctx.numVars());
        in.toSmodels("x1 :- not x3.\n"
                     "x3 :- not x1.\n"
                     "x2 :- x1.\n"
                     "x4 :- x1.\n");
        REQUIRE(compareSmodels(in, api));
    }
    SECTION("testTransformSimpleChoiceRule") {
        in.toSmodels("{x1;x2;x3} :- x2, not x3.\n"
                     "x2 :- not x1.\n"
                     "x3 :- not x2.");
        api.setExtendedRuleMode(Asp::LogicProgram::mode_transform_choice);
        REQUIRE(parse(api, in));
        REQUIRE(api.endProgram());
        in.toSmodels("x2. x4.");
        REQUIRE(compareSmodels(in, api));
    }
    SECTION("testSimpleConstraintRule") {
        in.toSmodels("x1 :- 2 {x3, x2, x4}.\n"
                     "x2 :- not x3.\n"
                     "x3 :- not x2.\n"
                     "x4 :- not x3.");
        REQUIRE(parse(api, in));
        REQUIRE(api.endProgram());
        REQUIRE(2u == ctx.numVars());
        in.toSmodels("x1 :- 2 {x3, x2 = 2}.\n"
                     "x2 :- not x3.\n"
                     "x3 :- not x2.\n"
                     "x4 :- x2.");
        REQUIRE(compareSmodels(in, api));
    }
    SECTION("testSimpleWeightRule") {
        in.toSmodels("x1 :- 2 {x3 = 2, x2 = 1, x4 = 3}. % but (x4 = 3 -> x4 = 2).\n"
                     "x2 :- not x3.\n"
                     "x3 :- not x2.\n"
                     "x4 :- not x3.");
        REQUIRE(parse(api, in));
        REQUIRE(api.endProgram());
        REQUIRE(2u == ctx.numVars());
        in.toSmodels("x1 :- 2 {x3 = 2, x2 = 3}.\n"
                     "x2 :- not x3.\n"
                     "x3 :- not x2.\n"
                     "x4 :- x2.");
        REQUIRE(compareSmodels(in, api));
    }
    SECTION("testSimpleChoiceRule") {
        in.toSmodels("{x1;x2;x3} :- x2, not x3.\n"
                     "x2 :- not x1.\n"
                     "x3 :- not x2.\n");
        REQUIRE(parse(api, in));
        REQUIRE(api.endProgram());
        in.toSmodels("x2.");
        REQUIRE(compareSmodels(in, api));
    }
    SECTION("testMinimizePriority") {
        in.toSmodels("{x1;x2;x3;x4}.\n"
                     "#minimize{not x1, not x2}.\n"
                     "#minimize{x3, x4}.");
        REQUIRE(parse(api, in));
        REQUIRE(api.endProgram());
        SharedMinimizeData* m1 = ctx.minimize();
        REQUIRE(m1->numRules() == 2);
        REQUIRE(contains(std::span(m1->lits, 2), WeightLiteral{api.getLiteral(3), 0}));
        REQUIRE(contains(std::span(m1->lits, 2), WeightLiteral{api.getLiteral(4), 0}));

        REQUIRE(contains(std::span(m1->lits + 2, 2), WeightLiteral{~api.getLiteral(1), 1}));
        REQUIRE(contains(std::span(m1->lits + 2, 2), WeightLiteral{~api.getLiteral(2), 1}));
    }
    SECTION("testEdgeDirectives") {
        in.toSmodels("{x1;x2}.\n"
                     "#output _edge(0,1)  : x1.\n"
                     "#output _acyc_1_1_0 : x2.");
        REQUIRE(parse(api, in, ParserOptions().enableAcycEdges()));
        REQUIRE((api.endProgram() && ctx.endInit()));
        REQUIRE(uint32_t(2) == ctx.stats().acycEdges);
    }
    SECTION("testHeuristicDirectives") {
        in.toSmodels("{x1;x2;x3}.\n"
                     "#output _heuristic(a,true,1) : x1.\n"
                     "#output _heuristic(_heuristic(a,true,1),true,1) : x2.\n"
                     "#output a : x3.");
        REQUIRE(parse(api, in, ParserOptions().enableHeuristic()));
        REQUIRE((api.endProgram() && ctx.endInit()));
        REQUIRE(ctx.heuristic.size() == 2);
    }
    SECTION("testSimpleIncremental") {
        in.toSmodels("#incremental.\n"
                     "{x1;x2} :-x3.\n"
                     "#external x3.\n"
                     "#step.\n"
                     "#external x3.[release]\n"
                     "{x3}.");
        api.updateProgram();
        ProgramParser& p = api.parser();
        REQUIRE(p.accept(in));
        REQUIRE(p.parse());
        REQUIRE(api.endProgram());
        REQUIRE(p.more());
        REQUIRE(api.stats.rules[0].sum() == 1);
        REQUIRE(api.isExternal(3));
        api.updateProgram();
        REQUIRE(p.parse());
        REQUIRE_FALSE(p.more());
        REQUIRE(api.stats.rules[0].sum() == 1);
        REQUIRE_FALSE(api.isExternal(3));
    }
    SECTION("testIncrementalMinimize") {
        in.toSmodels("#incremental.\n"
                     "{x1; x2}.\n"
                     "#minimize{not x1, not x2}.\n"
                     "#step."
                     "#minimize{x1, x2}.\n");
        api.updateProgram();
        ProgramParser& p = api.parser();
        REQUIRE(p.accept(in));
        REQUIRE(p.parse());
        REQUIRE(api.endProgram());
        SharedMinimizeData* m1 = ctx.minimize();
        m1->share();
        REQUIRE(contains(std::span(m1->lits, 2), WeightLiteral{~api.getLiteral(1), 1}));
        REQUIRE(contains(std::span(m1->lits, 2), WeightLiteral{~api.getLiteral(2), 1}));

        REQUIRE(p.more());
        api.updateProgram();
        REQUIRE(p.parse());
        REQUIRE_FALSE(p.more());
        REQUIRE(api.endProgram());
        SharedMinimizeData* m2 = ctx.minimize();
        REQUIRE(m1 != m2);
        REQUIRE(isSentinel(m2->lits[2].lit));
        REQUIRE(contains(std::span(m2->lits, 2), WeightLiteral{api.getLiteral(1), 1}));
        REQUIRE(contains(std::span(m2->lits, 2), WeightLiteral{api.getLiteral(2), 1}));
        m1->release();
    }
}

static bool sameProgram(Asp::LogicProgram& a, std::stringstream& prg) {
    std::stringstream out;
    AspParser::write(a, out, AspParser::format_aspif);
    prg.clear();
    prg.seekg(0);
    return compareProgram(prg, out);
}

TEST_CASE("Aspif parser", "[parser][asp]") {
    SharedContext     ctx;
    Input             in;
    Asp::LogicProgram api;
    api.start(ctx, Asp::LogicProgram::AspOptions().noScc());
    SECTION("testEmptyProgram") {
        in.toAspif("");
        REQUIRE(parse(api, in));
        REQUIRE(api.endProgram());
        REQUIRE(api.stats.rules[0].sum() == 0);
    }
    SECTION("testSingleFact") {
        in.toAspif("x1.");
        REQUIRE(parse(api, in));
        REQUIRE(api.endProgram());
        REQUIRE(api.stats.rules[0].sum() == 1);
        REQUIRE(api.getLiteral(1) == lit_true);
    }
    SECTION("testFactAfterRule") {
        in.toAspif("x1 :- not x2.\nx1.");
        REQUIRE(parse(api, in));
        REQUIRE(api.endProgram());
        REQUIRE(api.stats.rules[0].sum() == 2);
        REQUIRE(api.getLiteral(1) == lit_true);
        REQUIRE(api.getLiteral(2) == lit_false);
    }
    SECTION("testFactAfterRule2") {
        in.toAspif("x2 :- not x1.\nx1.");
        REQUIRE(parse(api, in));
        REQUIRE(api.endProgram());
        REQUIRE(api.stats.rules[0].sum() == 2);
        REQUIRE(api.getLiteral(1) == lit_true);
        REQUIRE(api.getLiteral(2) == lit_false);
    }
    SECTION("testFactAfterRule3") {
        in.toAspif("x2 :- x1.\nx1.");
        REQUIRE(parse(api, in));
        REQUIRE(api.endProgram());
        REQUIRE(api.stats.rules[0].sum() == 2);
        REQUIRE(api.getLiteral(1) == lit_true);
        REQUIRE(api.getLiteral(2) == lit_true);
    }
    SECTION("testFactAfterConstraint") {
        in.toAspif(":- x1.\nx1.");
        REQUIRE(parse(api, in));
        REQUIRE_FALSE(api.endProgram());
    }
    SECTION("testSimpleRule") {
        in.toAspif("x1 :- x3, not x2.");
        REQUIRE(parse(api, in));
        REQUIRE(api.stats.rules[0].sum() == 1);
        REQUIRE(api.numAtoms() == 3);
        REQUIRE(api.numBodies() == 1);
        REQUIRE(api.getBody(0)->size() == 2);
        REQUIRE(api.getBody(0)->goal(0) == posLit(3));
        REQUIRE(api.getBody(0)->goal(1) == negLit(2));
        REQUIRE(sameProgram(api, in));
    }
    SECTION("testInvalid") {
        std::stringstream prg;
        SECTION("Head") {
            prg << "x" << var_max << " :- not x2, x3.";
            in.toAspif(prg);
            REQUIRE_THROWS_AS(parse(api, in), std::runtime_error);
        }
        SECTION("Literal") {
            prg << "x1 :- not x" << var_max << ", x3.";
            in.toAspif(prg);
            REQUIRE_THROWS_AS(parse(api, in), std::runtime_error);
        }
    }

    SECTION("testIntegrityConstraint") {
        in.toAspif(":- not x1, x2.");
        REQUIRE(parse(api, in));
        REQUIRE(api.stats.rules[0].sum() == 1);
        REQUIRE(api.numAtoms() == 2);
        REQUIRE(api.numBodies() == 1);
        REQUIRE(api.getBody(0)->size() == 2);
        REQUIRE(api.getBody(0)->goal(0) == posLit(2));
        REQUIRE(api.getBody(0)->goal(1) == negLit(1));
        REQUIRE(api.getBody(0)->value() == value_false);
    }
    SECTION("testDisjunctiveRule") {
        in.toAspif("x1|x2.");
        REQUIRE(parse(api, in));
        REQUIRE(api.stats.rules[0].sum() == 1);
        REQUIRE(api.stats.disjunctions[0] == 1);
        REQUIRE(api.numAtoms() == 2);
        REQUIRE(sameProgram(api, in));
    }
    SECTION("testChoiceRule") {
        in.toAspif("{x1;x2;x3}.");
        REQUIRE(parse(api, in));
        REQUIRE(api.stats.rules[0].sum() == 1);
        REQUIRE(api.stats.rules[0][Asp::RuleStats::choice] == 1);
        REQUIRE(api.numAtoms() == 3);
        REQUIRE(sameProgram(api, in));
    }
    SECTION("testWeightRule") {
        in.toAspif("x1 :- 2{x2, x3, not x4}.\n"
                   "x5 :- 4{x2 = 2, x3, not x4 = 3}.\n");
        REQUIRE(parse(api, in));
        REQUIRE(api.stats.rules[0].sum() == 2);
        REQUIRE(api.stats.bodies[0][to_underlying(Asp::BodyType::sum)] == 1);
        REQUIRE(api.stats.bodies[0][to_underlying(Asp::BodyType::count)] == 1);
        REQUIRE(api.numBodies() == 2);
        REQUIRE((api.getBody(0)->bound() == 2 && not api.getBody(0)->hasWeights()));
        REQUIRE((api.getBody(1)->bound() == 4 && api.getBody(1)->hasWeights()));
        REQUIRE(sameProgram(api, in));
    }
    SECTION("testDisjunctiveWeightRule") {
        in.toAspif("x1|x2 :- 2{x3, x4, not x5}.");
        REQUIRE(parse(api, in));
        REQUIRE(sameProgram(api, in));
    }
    SECTION("testChoiceWeightRule") {
        in.toAspif("{x1;x2} :- 2{x3, x4, not x5}.");
        REQUIRE(parse(api, in));
        REQUIRE(sameProgram(api, in));
    }
    SECTION("testInvalidNegativeWeightInWeightRule") {
        in.toAspif("x1 :- 2 {x2 = -1, not x3 = 1, x4}.");
        REQUIRE_THROWS_AS(parse(api, in), std::runtime_error);
    }
    SECTION("testInvalidHeadInWeightRule") {
        in.prg << "asp 1 0 0" << "\n1 0 1 0 1 2 3 2 1 -3 1 4 1" << "\n0\n";
        REQUIRE_THROWS_AS(parse(api, in), std::runtime_error);
    }
    SECTION("testNegativeBoundInWeightRule") {
        in.toAspif("x1 :- -1 {x2, not x3, x4}.");
        REQUIRE(parse(api, in));
        REQUIRE(api.stats.rules[0].sum() == 1);
        REQUIRE(api.stats.bodies[0][to_underlying(Asp::BodyType::sum)] == 0);
    }
    SECTION("testMinimizeRule") {
        in.toAspif("{x1;x2;x3}.\n"
                   "#minimize{x1 = 2, x2, not x3 = 4}.");
        REQUIRE(parse(api, in));
        REQUIRE(api.stats.rules[0][Asp::RuleStats::minimize] == 1);
        REQUIRE(sameProgram(api, in));
    }
    SECTION("testMinimizeRuleMergePriority") {
        in.toAspif("#minimize{x1 = 2, x2, not x3 = 4}@1.\n"
                   "#minimize{x4 = 2, x2 = 2, x3 = 4}@1.");
        REQUIRE(parse(api, in));
        REQUIRE(api.stats.rules[0].sum() == 1);
        REQUIRE(api.stats.rules[0][Asp::RuleStats::minimize] == 1);
    }
    SECTION("testMinimizeRuleWithNegativeWeights") {
        in.toAspif("#minimize{x4 = -2, x2 = -1, x3 = 4}.");
        REQUIRE(parse(api, in));
        REQUIRE(api.stats.rules[0].sum() == 1);
        REQUIRE(api.endProgram());
        std::stringstream exp("6 0 2 2 4 2 2 1 ");
        REQUIRE(findSmodels(exp, api));
    }
    SECTION("testIncremental") {
        in.toAspif("#incremental.\n"
                   "{x1;x2}.\n"
                   "#minimize{x1=2, x2}.\n"
                   "#step.\n"
                   "{x3}.\n"
                   "#minimize{x3=4}.\n");

        REQUIRE(parse(api, in));
        REQUIRE(api.stats.rules[0].sum() == 2);
        REQUIRE(api.endProgram());

        ProgramParser& p = api.parser();
        REQUIRE(p.more());
        api.updateProgram();
        REQUIRE(p.parse());
        REQUIRE_FALSE(p.more());
        REQUIRE(api.stats.rules[0].sum() > 0);
        // minimize rule was merged
        REQUIRE(ctx.minimize()->numRules() == 1);
    }
    SECTION("testIncrementalExternal") {
        in.toAspif("#incremental."
                   "x1 :- x2.\n"
                   "#external x2. [true]\n"
                   "#step.\n"
                   "#external x2. [false]\n"
                   "#step.\n"
                   "#external x2. [release]\n");

        REQUIRE(parse(api, in));
        REQUIRE(api.endProgram());
        LitVec assume;
        api.getAssumptions(assume);
        REQUIRE((assume.size() == 1 && assume[0] == api.getLiteral(2)));

        ProgramParser& p = api.parser();
        REQUIRE(p.more());
        api.updateProgram();
        REQUIRE(p.parse());

        REQUIRE(api.endProgram());
        assume.clear();
        api.getAssumptions(assume);
        REQUIRE((assume.size() == 1 && assume[0] == ~api.getLiteral(2)));

        REQUIRE(p.more());
        api.updateProgram();
        REQUIRE(p.parse());
        REQUIRE_FALSE(p.more());
        REQUIRE(api.endProgram());
        assume.clear();
        api.getAssumptions(assume);
        REQUIRE(assume.empty());
        ctx.endInit();
        REQUIRE(ctx.master()->isFalse(api.getLiteral(2)));
    }
    SECTION("testSimpleEdgeDirective") {
        in.toAspif("{x1;x2}."
                   "#edge (0,1) : x1.\n"
                   "#edge (1,0) : x2.\n");
        REQUIRE(parse(api, in));
        REQUIRE((api.endProgram() && ctx.endInit()));
        REQUIRE(ctx.stats().acycEdges == 2);
        REQUIRE(sameProgram(api, in));
    }
    SECTION("testComplexEdgeDirective") {
        in.toAspif("{x1;x2;x3;x4}."
                   "#edge (0,1) : x1, not x2.\n"
                   "#edge (1,0) : x3, not x4.\n");
        REQUIRE(parse(api, in));
        REQUIRE((api.endProgram() && ctx.endInit()));
        REQUIRE(ctx.stats().acycEdges == 2);
        REQUIRE(sameProgram(api, in));
    }
    SECTION("testHeuristicDirective") {
        in.toAspif("{x1;x2;x3;x4}."
                   "#heuristic x1. [-1@1,sign]\n"
                   "#heuristic x1 : x3, not x4. [1@1,factor]");
        REQUIRE(parse(api, in));
        REQUIRE((api.endProgram() && ctx.endInit()));
        REQUIRE(ctx.heuristic.size() == 2);
        REQUIRE(ctx.heuristic.begin()->type() == DomModType::sign);
        REQUIRE((ctx.heuristic.begin() + 1)->type() == DomModType::factor);
        REQUIRE(ctx.heuristic.begin()->var() == (ctx.heuristic.begin() + 1)->var());
        REQUIRE(sameProgram(api, in));
    }

    SECTION("testOutputDirective") {
        in.toAspif("{x1;x2}."
                   "#output fact.\n"
                   "#output conj : x1, x2."
                   "#output lit : not x1.");
        REQUIRE(parse(api, in));
        REQUIRE((api.endProgram() && ctx.endInit()));
        REQUIRE(ctx.output.size() == 3);
        REQUIRE(sameProgram(api, in));
    }
    SECTION("testAssumptionDirective") {
        in.toAspif("{x1;x2}."
                   "#assume{not x2, x1}.");
        REQUIRE(parse(api, in));
        REQUIRE(api.endProgram());
        LitVec assume;
        api.getAssumptions(assume);
        REQUIRE(assume.size() == 2);
        REQUIRE(contains(assume, ~api.getLiteral(2)));
        REQUIRE(contains(assume, api.getLiteral(1)));
        REQUIRE(sameProgram(api, in));
    }
    SECTION("testProjectionDirective") {
        in.toAspif("{x1;x2;x3;x4}."
                   "#output a : x1.\n"
                   "#output b : x2.\n"
                   "#output c : x3.\n"
                   "#output d : x4.\n"
                   "#project{x1, x3}.");
        REQUIRE(parse(api, in));
        api.enableOutputState();
        REQUIRE(api.endProgram());
        REQUIRE(ctx.output.size() == 4);
        Literal a  = api.getLiteral(1);
        Literal b  = api.getLiteral(2);
        Literal c  = api.getLiteral(3);
        Literal d  = api.getLiteral(4);
        auto    pr = ctx.output.proj_range();
        REQUIRE(contains(pr, a));
        REQUIRE_FALSE(contains(pr, b));
        REQUIRE(contains(pr, c));
        REQUIRE_FALSE(contains(pr, d));
        REQUIRE(sameProgram(api, in));

        CHECK(api.getOutputState(1) == Asp::LogicProgram::out_all);
        CHECK(api.getOutputState(2) == Asp::LogicProgram::out_shown);
        CHECK(api.getOutputState(3) == Asp::LogicProgram::out_all);
        CHECK(api.getOutputState(4) == Asp::LogicProgram::out_shown);
    }
    SECTION("testEmptyProjectionDirective") {
        in.toAspif("{x1;x2;x3;x4}."
                   "#project.");
        REQUIRE(parse(api, in));
        REQUIRE(api.endProgram());
        REQUIRE(ctx.output.projectMode() == ProjectMode::project);
        REQUIRE(sameProgram(api, in));
    }
    SECTION("testIgnoreCommentDirective") {
        in.prg << "asp 1 0 0" << "\n" << to_underlying(Potassco::AspifType::comment) << " Ignore me!" << "\n0\n";
        REQUIRE(parse(api, in));
    }
    SECTION("testReadTheoryAtoms") {
        AspifOutput aspif(in.prg);
        aspif.initProgram(false);
        aspif.beginStep();
        aspif.theoryTerm(0, 1);   // (number 1)
        aspif.theoryTerm(1, 2);   // (number 2)
        aspif.theoryTerm(2, 3);   // (number 3)
        aspif.theoryTerm(3, 4);   // (number 4)
        aspif.theoryTerm(4, "x"); // (string x)
        aspif.theoryTerm(5, "z"); // (string z)
        aspif.theoryTerm(6, "+"); // (string +)
        aspif.theoryTerm(7, "*"); // (string *)
        std::vector<uint32_t> ids;
        aspif.theoryTerm(8, 4, ids = {0});      // (function x(1))
        aspif.theoryTerm(9, 4, ids = {1});      // (function x(2))
        aspif.theoryTerm(10, 4, ids = {2});     // (function x(3))
        aspif.theoryTerm(11, 7, ids = {0, 8});  // (term 1*x(1))
        aspif.theoryTerm(12, 7, ids = {1, 9});  // (term 2*x(2))
        aspif.theoryTerm(13, 7, ids = {2, 10}); // (term 3*x(3))
        aspif.theoryTerm(14, 7, ids = {3, 5});  // (term 4*z))

        aspif.theoryElement(0, ids = {11}, {});              // (element 1*x(1):)
        aspif.theoryElement(1, ids = {12}, {});              // (element 2*x(2):)
        aspif.theoryElement(2, ids = {13}, {});              // (element 3*x(3):)
        aspif.theoryElement(3, ids = {14}, {});              // (element 4*z:)
        aspif.theoryTerm(15, "sum");                         // (string sum)
        aspif.theoryTerm(16, ">=");                          // (string >=)
        aspif.theoryTerm(17, 42);                            // (number 42)
        aspif.theoryAtom(1, 15, ids = {0, 1, 2, 3}, 16, 17); // (&sum { 1*x(1); 2*x(2); 3*x(3); 4*z     } >= 42)
        aspif.endStep();
        REQUIRE(parse(api, in));

        Potassco::TheoryData& t = api.theoryData();
        REQUIRE_FALSE(t.empty());
        REQUIRE(t.numAtoms() == 1);

        const Potassco::TheoryAtom& a = *t.atoms().front();
        REQUIRE(a.atom() == 1);
        REQUIRE(std::strcmp(t.getTerm(a.term()).symbol(), "sum") == 0);
        REQUIRE(a.size() == 4);
        std::vector<std::string> expected = {"1*x(1)", "2*x(2)", "3*x(3)", "4*z"};
        auto                     idx      = 0u;
        for (auto eId : a) {
            CAPTURE(idx);
            const auto& e = t.getElement(eId);
            REQUIRE(e.size() == 1);
            REQUIRE(Literal::fromId(e.condition()) == lit_true);
            const auto& term = t.getTerm(*e.begin());
            REQUIRE(term.isFunction());
            REQUIRE(term.size() == 2);
            const auto& func = t.getTerm(term.function());
            const auto& lhs  = t.getTerm(term.terms()[0]);
            const auto& rhs  = t.getTerm(term.terms()[1]);
            REQUIRE(lhs.type() == Potassco::TheoryTermType::number);
            auto s = std::to_string(lhs.number()).append(func.symbol());
            if (rhs.isFunction()) {
                s.append(t.getTerm(rhs.function()).symbol()).append(1, '(');
                REQUIRE(rhs.size() == 1);
                REQUIRE_NOTHROW(s.append(std::to_string(t.getTerm(*rhs.begin()).number())));
                s.append(1, ')');
            }
            else {
                REQUIRE(rhs.type() == Potassco::TheoryTermType::symbol);
                s.append(rhs.symbol());
            }
            REQUIRE(s == expected.at(idx));
            ++idx;
        }
        REQUIRE(t.getTerm(*a.guard()).symbol() == std::string(">="));
        REQUIRE(t.getTerm(*a.rhs()).number() == 42);
    }

    SECTION("testWriteTheoryAtoms") {
        std::vector<uint32_t> ids;
        AspifOutput           aspif(in.prg);
        aspif.initProgram(true);
        aspif.beginStep();
        aspif.rule(Potassco::HeadType::choice, ids = {1}, {});
        aspif.theoryTerm(0, 1);                // (number 1)
        aspif.theoryTerm(1, "x");              // (string x)
        aspif.theoryTerm(3, "foo");            // (string foo)
        aspif.theoryTerm(2, 1, ids = {0});     // (function x(1))
        aspif.theoryElement(0, ids = {2}, {}); // (element x(1):)
        aspif.theoryAtom(1, 3, ids = {0});     // (&foo { x(1); })
        aspif.endStep();
        std::stringstream step1;
        step1 << in.prg.str();
        aspif.beginStep();
        aspif.rule(Potassco::HeadType::choice, ids = {2}, {});
        aspif.theoryAtom(2, 3, ids = {0}); // (&foo { x(1); })
        aspif.endStep();
        REQUIRE(parse(api, in));
        REQUIRE((api.endProgram() && api.theoryData().numAtoms() == 1));
        std::stringstream out;
        AspParser::write(api, out);
        REQUIRE(findProgram(step1, out));
        ProgramParser& p = api.parser();
        REQUIRE(p.more());
        api.updateProgram();
        REQUIRE(api.theoryData().empty());
        REQUIRE(p.parse());
        REQUIRE((api.endProgram() && api.theoryData().numAtoms() == 1));
        AspParser::write(api, out);
    }
    SECTION("testTheoryElementWithCondition") {
        std::vector<uint32_t> ids;
        AspifOutput           aspif(in.prg);
        aspif.initProgram(false);
        aspif.beginStep();
        aspif.rule(Potassco::HeadType::choice, ids = {1, 2}, {});
        aspif.theoryTerm(0, 1); // (number 1)
        aspif.theoryTerm(1, "foo");
        Potassco::Lit_t lits[2] = {1, -2};
        aspif.theoryElement(0, ids = {0}, lits);
        aspif.theoryAtom(0, 1, ids = {0});
        aspif.endStep();
        REQUIRE(parse(api, in));
        in.prg.clear();
        in.prg.seekg(0);
        Potassco::TheoryData& t = api.theoryData();
        REQUIRE(t.numAtoms() == 1);
        const Potassco::TheoryAtom& a = *t.atoms().front();
        REQUIRE(a.size() == 1);
        const Potassco::TheoryElement& e = t.getElement(*a.begin());
        REQUIRE(e.condition() != 0);
        Potassco::LitVec cond;
        api.extractCondition(e.condition(), cond);
        REQUIRE(cond.size() == 2);
        std::stringstream out;
        REQUIRE(api.endProgram());
        AspParser::write(api, out);
        REQUIRE(findProgram(out, in));
    }
    SECTION("testBasicAdapter") { REQUIRE_THROWS_AS(BasicProgramAdapter(api), std::logic_error); }
}

TEST_CASE("Dimacs parser", "[parser][sat]") {
    SharedContext ctx;
    SatBuilder    api;
    api.startProgram(ctx);
    std::stringstream prg;
    SECTION("testDimacs") {
        prg << "c simple test case\n"
            << "p cnf 4 3\n"
            << "1 2 0\n"
            << "3 4 0\n"
            << "-1 -2 -3 -4 0\n";
        REQUIRE((parse(api, prg) && api.endProgram()));
        REQUIRE(ctx.numVars() == 4);
        REQUIRE(ctx.numConstraints() == 3);
    }

    SECTION("invalid") {
        prg << "c simple test case\n";
        SECTION("missing problem line") {
            prg << "1 2 0\n";
            REQUIRE_THROWS_AS(parse(api, prg), std::runtime_error);
        }
        SECTION("invalid element in clause") {
            prg << "p cnf 4 3\n";
            prg << "-1 2 -x3 0";
            REQUIRE_THROWS_AS(parse(api, prg), std::runtime_error);
        }
        SECTION("invalid character") {
            prg << "p cnf 4 3\n"
                << "1 2 0\n"
                << "3 4 0\n";
            prg << "foo";
            REQUIRE_THROWS_AS(parse(api, prg), std::runtime_error);
        }
        SECTION("duplicate problem line") {
            prg << "p cnf 2 1\n"
                << "1 2 0\n"
                << "p cnf 2 1\n"
                << "2 -1 0\n";
            REQUIRE_THROWS_AS(parse(api, prg), std::runtime_error);
        }
    }

    SECTION("testDimacsDontAddTaut") {
        prg << "c simple test case\n"
            << "p cnf 4 4\n"
            << "1 2 0\n"
            << "3 4 0\n"
            << "-1 -2 -3 -4 0\n"
            << "1 -2 -3 2 0\n";
        REQUIRE((parse(api, prg) && api.endProgram()));
        REQUIRE(ctx.numVars() == 4);
        REQUIRE(ctx.numConstraints() == 3);
    }

    SECTION("testDimacsDontAddDupLit") {
        prg << "c simple test case\n"
            << "p cnf 2 4\n"
            << "1 2 2 1 0\n"
            << "1 2 1 2 0\n"
            << "-1 -2 -1 0\n"
            << "-2 -1 -2 0\n";
        REQUIRE((parse(api, prg) && api.endProgram()));
        REQUIRE(ctx.numVars() == 2);
        REQUIRE(ctx.numConstraints() == 4);
        REQUIRE(ctx.numBinary() == 4);
    }

    SECTION("testDimacsBadVars") {
        prg << "p cnf 1 1\n"
            << "1 2 0\n";
        REQUIRE_THROWS_AS(parse(api, prg), std::runtime_error);
    }

    SECTION("testCnf+") {
        prg << "p cnf+ 7 3\n"
               "1 -2 3 5 -7 <= 3\n"
               "4 5 6 -7    >= 2\n"
               "3 5 7 0\n";
        REQUIRE((parse(api, prg) && api.endProgram()));
        REQUIRE(ctx.numVars() == 7);
        REQUIRE(ctx.output.size() == 7);
        REQUIRE(ctx.numConstraints() == 3);
    }

    SECTION("testCnf+Pb") {
        prg << "p cnf+ 7 3\n"
               "1 -2 3 5 -7 <= 3\n"
               "w 1*4 2*5 1*6 3*-7 >= 2\n"
               "3 5 7 0\n";
        REQUIRE((parse(api, prg) && api.endProgram()));
        REQUIRE(ctx.numVars() == 7);
        REQUIRE(ctx.output.size() == 7);
        REQUIRE(ctx.numConstraints() == 3);
    }

    SECTION("testWcnf") {
        prg << "c comments Weighted Max-SAT\n"
            << "p wcnf 3 5\n"
            << "10 1 -2 0\n"
            << "3 -1 2 -3 0\n"
            << "8 -3 2 0\n"
            << "5 1 3 0\n"
            << "2 3 0\n";
        REQUIRE((parse(api, prg) && api.endProgram()));
        REQUIRE(ctx.numVars() == 7);
        REQUIRE(ctx.output.size() == 3);
        REQUIRE(ctx.numConstraints() == 4);

        SharedMinimizeData* wLits = ctx.minimize();
        REQUIRE(wLits->numRules() == 1);
        REQUIRE(wLits->lits[0].weight == 10);
        REQUIRE(wLits->lits[1].weight == 8);
        REQUIRE(wLits->lits[2].weight == 5);
        REQUIRE(wLits->lits[3].weight == 3);
        REQUIRE(wLits->lits[4].weight == 2);
    }

    SECTION("testPartialWcnf") {
        prg << "c comments Weigthed Partial Max-SAT\n"
            << "p wcnf 4 5 16\n"
            << "16 1 -2 4 0\n"
            << "16 -1 -2 3 0\n"
            << "8 -2 -4 0\n"
            << "4 -3 2 0\n"
            << "1 1 3 0\n";
        REQUIRE((parse(api, prg) && api.endProgram()));
        REQUIRE(ctx.numVars() == 7);
        REQUIRE(ctx.output.size() == 4);
        REQUIRE(ctx.numConstraints() == 5);
        SharedMinimizeData* wLits = ctx.minimize();

        REQUIRE(wLits->numRules() == 1);
        REQUIRE(wLits->lits[0].weight == 8);
        REQUIRE(wLits->lits[1].weight == 4);
        REQUIRE(wLits->lits[2].weight == 1);
    }

    SECTION("testWcnfPlus") {
        prg << "p wcnf+ 7 3 10\n"
               "10 1 -2 3 5 -7 <= 3\n"
               "10 w 1*4 2*5 1*6 3*-7 >= 2\n";
        REQUIRE((parse(api, prg) && api.endProgram()));
        REQUIRE(ctx.numVars() == 7);
        REQUIRE(ctx.output.size() == 7);
        REQUIRE(ctx.numConstraints() == 2);
    }

    SECTION("testKnf") {
        prg << "p knf 4 2\n"
               "1 2 0\n"
               "3 4 0\n"
               "k 2 1 2 3 4 0\n";
        REQUIRE((parse(api, prg) && api.endProgram()));
        REQUIRE(ctx.numVars() == 4);
        REQUIRE(ctx.output.size() == 4);
        REQUIRE(ctx.numConstraints() == 3);
    }

    SECTION("testDimacsExtSupportsGraph") {
        prg << "p cnf 4 3\n"
            << "c graph 2\n"
            << "c node 1 1\n"
            << "c node 2 1\n"
            << "c arc 1 1 2\n"
            << "c arc 2 2 1\n"
            << "c endgraph\n"
            << "1 2 0\n"
            << "3 4 0\n"
            << "-1 -2 -3 -4 0\n";
        REQUIRE((parse(api, prg, ParserOptions().enableAcycEdges()) && api.endProgram() && ctx.endInit()));
        REQUIRE(uint32_t(2) == ctx.stats().acycEdges);
    }
    SECTION("testDimacsExtSupportsCostFunc") {
        prg << "p cnf 4 3\n"
            << "c minweight 1 2 2 4 -3 1 -4 2 0\n"
            << "1 2 0\n"
            << "3 4 0\n"
            << "-1 -2 -3 -4 0\n";
        REQUIRE((parse(api, prg, ParserOptions().enableMinimize()) && api.endProgram()));
        REQUIRE(ctx.hasMinimize());
        SharedMinimizeData* wLits = ctx.minimize();

        REQUIRE(wLits->numRules() == 1);
        REQUIRE(wLits->lits[0] == WeightLiteral{posLit(2), 4});
        REQUIRE(wLits->lits[1] == WeightLiteral{posLit(1), 2});
        REQUIRE(wLits->lits[2] == WeightLiteral{negLit(4), 2});
        REQUIRE(wLits->lits[3] == WeightLiteral{negLit(3), 1});
    }
    SECTION("testDimacsExtSupportsProject") {
        prg << "p cnf 4 3\n"
            << "c project 1 4\n"
            << "1 2 0\n"
            << "3 4 0\n"
            << "-1 -2 -3 -4 0\n";
        REQUIRE((parse(api, prg, ParserOptions().enableProject()) && api.endProgram()));
        REQUIRE(ctx.output.projectMode() == ProjectMode::project);
        auto pr = ctx.output.proj_range();
        REQUIRE(contains(pr, posLit(1)));
        REQUIRE(contains(pr, posLit(4)));
    }
    SECTION("testDimacsExtSupportsHeuristic") {
        prg << "p cnf 4 0\n"
            << "c heuristic 4 1 1 0 0\n"
            << "c heuristic 5 2 1 0 0\n"
            << "c heuristic 5 3 1 0 -1\n";
        REQUIRE((parse(api, prg, ParserOptions().enableHeuristic()) && api.endProgram()));
        REQUIRE(ctx.heuristic.size() == 3);
        auto it = std::ranges::find_if(ctx.heuristic, [](const auto& x) { return x.var() == 3; });
        REQUIRE(it != ctx.heuristic.end());
        REQUIRE(it->bias() == 1);
        REQUIRE(it->prio() == 0);
        REQUIRE(it->type() == Potassco::DomModifier::false_);
        REQUIRE(it->cond() == negLit(1));
    }
    SECTION("testDimacsExtSupportsAssumptions") {
        prg << "p cnf 4 0\n"
            << "c assume 1 -2 3\n";
        REQUIRE((parse(api, prg, ParserOptions().enableAssume()) && api.endProgram()));
        LitVec ass;
        api.getAssumptions(ass);
        REQUIRE(ass.size() == 3);
        REQUIRE(ass[0] == posLit(1));
        REQUIRE(ass[1] == negLit(2));
        REQUIRE(ass[2] == posLit(3));
        REQUIRE(ctx.numVars() == 4);
        REQUIRE(ctx.numEliminatedVars() == 1);
        REQUIRE(ctx.eliminated(4));
        REQUIRE_FALSE(ctx.eliminated(1));
        REQUIRE_FALSE(ctx.eliminated(2));
        REQUIRE_FALSE(ctx.eliminated(3));
        REQUIRE_FALSE(ctx.master()->pref(1).sign());
        REQUIRE(ctx.master()->pref(2).sign());
        REQUIRE(ctx.varInfo(1).frozen());
        REQUIRE(ctx.varInfo(2).frozen());
        REQUIRE(ctx.varInfo(3).frozen());
    }
    SECTION("testDimacsExtSupportsOutputRange") {
        prg << "p cnf 4 0\n"
            << "c output range 2 3\n";
        REQUIRE((parse(api, prg, ParserOptions().enableOutput()) && api.endProgram()));
        REQUIRE(isEq(ctx.output.vars_range(), irange(2u, 4u)));
    }
    SECTION("testDimacsExtSupportsOutputTable") {
        prg << "p cnf 4 0\n"
            << "c output 1  var(1)      \n"
            << "c output -2 not_var(2)  \n"
            << "c 0\n";
        REQUIRE((parse(api, prg, ParserOptions().enableOutput()) && api.endProgram()));
        REQUIRE(ctx.output.vars_range().empty());
        REQUIRE(ctx.output.size() == 2);
        for (const auto& pred : ctx.output.pred_range()) {
            REQUIRE(((pred.name.c_str() == std::string("var(1)") && pred.cond == posLit(1)) ||
                     (pred.name.c_str() == std::string("not_var(2)") && pred.cond == negLit(2))));
        }
    }
    SECTION("testBasicAdapter") {
        NullBuilder sat(ProblemType::sat);
        REQUIRE_THROWS_AS(BasicProgramAdapter(sat), std::logic_error);
        BasicProgramAdapter adapter(api);
        prg << "p cnf 4 1\n";
        REQUIRE(parse(api, prg));
        adapter.rule({}, {}, Potassco::LitSpan{{1, -2, 3, 4}});
        adapter.minimize(0, Potassco::WeightLitSpan{
                                {Potassco::WeightLit{1, 2}, Potassco::WeightLit{-2, 1}, Potassco::WeightLit{-4, 3}}});
        REQUIRE(api.endProgram());
        REQUIRE(ctx.numVars() == 4);
        REQUIRE(ctx.numConstraints() >= 1);
        SharedMinimizeData* wLits = ctx.minimize();
        REQUIRE((wLits && wLits->numRules() == 1));
    }
}

TEST_CASE("Opb parser", "[parser][pb]") {
    SharedContext ctx;
    PBBuilder     api;
    api.startProgram(ctx);
    std::stringstream prg;

    SECTION("testBadVar") {
        prg << "* #variable= 1 #constraint= 1\n+1 x2 >= 1;\n";
        REQUIRE_THROWS_AS(parse(api, prg), std::runtime_error);
    }
    SECTION("testBadVarInGraph") {
        prg << "* #variable= 1 #constraint= 1\n"
            << "* graph 2\n"
            << "* arc 1 1 2\n"
            << "* arc 2 2 1\n"
            << "* endgraph\n";
        REQUIRE_THROWS_AS(parse(api, prg, ParserOptions().enableAcycEdges()), std::runtime_error);
    }
    SECTION("testWBO") {
        prg << "* #variable= 1 #constraint= 2 #soft= 2 mincost= 2 maxcost= 3 sumcost= 5\n"
            << "soft: 6 ;\n"
            << "[2] +1 x1 >= 1 ;\n"
            << "[3] -1 x1 >= 0 ;\n";
        REQUIRE((parse(api, prg) && api.endProgram()));
        REQUIRE(ctx.numVars() == 3);
        REQUIRE((ctx.numConstraints() == 0 || ctx.numConstraints() == 2));
        REQUIRE(ctx.output.size() == 1);
        SumVec bound;
        api.getWeakBounds(bound);
        REQUIRE((bound.size() == 1 && bound[0] == 5));
        SharedMinimizeData* wLits = ctx.minimize();
        REQUIRE((wLits && wLits->numRules() == 1));
        REQUIRE(wLits->adjust(0) == 2);
    }

    SECTION("testNLC") {
        prg << "* #variable= 5 #constraint= 4 #product= 5 sizeproduct= 13\n"
            << "1 x1 +4 x1 ~x2 -2 x5 >=1;\n"
            << "-1 x1 +4 x2 -2 x5 >= 3;\n"
            << "10 x4 +4 x3 >= 10;\n"
            << "2 x2 x3 +3 x4 ~x5 +2 ~x1 x2 +3 ~x1 x2 x3 ~x4 ~x5 >= 1 ;\n";
        REQUIRE((parse(api, prg) && api.endProgram()));
        REQUIRE(ctx.numVars() == 10);
        REQUIRE(ctx.numConstraints() >= 4);
        REQUIRE(ctx.output.size() == 5);
    }

    SECTION("testNLCUnsorted") {
        prg << "* #variable= 4 #constraint= 2 #product= 2 sizeproduct= 8\n"
            << "1 x1 +1 x2 x1 >=1;\n"
            << "1 x1 +1 x2 x3 x4 ~x4 x2 x3 >=1;\n";
        REQUIRE((parse(api, prg) && api.endProgram()));
        REQUIRE(ctx.numVars() == 6);
        REQUIRE(ctx.master()->isTrue(posLit(1)));
        REQUIRE(ctx.master()->isFalse(posLit(6)));
    }

    SECTION("testPBEqualityBug") {
        prg << "* #variable= 4 #constraint= 2\n"
            << "+1 x1 = 1;\n"
            << "+1 x1 +1 x2 +1 x3 +1 x4 = 1;\n";
        REQUIRE((parse(api, prg) && api.endProgram()));
        REQUIRE(ctx.master()->isTrue(posLit(1)));
        REQUIRE(ctx.master()->isFalse(posLit(2)));
        REQUIRE(ctx.master()->isFalse(posLit(3)));
        REQUIRE(ctx.master()->isFalse(posLit(4)));
    }
    SECTION("testPBProject") {
        prg << "* #variable= 6 #constraint= 0\n"
            << "* project x1 x2\n"
            << "* project x4\n";
        REQUIRE((parse(api, prg, ParserOptions().enableProject()) && api.endProgram()));
        REQUIRE(ctx.output.projectMode() == ProjectMode::project);
        REQUIRE(ctx.output.proj_range().size() == 3u);
    }
    SECTION("testPBAssume") {
        prg << "* #variable= 6 #constraint= 0\n"
            << "* assume x1 -x5\n";
        REQUIRE((parse(api, prg, ParserOptions().enableAssume()) && api.endProgram()));
        LitVec ass;
        api.getAssumptions(ass);
        REQUIRE(ass.size() == 2);
        REQUIRE(ass[0] == posLit(1));
        REQUIRE(ass[1] == negLit(5));
        REQUIRE(ctx.varInfo(1).frozen());
        REQUIRE_FALSE(ctx.varInfo(2).frozen());
        REQUIRE(ctx.varInfo(5).frozen());
    }
    SECTION("testPBOutput") {
        prg << "* #variable= 6 #constraint= 0\n"
            << "* output range x2 x4\n";
        REQUIRE((parse(api, prg, ParserOptions().enableOutput()) && api.endProgram()));
        REQUIRE(isEq(ctx.output.vars_range(), irange(2u, 5u)));
    }
    SECTION("testPBOutputTable") {
        prg << "* #variable= 6 #constraint= 0\n"
            << "* output x1 var(1)\n"
            << "* output -x2 not_var(2)\n"
            << "* 0\n";
        REQUIRE((parse(api, prg, ParserOptions().enableOutput()) && api.endProgram()));
        REQUIRE(ctx.output.vars_range().empty());
        REQUIRE(ctx.output.size() == 2);
        for (const auto& pred : ctx.output.pred_range()) {
            REQUIRE(((pred.name.c_str() == std::string("var(1)") && pred.cond == posLit(1)) ||
                     (pred.name.c_str() == std::string("not_var(2)") && pred.cond == negLit(2))));
        }
    }
    SECTION("testBasicAdapter") {
        BasicProgramAdapter adapter(api);
        prg << "* #variable= 4 #constraint= 1\n";
        REQUIRE(parse(api, prg));
        auto ws = Potassco::WLitVec{{1, 2}, {-2, 1}, {-4, 3}};
        SECTION("simple") {
            adapter.rule({}, {}, Potassco::LitSpan{{1, -2, 3, 4}});
            adapter.minimize(0, ws);
            REQUIRE(api.endProgram());
            REQUIRE(ctx.numVars() == 4);
            REQUIRE(ctx.numConstraints() >= 1);
            SharedMinimizeData* wLits = ctx.minimize();
            REQUIRE((wLits && wLits->numRules() == 1));
        }
        SECTION("unsat") {
            adapter.rule({}, {}, 0, ws);
            REQUIRE_FALSE(api.endProgram());
            REQUIRE_FALSE(ctx.ok());
            REQUIRE(ctx.numVars() == 4);
            REQUIRE(ctx.numConstraints() == 0);
        }
    }
    SECTION("testBasicAdapterTypeCheck") {
        NullBuilder pb(ProblemType::pb);
        REQUIRE_THROWS_AS(BasicProgramAdapter(pb), std::logic_error);
    }
}
} // namespace Clasp::Test
