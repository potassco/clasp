//
// Copyright (c) 2006, Benjamin Kaufmann
//
// This file is part of Clasp. See http://www.cs.uni-potsdam.de/clasp/
//
// Clasp is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2 of the License, or
// (at your option) any later version.
//
// Clasp is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with Clasp; if not, write to the Free Software
// Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
//
#include "test.h"
#include "lpcompare.h"
#include <clasp/parser.h>
#include <clasp/minimize_constraint.h>
#include <clasp/solver.h>
#include <potassco/theory_data.h>
#include <potassco/aspif.h>
#include <potassco/smodels.h>
#include <potassco/string_convert.h>
namespace Clasp { namespace Test {

template <class Api>
static bool parse(Api& api, std::istream& str, const ParserOptions& opts = ParserOptions()) {
	ProgramParser& p = api.parser();
	return p.accept(str, opts) && p.parse();
}
VarVec& clear(VarVec& vec) { vec.clear(); return vec; }
static VarVec& operator, (VarVec& vec, int val) {
	vec.push_back(val);
	return vec;
}
static struct Empty {
	template <class T>
	operator Potassco::Span<T> () const { return Potassco::toSpan<T>(); }
} empty;

#define NOT_EMPTY(X,...)
#define SPAN(VEC,...)      NOT_EMPTY(__VA_ARGS__) Potassco::toSpan((clear(VEC) , __VA_ARGS__))

using Potassco::SmodelsOutput;
using Potassco::AspifOutput;
class SmodelsParserTest : public CppUnit::TestFixture {
	CPPUNIT_TEST_SUITE(SmodelsParserTest);
	CPPUNIT_TEST(testEmptySmodels);
	CPPUNIT_TEST(testSingleFact);
	CPPUNIT_TEST(testComputeStatementAssumptions);
	CPPUNIT_TEST(testTransformSimpleConstraintRule);
	CPPUNIT_TEST(testTransformSimpleWeightRule);
	CPPUNIT_TEST(testTransformSimpleChoiceRule);
	CPPUNIT_TEST(testSimpleConstraintRule);
	CPPUNIT_TEST(testSimpleWeightRule);
	CPPUNIT_TEST(testSimpleChoiceRule);
	CPPUNIT_TEST(testMinimizePriority);
	CPPUNIT_TEST(testEdgeDirectives);
	CPPUNIT_TEST(testHeuristicDirectives);
	CPPUNIT_TEST(testSimpleIncremental);
	CPPUNIT_TEST(testIncrementalMinimize);
	CPPUNIT_TEST_SUITE_END();

	std::stringstream prg;
	SharedContext     ctx;
	Asp::LogicProgram api;
public:
	void setUp() {
		api.start(ctx, Asp::LogicProgram::AspOptions().noScc());
	}
	void toSmodels(const char* txt, Var falseAt = 0) {
		prg.clear();
		prg.str("");
		SmodelsOutput sm(prg, true, falseAt);
		Potassco::AspifTextInput x(&sm);
		std::stringstream temp; temp << txt;
		CPPUNIT_ASSERT(Potassco::readProgram(temp, x, 0) == 0);
	}
	bool parseProgram() {
		return parse(api, prg);
	}
	void testEmptySmodels() {
		toSmodels("");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		api.endProgram();
		std::stringstream empty;
		CPPUNIT_ASSERT(compareSmodels(empty, api));
	}
	void testSingleFact() {
		toSmodels("x1.");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		api.endProgram();
		CPPUNIT_ASSERT_EQUAL(0u, ctx.numVars());
	}
	void testComputeStatementAssumptions() {
		toSmodels(
			"x1 :- not x2.\n"
			"x2 :- not x3.\n"
			"x3 :- not x4.\n"
			"x4 :- not x3.\n"
			":- x2.\n", 2);
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		api.endProgram() && ctx.endInit();
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isTrue(api.getLiteral(3)));
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isTrue(api.getLiteral(1)));
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isFalse(api.getLiteral(2)));
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isFalse(api.getLiteral(4)));
	}
	void testTransformSimpleConstraintRule() {
		toSmodels(
			"x1 :- 2{not x3, x2, x4}.\n"
			"x2 :- not x3.\n"
			"x3 :- not x2.\n"
			"x4 :- not x3.\n");
		api.setExtendedRuleMode(Asp::LogicProgram::mode_transform_weight);
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram());
		CPPUNIT_ASSERT(api.getLiteral(2) == api.getLiteral(1));
		CPPUNIT_ASSERT(api.getLiteral(4) == api.getLiteral(1));
		toSmodels(
			"x1 :- not x3.\n"
			"x3 :-not x1.\n"
			"x2 :- x1.\n"
			"x4 :- x1.\n");
		CPPUNIT_ASSERT(compareSmodels(prg, api));
	}
	void testTransformSimpleWeightRule() {
		toSmodels(
			"x1 :- 2 {x2=1, not x3=2, x4=3}.\n"
			"x2 :- not x3.\n"
			"x3 :- not x2.\n"
			"x4 :-not x3.");
		api.setExtendedRuleMode(Asp::LogicProgram::mode_transform_weight);
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram());
		CPPUNIT_ASSERT_EQUAL(1u, ctx.numVars());
		toSmodels(
			"x1 :- not x3.\n"
			"x3 :- not x1.\n"
			"x2 :- x1.\n"
			"x4 :- x1.\n");
		CPPUNIT_ASSERT(compareSmodels(prg, api));
	}
	void testTransformSimpleChoiceRule() {
		toSmodels("{x1;x2;x3} :- x2, not x3.\n"
			"x2 :- not x1.\n"
			"x3 :- not x2.");
		api.setExtendedRuleMode(Asp::LogicProgram::mode_transform_choice);
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram());
		toSmodels("x2. x4.");
		CPPUNIT_ASSERT(compareSmodels(prg, api));
	}
	void testSimpleConstraintRule() {
		toSmodels("x1 :- 2 {x3, x2, x4}.\n"
			"x2 :- not x3.\n"
			"x3 :- not x2.\n"
			"x4 :- not x3.");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram());
		CPPUNIT_ASSERT_EQUAL(2u, ctx.numVars());
		toSmodels("x1 :- 2 {x3, x2 = 2}.\n"
			"x2 :- not x3.\n"
			"x3 :- not x2.\n"
			"x4 :- x2.");
		CPPUNIT_ASSERT(compareSmodels(prg, api));
	}
	void testSimpleWeightRule() {
		toSmodels("x1 :- 2 {x3 = 2, x2 = 1, x4 = 3}. % but (x4 = 3 -> x4 = 2).\n"
			"x2 :- not x3.\n"
			"x3 :- not x2.\n"
			"x4 :- not x3.");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram());
		CPPUNIT_ASSERT_EQUAL(2u, ctx.numVars());
		toSmodels("x1 :- 2 {x3 = 2, x2 = 3}.\n"
			"x2 :- not x3.\n"
			"x3 :- not x2.\n"
			"x4 :- x2.");
		CPPUNIT_ASSERT(compareSmodels(prg, api));
	}
	void testSimpleChoiceRule() {
		toSmodels("{x1;x2;x3} :- x2, not x3.\n"
			"x2 :- not x1.\n"
			"x3 :- not x2.\n");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram());
		toSmodels("x2.");
		CPPUNIT_ASSERT(compareSmodels(prg, api));
	}
	void testMinimizePriority() {
		toSmodels("{x1;x2;x3;x4}.\n"
			"#minimize{not x1, not x2}.\n"
			"#minimize{x3, x4}.");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram());
		SharedMinimizeData* m1 = ctx.minimize();
		CPPUNIT_ASSERT(m1->numRules() == 2);
		CPPUNIT_ASSERT(std::find(m1->lits, m1->lits + 2, WeightLiteral(api.getLiteral(3), 0)) != m1->lits + 2);
		CPPUNIT_ASSERT(std::find(m1->lits, m1->lits + 2, WeightLiteral(api.getLiteral(4), 0)) != m1->lits + 2);
		CPPUNIT_ASSERT(std::find(m1->lits + 2, m1->lits + 4, WeightLiteral(~api.getLiteral(1), 1)) != m1->lits + 4);
		CPPUNIT_ASSERT(std::find(m1->lits + 2, m1->lits + 4, WeightLiteral(~api.getLiteral(2), 1)) != m1->lits + 4);
	}
	void testEdgeDirectives() {
		toSmodels("{x1;x2}.\n"
			"#output _edge(0,1)  : x1.\n"
			"#output _acyc_1_1_0 : x2.");
		CPPUNIT_ASSERT_EQUAL(true, parse(api, prg, ParserOptions().enableAcycEdges()));
		CPPUNIT_ASSERT(api.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(uint32(2), ctx.stats().acycEdges);
	}
	void testHeuristicDirectives() {
		toSmodels("{x1;x2;x3}.\n"
			"#output _heuristic(a,true,1) : x1.\n"
			"#output _heuristic(_heuristic(a,true,1),true,1) : x2.\n"
			"#output a : x3.");
		CPPUNIT_ASSERT_EQUAL(true, parse(api, prg, ParserOptions().enableHeuristic()));
		CPPUNIT_ASSERT(api.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.heuristic.size() == 2);
	}
	void testSimpleIncremental() {
		toSmodels(
			"#incremental.\n"
			"{x1;x2} :-x3.\n"
			"#external x3.\n"
			"#step.\n"
			"#external x3.[release]\n"
			"{x3}.");
		api.updateProgram();
		ProgramParser& p = api.parser();
		CPPUNIT_ASSERT_EQUAL(true, p.accept(prg));
		CPPUNIT_ASSERT_EQUAL(true, p.parse());
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram());
		CPPUNIT_ASSERT(p.more());
		CPPUNIT_ASSERT(api.stats.rules[0].sum() == 1);
		CPPUNIT_ASSERT(api.isExternal(3));
		api.updateProgram();
		CPPUNIT_ASSERT_EQUAL(true, p.parse());
		CPPUNIT_ASSERT(!p.more());
		CPPUNIT_ASSERT(api.stats.rules[0].sum() == 1);
		CPPUNIT_ASSERT(!api.isExternal(3));
	}
	void testIncrementalMinimize() {
		toSmodels(
			"#incremental.\n"
			"{x1; x2}.\n"
			"#minimize{not x1, not x2}.\n"
			"#step."
			"#minimize{x1, x2}.\n");
		api.updateProgram();
		ProgramParser& p = api.parser();
		CPPUNIT_ASSERT_EQUAL(true, p.accept(prg));
		CPPUNIT_ASSERT_EQUAL(true, p.parse());
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram());
		SharedMinimizeData* m1 = ctx.minimize();
		m1->share();
		CPPUNIT_ASSERT(std::find(m1->lits, m1->lits + 2, WeightLiteral(~api.getLiteral(1), 1)) != m1->lits + 2);
		CPPUNIT_ASSERT(std::find(m1->lits, m1->lits + 2, WeightLiteral(~api.getLiteral(2), 1)) != m1->lits + 2);

		CPPUNIT_ASSERT(p.more());
		api.updateProgram();
		CPPUNIT_ASSERT_EQUAL(true, p.parse());
		CPPUNIT_ASSERT(!p.more());
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram());
		SharedMinimizeData* m2 = ctx.minimize();
		CPPUNIT_ASSERT(m1 != m2);
		CPPUNIT_ASSERT(isSentinel(m2->lits[2].first));
		CPPUNIT_ASSERT(std::find(m2->lits, m2->lits + 2, WeightLiteral(api.getLiteral(1), 1)) != m2->lits + 2);
		CPPUNIT_ASSERT(std::find(m2->lits, m2->lits + 2, WeightLiteral(api.getLiteral(2), 1)) != m2->lits + 2);
		m1->release();
	}
};
class ClaspParserTest : public CppUnit::TestFixture {
	CPPUNIT_TEST_SUITE(ClaspParserTest);
	CPPUNIT_TEST(testEmptyProgram);
	CPPUNIT_TEST(testSingleFact);
	CPPUNIT_TEST(testSimpleRule);
	CPPUNIT_TEST(testInvalidAtom);
	CPPUNIT_TEST(testInvalidLiteral);
	CPPUNIT_TEST(testIntegrityConstraint);
	CPPUNIT_TEST(testDisjunctiveRule);
	CPPUNIT_TEST(testChoiceRule);
	CPPUNIT_TEST(testWeightRule);
	CPPUNIT_TEST(testDisjunctiveWeightRule);
	CPPUNIT_TEST(testChoiceWeightRule);
	CPPUNIT_TEST(testInvalidNegativeWeightInWeightRule);
	CPPUNIT_TEST(testInvalidHeadInWeightRule);
	CPPUNIT_TEST(testNegativeBoundInWeightRule);
	CPPUNIT_TEST(testMinimizeRule);
	CPPUNIT_TEST(testMinimizeRuleMergePriority);
	CPPUNIT_TEST(testMinimizeRuleWithNegativeWeights);
	CPPUNIT_TEST(testIncremental);
	CPPUNIT_TEST(testIncrementalExternal);
	CPPUNIT_TEST(testSimpleEdgeDirective);
	CPPUNIT_TEST(testComplexEdgeDirective);
	CPPUNIT_TEST(testHeuristicDirective);
	CPPUNIT_TEST(testOutputDirective);
	CPPUNIT_TEST(testAssumptionDirective);
	CPPUNIT_TEST(testProjectionDirective);
	CPPUNIT_TEST(testEmptyProjectionDirective);
	CPPUNIT_TEST(testIgnoreCommentDirective);
	CPPUNIT_TEST(testReadTheoryAtoms);
	CPPUNIT_TEST(testWriteTheoryAtoms);
	CPPUNIT_TEST(testTheoryElementWithCondition);
	CPPUNIT_TEST_SUITE_END();

	std::stringstream prg;
	SharedContext     ctx;
	Asp::LogicProgram api;
public:
	void setUp() {
		api.start(ctx, Asp::LogicProgram::AspOptions().noScc());
	}
	bool sameProgram(Asp::LogicProgram& a, std::stringstream& prg) {
		std::stringstream out;
		AspParser::write(a, out, AspParser::format_aspif);
		prg.clear();
		prg.seekg(0);
		return compareProgram(prg, out);
	}
	void toAspif(const char* txt) {
		prg.clear();
		prg.str("");
		AspifOutput aspif(prg);
		Potassco::AspifTextInput x(&aspif);
		std::stringstream temp; temp << txt;
		CPPUNIT_ASSERT(Potassco::readProgram(temp, x, 0) == 0);
	}
	bool parseProgram() {
		return parse(api, prg);
	}
	void testEmptyProgram() {
		toAspif("");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram());
		CPPUNIT_ASSERT(api.stats.rules[0].sum() == 0);
	}
	void testSingleFact() {
		toAspif("x1.");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram());
		CPPUNIT_ASSERT(api.stats.rules[0].sum() == 1);
		CPPUNIT_ASSERT(api.getLiteral(1) == lit_true());
	}
	void testSimpleRule() {
		toAspif("x1 :- x3, not x2.");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT(api.stats.rules[0].sum() == 1);
		CPPUNIT_ASSERT(api.numAtoms() == 3);
		CPPUNIT_ASSERT(api.numBodies() == 1);
		CPPUNIT_ASSERT(api.getBody(0)->size() == 2);
		CPPUNIT_ASSERT(api.getBody(0)->goal(0) == posLit(3));
		CPPUNIT_ASSERT(api.getBody(0)->goal(1) == negLit(2));
		CPPUNIT_ASSERT(sameProgram(api, prg));
	}
	void testInvalidAtom() {
		toAspif(POTASSCO_FORMAT("x%u :- not x2, x3.", varMax));
		CPPUNIT_ASSERT_THROW(parseProgram(), std::logic_error);
	}
	void testInvalidLiteral() {
		toAspif(POTASSCO_FORMAT("x1 :- not x%u, x3.", varMax));
		CPPUNIT_ASSERT_THROW(parseProgram(), std::logic_error);
	}
	void testIntegrityConstraint() {
		toAspif(":- not x1, x2.");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT(api.stats.rules[0].sum() == 1);
		CPPUNIT_ASSERT(api.numAtoms() == 2);
		CPPUNIT_ASSERT(api.numBodies() == 1);
		CPPUNIT_ASSERT(api.getBody(0)->size() == 2);
		CPPUNIT_ASSERT(api.getBody(0)->goal(0) == posLit(2));
		CPPUNIT_ASSERT(api.getBody(0)->goal(1) == negLit(1));
		CPPUNIT_ASSERT(api.getBody(0)->value() == value_false);
	}
	void testDisjunctiveRule() {
		toAspif("x1|x2.");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT(api.stats.rules[0].sum() == 1);
		CPPUNIT_ASSERT(api.stats.disjunctions[0] == 1);
		CPPUNIT_ASSERT(api.numAtoms() == 2);
		CPPUNIT_ASSERT(sameProgram(api, prg));
	}
	void testChoiceRule() {
		toAspif("{x1;x2;x3}.");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT(api.stats.rules[0].sum() == 1);
		CPPUNIT_ASSERT(api.stats.rules[0][Asp::RuleStats::Choice] == 1);
		CPPUNIT_ASSERT(api.numAtoms() == 3);
		CPPUNIT_ASSERT(sameProgram(api, prg));
	}
	void testWeightRule() {
		toAspif(
			"x1 :- 2{x2, x3, not x4}.\n"
			"x5 :- 4{x2 = 2, x3, not x4 = 3}.\n");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT(api.stats.rules[0].sum() == 2);
		CPPUNIT_ASSERT(api.stats.bodies[0][Asp::Body_t::Sum] == 1);
		CPPUNIT_ASSERT(api.stats.bodies[0][Asp::Body_t::Count] == 1);
		CPPUNIT_ASSERT(api.numBodies() == 2);
		CPPUNIT_ASSERT(api.getBody(0)->bound() == 2 && !api.getBody(0)->hasWeights());
		CPPUNIT_ASSERT(api.getBody(1)->bound() == 4 && api.getBody(1)->hasWeights());
		CPPUNIT_ASSERT(sameProgram(api, prg));
	}
	void testDisjunctiveWeightRule() {
		toAspif("x1|x2 :- 2{x3, x4, not x5}.");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT(sameProgram(api, prg));
	}
	void testChoiceWeightRule() {
		toAspif("{x1;x2} :- 2{x3, x4, not x5}.");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT(sameProgram(api, prg));
	}
	void testInvalidNegativeWeightInWeightRule() {
		toAspif("x1 :- 2 {x2 = -1, not x3 = 1, x4}.");
		CPPUNIT_ASSERT_THROW(parseProgram(), std::logic_error);
	}
	void testInvalidHeadInWeightRule() {
		prg
			<< "asp 1 0 0"
			<< "\n1 0 1 0 1 2 3 2 1 -3 1 4 1"
			<< "\n0\n";
		CPPUNIT_ASSERT_THROW(parseProgram(), std::logic_error);
	}
	void testNegativeBoundInWeightRule() {
		toAspif("x1 :- -1 {x2, not x3, x4}.");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT(api.stats.rules[0].sum() == 1);
		CPPUNIT_ASSERT(api.stats.bodies[0][Asp::Body_t::Sum] == 0);
	}
	void testMinimizeRule() {
		toAspif(
			"{x1;x2;x3}.\n"
			"#minimize{x1 = 2, x2, not x3 = 4}.");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT(api.stats.rules[0][Asp::RuleStats::Minimize] == 1);
		CPPUNIT_ASSERT(sameProgram(api, prg));
	}
	void testMinimizeRuleMergePriority() {
		toAspif(
			"#minimize{x1 = 2, x2, not x3 = 4}@1.\n"
			"#minimize{x4 = 2, x2 = 2, x3 = 4}@1.");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT(api.stats.rules[0].sum() == 1);
		CPPUNIT_ASSERT(api.stats.rules[0][Asp::RuleStats::Minimize] == 1);
	}
	void testMinimizeRuleWithNegativeWeights() {
		toAspif("#minimize{x4 = -2, x2 = -1, x3 = 4}.");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT(api.stats.rules[0].sum() == 1);
		CPPUNIT_ASSERT(api.endProgram());
		std::stringstream exp("6 0 2 2 4 2 2 1 ");
		CPPUNIT_ASSERT(findSmodels(exp, api));
	}
	void testIncremental() {
		toAspif("#incremental.\n"
			"{x1;x2}.\n"
			"#minimize{x1=2, x2}.\n"
			"#step.\n"
			"{x3}.\n"
			"#minimize{x3=4}.\n");

		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT(api.stats.rules[0].sum() == 2);
		CPPUNIT_ASSERT(api.endProgram());

		ProgramParser& p = api.parser();
		CPPUNIT_ASSERT(p.more());
		api.updateProgram();
		CPPUNIT_ASSERT_EQUAL(true , p.parse());
		CPPUNIT_ASSERT_EQUAL(false, p.more());
		CPPUNIT_ASSERT(api.stats.rules[0].sum() > 0);
		// minimize rule was merged
		CPPUNIT_ASSERT(ctx.minimize()->numRules() == 1);
	}
	void testIncrementalExternal() {
		toAspif("#incremental."
			"x1 :- x2.\n"
			"#external x2. [true]\n"
			"#step.\n"
			"#external x2. [false]\n"
			"#step.\n"
			"#external x2. [release]\n");

		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT(api.endProgram());
		LitVec assume;
		api.getAssumptions(assume);
		CPPUNIT_ASSERT(assume.size() == 1 && assume[0] == api.getLiteral(2));

		ProgramParser& p = api.parser();
		CPPUNIT_ASSERT(p.more());
		api.updateProgram();
		CPPUNIT_ASSERT_EQUAL(true, p.parse());

		CPPUNIT_ASSERT(api.endProgram());
		assume.clear();
		api.getAssumptions(assume);
		CPPUNIT_ASSERT(assume.size() == 1 && assume[0] == ~api.getLiteral(2));

		CPPUNIT_ASSERT(p.more());
		api.updateProgram();
		CPPUNIT_ASSERT_EQUAL(true, p.parse());
		CPPUNIT_ASSERT(!p.more());
		CPPUNIT_ASSERT(api.endProgram());
		assume.clear();
		api.getAssumptions(assume);
		CPPUNIT_ASSERT(assume.empty());
		ctx.endInit();
		CPPUNIT_ASSERT(ctx.master()->isFalse(api.getLiteral(2)));
	}
	void testSimpleEdgeDirective() {
		toAspif("{x1;x2}."
			"#edge (0,1) : x1.\n"
			"#edge (1,0) : x2.\n");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT(api.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.stats().acycEdges == 2);
		CPPUNIT_ASSERT(sameProgram(api, prg));
	}
	void testComplexEdgeDirective() {
		toAspif("{x1;x2;x3;x4}."
			"#edge (0,1) : x1, not x2.\n"
			"#edge (1,0) : x3, not x4.\n");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT(api.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.stats().acycEdges == 2);
		CPPUNIT_ASSERT(sameProgram(api, prg));
	}
	void testHeuristicDirective() {
		toAspif("{x1;x2;x3;x4}."
			"#heuristic x1. [-1@1,sign]\n"
			"#heuristic x1 : x3, not x4. [1@1,factor]");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT(api.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.heuristic.size() == 2);
		CPPUNIT_ASSERT(ctx.heuristic.begin()->type() == DomModType::Sign);
		CPPUNIT_ASSERT((ctx.heuristic.begin() + 1)->type() == DomModType::Factor);
		CPPUNIT_ASSERT(ctx.heuristic.begin()->var() == (ctx.heuristic.begin() + 1)->var());
		CPPUNIT_ASSERT(sameProgram(api, prg));
	}

	void testOutputDirective() {
		toAspif("{x1;x2}."
			"#output fact.\n"
			"#output conj : x1, x2.");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT(api.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.output.size() == 2);
		CPPUNIT_ASSERT(ctx.output.numFacts() == 1);
		CPPUNIT_ASSERT(sameProgram(api, prg));
	}
	void testAssumptionDirective() {
		toAspif("{x1;x2}."
			"#assume{not x2, x1}.");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT(api.endProgram());
		LitVec assume;
		api.getAssumptions(assume);
		CPPUNIT_ASSERT(assume.size() == 2);
		CPPUNIT_ASSERT(std::find(assume.begin(), assume.end(), ~api.getLiteral(2)) != assume.end());
		CPPUNIT_ASSERT(std::find(assume.begin(), assume.end(), api.getLiteral(1)) != assume.end());
		CPPUNIT_ASSERT(sameProgram(api, prg));
	}
	void testProjectionDirective() {
		toAspif("{x1;x2;x3;x4}."
			"#output a : x1.\n"
			"#output b : x2.\n"
			"#output c : x3.\n"
			"#output d : x4.\n"
			"#project{x1, x3}.");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT(api.endProgram());
		CPPUNIT_ASSERT(ctx.output.size() == 4);
		Literal a = api.getLiteral(1);
		Literal b = api.getLiteral(2);
		Literal c = api.getLiteral(3);
		Literal d = api.getLiteral(4);
		OutputTable::lit_iterator proj_begin = ctx.output.proj_begin(), proj_end = ctx.output.proj_end();
		CPPUNIT_ASSERT_EQUAL(true , std::find(proj_begin, proj_end, a) != proj_end);
		CPPUNIT_ASSERT_EQUAL(false, std::find(proj_begin, proj_end, b) != proj_end);
		CPPUNIT_ASSERT_EQUAL(true , std::find(proj_begin, proj_end, c) != proj_end);
		CPPUNIT_ASSERT_EQUAL(false, std::find(proj_begin, proj_end, d) != proj_end);
		CPPUNIT_ASSERT(sameProgram(api, prg));
	}
	void testEmptyProjectionDirective() {
		toAspif("{x1;x2;x3;x4}."
			"#project.");
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT(api.endProgram());
		CPPUNIT_ASSERT(ctx.output.projectMode() == OutputTable::project_explicit);
		CPPUNIT_ASSERT(sameProgram(api, prg));
	}
	void testIgnoreCommentDirective() {
		prg
			<< "asp 1 0 0"
			<< "\n" << Potassco::Directive_t::Comment << " Ignore me!"
			<< "\n0\n";
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
	}
	void testReadTheoryAtoms() {
		AspifOutput aspif(prg);
		aspif.initProgram(false);
		aspif.beginStep();
		aspif.theoryTerm(0, 1);                     // (number 1)
		aspif.theoryTerm(1, 2);                     // (number 2)
		aspif.theoryTerm(2, 3);                     // (number 3)
		aspif.theoryTerm(3, 4);                     // (number 4)
		aspif.theoryTerm(4, Potassco::toSpan("x")); // (string x)
		aspif.theoryTerm(5, Potassco::toSpan("z")); // (string z)
		aspif.theoryTerm(6, Potassco::toSpan("+")); // (string +)
		aspif.theoryTerm(7, Potassco::toSpan("*")); // (string *)
		VarVec ids;
		aspif.theoryTerm(8,  4, SPAN(ids, 0));         // (function x(1))
		aspif.theoryTerm(9,  4, SPAN(ids, 1));         // (function x(2))
		aspif.theoryTerm(10, 4, SPAN(ids, 2));         // (function x(3))
		aspif.theoryTerm(11, 7, SPAN(ids, 0, 8));      // (term 1*x(1))
		aspif.theoryTerm(12, 7, SPAN(ids, 1, 9));      // (term 2*x(2))
		aspif.theoryTerm(13, 7, SPAN(ids, 2, 10));     // (term 3*x(3))
		aspif.theoryTerm(14, 7, SPAN(ids, 3, 5));      // (term 3*x(3))

		aspif.theoryElement(0, SPAN(ids, 11), empty);      // (element 1*x(1):)
		aspif.theoryElement(1, SPAN(ids, 12), empty);      // (element 2*x(2):)
		aspif.theoryElement(2, SPAN(ids, 13), empty);      // (element 3*x(3):)
		aspif.theoryElement(3, SPAN(ids, 14), empty);      // (element 4*z:)
		aspif.theoryTerm(15, Potassco::toSpan("sum"));    // (string sum)
		aspif.theoryTerm(16, Potassco::toSpan(">="));     // (string >=)
		aspif.theoryTerm(17, 42);                         // (number 42)
		aspif.theoryAtom(1, 15, SPAN(ids, 0, 1, 2, 3), 16, 17); // (&sum { 1*x(1); 2*x(2); 3*x(3); 4*z     } >= 42)
		aspif.endStep();
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());

		Potassco::TheoryData& t = api.theoryData();
		CPPUNIT_ASSERT(t.numAtoms() == 1);

		const Potassco::TheoryAtom& a = **t.begin();
		CPPUNIT_ASSERT(a.atom() == 1);
		CPPUNIT_ASSERT(std::strcmp(t.getTerm(a.term()).symbol(), "sum") == 0);
		CPPUNIT_ASSERT(a.size() == 4);
		for (Potassco::TheoryAtom::iterator it = a.begin(), end = a.end(); it != end; ++it) {
			const Potassco::TheoryElement& e = t.getElement(*it);
			CPPUNIT_ASSERT(e.size() == 1);
			CPPUNIT_ASSERT(Literal::fromId(e.condition()) == lit_true());
			CPPUNIT_ASSERT(t.getTerm(*e.begin()).type() == Potassco::Theory_t::Compound);
		}
		CPPUNIT_ASSERT(std::strcmp(t.getTerm(*a.guard()).symbol(), ">=") == 0);
		CPPUNIT_ASSERT(t.getTerm(*a.rhs()).number() == 42);


		struct BuildStr : public Potassco::TheoryAtomStringBuilder {
			virtual Potassco::LitSpan getCondition(Potassco::Id_t) const { return Potassco::toSpan<Potassco::Lit_t>(); }
			virtual std::string       getName(Potassco::Atom_t)    const { return ""; }
		} builder;

		std::string n = builder.toString(t, a);
		CPPUNIT_ASSERT(n == "&sum{1 * x(1); 2 * x(2); 3 * x(3); 4 * z} >= 42");
	}

	void testWriteTheoryAtoms() {
		VarVec ids;
		AspifOutput aspif(prg);
		aspif.initProgram(true);
		aspif.beginStep();
		aspif.rule(Potassco::Head_t::Choice, SPAN(ids, 1), empty);
		aspif.theoryTerm(0, 1);                      // (number 1)
		aspif.theoryTerm(1, Potassco::toSpan("x"));  // (string x)
		aspif.theoryTerm(3, Potassco::toSpan("foo"));// (string foo)
		aspif.theoryTerm(2, 1, SPAN(ids, 0));         // (function x(1))
		aspif.theoryElement(0, SPAN(ids, 2), empty);  // (element x(1):)
		aspif.theoryAtom(1, 3, SPAN(ids, 0));         // (&foo { x(1); })
		aspif.endStep();
		std::stringstream step1;
		step1 << prg.str();
		aspif.beginStep();
		aspif.rule(Potassco::Head_t::Choice, SPAN(ids, 2), empty);
		aspif.theoryAtom(2, 3, SPAN(ids, 0));              // (&foo { x(1); })
		aspif.endStep();
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		CPPUNIT_ASSERT(api.endProgram() && api.theoryData().numAtoms() == 1);
		std::stringstream out;
		AspParser::write(api, out);
		CPPUNIT_ASSERT(findProgram(step1, out));
		ProgramParser& p = api.parser();
		CPPUNIT_ASSERT(p.more());
		api.updateProgram();
		CPPUNIT_ASSERT(api.theoryData().numAtoms() == 0);
		CPPUNIT_ASSERT_EQUAL(true, p.parse());
		CPPUNIT_ASSERT(api.endProgram() && api.theoryData().numAtoms() == 1);
		AspParser::write(api, out);
	}
	void testTheoryElementWithCondition() {
		VarVec ids;
		AspifOutput aspif(prg);
		aspif.initProgram(false);
		aspif.beginStep();
		aspif.rule(Potassco::Head_t::Choice, SPAN(ids, 1, 2), empty);
		aspif.theoryTerm(0, 1); // (number 1)
		aspif.theoryTerm(1, Potassco::toSpan("foo"));
		Potassco::Lit_t lits[2] = {1, -2};
		aspif.theoryElement(0, SPAN(ids, 0), Potassco::toSpan(lits, 2));
		aspif.theoryAtom(0, 1, SPAN(ids, 0));
		aspif.endStep();
		CPPUNIT_ASSERT_EQUAL(true, parseProgram());
		prg.clear();
		prg.seekg(0);
		Potassco::TheoryData& t = api.theoryData();
		CPPUNIT_ASSERT(t.numAtoms() == 1);
		const Potassco::TheoryAtom& a = **t.begin();
		CPPUNIT_ASSERT(a.size() == 1);
		const Potassco::TheoryElement& e = t.getElement(*a.begin());
		CPPUNIT_ASSERT(e.condition() != 0);
		Potassco::LitVec cond;
		api.extractCondition(e.condition(), cond);
		CPPUNIT_ASSERT(cond.size() == 2);
		std::stringstream out;
		CPPUNIT_ASSERT(api.endProgram());
		AspParser::write(api, out);
		CPPUNIT_ASSERT(findProgram(out, prg));
	}
};

class DimacsParserTest : public CppUnit::TestFixture {
  CPPUNIT_TEST_SUITE(DimacsParserTest);
	CPPUNIT_TEST(testDimacs);
	CPPUNIT_TEST(testDimacsDontAddTaut);
	CPPUNIT_TEST(testDimacsDontAddDupLit);
	CPPUNIT_TEST(testDimacsBadVars);

	CPPUNIT_TEST(testWcnf);
	CPPUNIT_TEST(testPartialWcnf);

	CPPUNIT_TEST(testDimacsExtSupportsGraph);
	CPPUNIT_TEST(testDimacsExtSupportsCostFunc);
	CPPUNIT_TEST(testDimacsExtSupportsProject);
	CPPUNIT_TEST(testDimacsExtSupportsHeuristic);
	CPPUNIT_TEST(testDimacsExtSupportsAssumptions);
	CPPUNIT_TEST(testDimacsExtSupportsOutputRange);
	CPPUNIT_TEST(testDimacsExtSupportsOutputTable);
	CPPUNIT_TEST_SUITE_END();

public:
	void setUp() {
		api.startProgram(ctx);
	}
	void testDimacs() {
		std::stringstream prg;
		prg << "c simple test case\n"
		    << "p cnf 4 3\n"
		    << "1 2 0\n"
		    << "3 4 0\n"
		    << "-1 -2 -3 -4 0\n";
		CPPUNIT_ASSERT(parse(api, prg) && api.endProgram());
		CPPUNIT_ASSERT(ctx.numVars() == 4);
		CPPUNIT_ASSERT(ctx.numConstraints() == 3);
	}

	void testDimacsDontAddTaut() {
		std::stringstream prg;
		prg << "c simple test case\n"
		    << "p cnf 4 4\n"
		    << "1 2 0\n"
		    << "3 4 0\n"
		    << "-1 -2 -3 -4 0\n"
		    << "1 -2 -3 2 0\n";
		CPPUNIT_ASSERT(parse(api, prg) && api.endProgram());
		CPPUNIT_ASSERT(ctx.numVars() == 4);
		CPPUNIT_ASSERT(ctx.numConstraints() == 3);
	}

	void testDimacsDontAddDupLit() {
		std::stringstream prg;
		prg << "c simple test case\n"
		    << "p cnf 2 4\n"
		    << "1 2 2 1 0\n"
		    << "1 2 1 2 0\n"
		    << "-1 -2 -1 0\n"
		    << "-2 -1 -2 0\n";
		CPPUNIT_ASSERT(parse(api, prg) && api.endProgram());
		CPPUNIT_ASSERT(ctx.numVars() == 2);
		CPPUNIT_ASSERT(ctx.numConstraints() == 4);
		CPPUNIT_ASSERT(ctx.numBinary() == 4);
	}

	void testDimacsBadVars() {
		std::stringstream prg;
		prg << "p cnf 1 1\n"
		    << "1 2 0\n";
		CPPUNIT_ASSERT_THROW(parse(api, prg), std::logic_error);
	}

	void testWcnf() {
		std::stringstream prg;
		prg << "c comments Weighted Max-SAT\n"
		    << "p wcnf 3 5\n"
		    << "10 1 -2 0\n"
		    << "3 -1 2 -3 0\n"
		    << "8 -3 2 0\n"
		    << "5 1 3 0\n"
		    << "2 3 0\n";
		CPPUNIT_ASSERT(parse(api, prg) && api.endProgram());
		CPPUNIT_ASSERT(ctx.numVars() == 7);
		CPPUNIT_ASSERT(ctx.output.size() == 3);
		CPPUNIT_ASSERT(ctx.numConstraints() == 4);

		SharedMinimizeData* wLits = ctx.minimize();
		CPPUNIT_ASSERT(wLits->numRules() == 1);
		CPPUNIT_ASSERT(wLits->lits[0].second == 10);
		CPPUNIT_ASSERT(wLits->lits[1].second == 8);
		CPPUNIT_ASSERT(wLits->lits[2].second == 5);
		CPPUNIT_ASSERT(wLits->lits[3].second == 3);
	}

	void testPartialWcnf() {
		std::stringstream prg;
		prg << "c comments Weigthed Partial Max-SAT\n"
		    << "p wcnf 4 5 16\n"
		    << "16 1 -2 4 0\n"
		    << "16 -1 -2 3 0\n"
		    << "8 -2 -4 0\n"
		    << "4 -3 2 0\n"
		    << "1 1 3 0\n";
		CPPUNIT_ASSERT(parse(api, prg) && api.endProgram());
		CPPUNIT_ASSERT(ctx.numVars() == 7);
		CPPUNIT_ASSERT(ctx.output.size() == 4);
		CPPUNIT_ASSERT(ctx.numConstraints() == 5);
		SharedMinimizeData* wLits = ctx.minimize();;
		CPPUNIT_ASSERT(wLits->numRules() == 1);
		CPPUNIT_ASSERT(wLits->lits[0].second == 8);
		CPPUNIT_ASSERT(wLits->lits[1].second == 4);
		CPPUNIT_ASSERT(wLits->lits[2].second == 1);
	}
	void testDimacsExtSupportsGraph() {
		std::stringstream prg;
		prg
			<< "p cnf 4 3\n"
			<< "c graph 2\n"
			<< "c node 1 1\n"
			<< "c node 2 1\n"
			<< "c arc 1 1 2\n"
			<< "c arc 2 2 1\n"
			<< "c endgraph\n"
			<< "1 2 0\n"
			<< "3 4 0\n"
			<< "-1 -2 -3 -4 0\n";
		CPPUNIT_ASSERT(parse(api, prg, ParserOptions().enableAcycEdges()) && api.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(uint32(2), ctx.stats().acycEdges);
	}
	void testDimacsExtSupportsCostFunc() {
		std::stringstream prg;
		prg
			<< "p cnf 4 3\n"
			<< "c minweight 1 2 2 4 -3 1 -4 2 0\n"
			<< "1 2 0\n"
			<< "3 4 0\n"
			<< "-1 -2 -3 -4 0\n";
		CPPUNIT_ASSERT(parse(api, prg, ParserOptions().enableMinimize()) && api.endProgram());
		CPPUNIT_ASSERT(ctx.hasMinimize());
		SharedMinimizeData* wLits = ctx.minimize();;
		CPPUNIT_ASSERT(wLits->numRules() == 1);
		CPPUNIT_ASSERT(wLits->lits[0] == WeightLiteral(posLit(2), 4));
		CPPUNIT_ASSERT(wLits->lits[1] == WeightLiteral(posLit(1), 2));
		CPPUNIT_ASSERT(wLits->lits[2] == WeightLiteral(negLit(4), 2));
		CPPUNIT_ASSERT(wLits->lits[3] == WeightLiteral(negLit(3), 1));
	}
	void testDimacsExtSupportsProject() {
		std::stringstream prg;
		prg
			<< "p cnf 4 3\n"
			<< "c project 1 4\n"
			<< "1 2 0\n"
			<< "3 4 0\n"
			<< "-1 -2 -3 -4 0\n";
		CPPUNIT_ASSERT(parse(api, prg, ParserOptions().enableProject()) && api.endProgram());
		CPPUNIT_ASSERT(ctx.output.projectMode() == OutputTable::project_explicit);
		CPPUNIT_ASSERT(std::find(ctx.output.proj_begin(), ctx.output.proj_end(), posLit(1)) != ctx.output.proj_end());
		CPPUNIT_ASSERT(std::find(ctx.output.proj_begin(), ctx.output.proj_end(), posLit(4)) != ctx.output.proj_end());
	}
	void testDimacsExtSupportsHeuristic() {
		std::stringstream prg;
		prg
			<< "p cnf 4 0\n"
			<< "c heuristic 4 1 1 0 0\n"
			<< "c heuristic 5 2 1 0 0\n"
			<< "c heuristic 5 3 1 0 -1\n";
		CPPUNIT_ASSERT(parse(api, prg, ParserOptions().enableHeuristic()) && api.endProgram());
		CPPUNIT_ASSERT(ctx.heuristic.size() == 3);
		DomainTable::iterator it, end = ctx.heuristic.end();
		for (it = ctx.heuristic.begin(); it != end && it->var() != 3; ++it) { ;  }
		CPPUNIT_ASSERT_MESSAGE("'_heuristic(3,false,1,0) : -1' not found", it != end);
		CPPUNIT_ASSERT(it->bias() == 1);
		CPPUNIT_ASSERT(it->prio() == 0);
		CPPUNIT_ASSERT(it->type() == Potassco::Heuristic_t::False);
		CPPUNIT_ASSERT(it->cond() == negLit(1));
	}
	void testDimacsExtSupportsAssumptions() {
		std::stringstream prg;
		prg
			<< "p cnf 4 0\n"
			<< "c assume 1 -2 3\n";
		CPPUNIT_ASSERT(parse(api, prg, ParserOptions().enableAssume()) && api.endProgram());
		LitVec ass;
		api.getAssumptions(ass);
		CPPUNIT_ASSERT(ass.size() == 3);
		CPPUNIT_ASSERT(ass[0] == posLit(1));
		CPPUNIT_ASSERT(ass[1] == negLit(2));
		CPPUNIT_ASSERT(ass[2] == posLit(3));
	}
	void testDimacsExtSupportsOutputRange() {
		std::stringstream prg;
		prg
			<< "p cnf 4 0\n"
			<< "c output range 2 3\n";
		CPPUNIT_ASSERT(parse(api, prg, ParserOptions().enableOutput()) && api.endProgram());
		CPPUNIT_ASSERT(*ctx.output.vars_begin()   == 2);
		CPPUNIT_ASSERT(*(ctx.output.vars_end()-1) == 3);
	}
	void testDimacsExtSupportsOutputTable() {
		std::stringstream prg;
		prg
			<< "p cnf 4 0\n"
			<< "c output 1  var(1)      \n"
			<< "c output -2 not_var(2)  \n"
			<< "c 0\n";
		CPPUNIT_ASSERT(parse(api, prg, ParserOptions().enableOutput()) && api.endProgram());
		CPPUNIT_ASSERT(ctx.output.vars_begin() == ctx.output.vars_end());
		CPPUNIT_ASSERT(ctx.output.size() == 2);
		for (OutputTable::pred_iterator it = ctx.output.pred_begin(), end = ctx.output.pred_end(); it != end; ++it) {
			CPPUNIT_ASSERT(
				(it->name.c_str() == std::string("var(1)") && it->cond == posLit(1))
				||
				(it->name.c_str() == std::string("not_var(2)") && it->cond == negLit(2))
				);
		}
	}
private:
	SharedContext ctx;
	SatBuilder    api;
};

class OPBParserTest : public CppUnit::TestFixture {
  CPPUNIT_TEST_SUITE(OPBParserTest);
	CPPUNIT_TEST(testBadVar);
	CPPUNIT_TEST(testBadVarInGraph);
	CPPUNIT_TEST(testWBO);
	CPPUNIT_TEST(testNLC);
	CPPUNIT_TEST(testNLCUnsorted);
	CPPUNIT_TEST(testPBEqualityBug);
	CPPUNIT_TEST(testPBProject);
	CPPUNIT_TEST(testPBAssume);
	CPPUNIT_TEST(testPBOutput);
	CPPUNIT_TEST(testPBOutputTable);
	CPPUNIT_TEST_SUITE_END();
public:
	void setUp() {
		api.startProgram(ctx);
	}
	void testBadVar() {
		std::stringstream prg;
		prg << "* #variable= 1 #constraint= 1\n+1 x2 >= 1;\n";
		CPPUNIT_ASSERT_THROW(parse(api, prg), std::logic_error);
	}
	void testBadVarInGraph() {
		std::stringstream prg;
		prg << "* #variable= 1 #constraint= 1\n"
		    << "* graph 2\n"
		    << "* arc 1 1 2\n"
		    << "* arc 2 2 1\n"
		    << "* endgraph\n";
		CPPUNIT_ASSERT_THROW(parse(api, prg, ParserOptions().enableAcycEdges()), std::logic_error);
	}
	void testWBO() {
		std::stringstream prg;
		prg << "* #variable= 1 #constraint= 2 #soft= 2 mincost= 2 maxcost= 3 sumcost= 5\n"
		    << "soft: 6 ;\n"
		    << "[2] +1 x1 >= 1 ;\n"
		    << "[3] -1 x1 >= 0 ;\n";
		CPPUNIT_ASSERT(parse(api, prg) && api.endProgram());
		CPPUNIT_ASSERT(ctx.numVars() == 3);
		CPPUNIT_ASSERT(ctx.numConstraints() == 0 || ctx.numConstraints() == 2);
		CPPUNIT_ASSERT(ctx.output.size() == 1);
		SumVec bound;
		api.getWeakBounds(bound);
		CPPUNIT_ASSERT(bound.size() == 1 && bound[0] == 5);
		SharedMinimizeData* wLits = ctx.minimize();
		CPPUNIT_ASSERT(wLits && wLits->numRules() == 1);
		CPPUNIT_ASSERT(wLits->adjust(0) == 2);
	}

	void testNLC() {
		std::stringstream prg;
		prg << "* #variable= 5 #constraint= 4 #product= 5 sizeproduct= 13\n"
		    << "1 x1 +4 x1 ~x2 -2 x5 >=1;\n"
		    << "-1 x1 +4 x2 -2 x5 >= 3;\n"
		    << "10 x4 +4 x3 >= 10;\n"
		    << "2 x2 x3 +3 x4 ~x5 +2 ~x1 x2 +3 ~x1 x2 x3 ~x4 ~x5 >= 1 ;\n";
		CPPUNIT_ASSERT(parse(api, prg) && api.endProgram());
		CPPUNIT_ASSERT(ctx.numVars() == 10);
		CPPUNIT_ASSERT(ctx.numConstraints() >= 4);
		CPPUNIT_ASSERT(ctx.output.size() == 5);
	}

	void testNLCUnsorted() {
		std::stringstream prg;
		prg << "* #variable= 4 #constraint= 2 #product= 2 sizeproduct= 8\n"
		    << "1 x1 +1 x2 x1 >=1;\n"
		    << "1 x1 +1 x2 x3 x4 ~x4 x2 x3 >=1;\n";
		CPPUNIT_ASSERT(parse(api, prg) && api.endProgram());
		CPPUNIT_ASSERT(ctx.numVars() == 6);
		CPPUNIT_ASSERT(ctx.master()->isTrue(posLit(1)));
		CPPUNIT_ASSERT(ctx.master()->isFalse(posLit(6)));
	}

	void testPBEqualityBug() {
		std::stringstream prg;
		prg << "* #variable= 4 #constraint= 2\n"
		    << "+1 x1 = 1;\n"
		    << "+1 x1 +1 x2 +1 x3 +1 x4 = 1;\n";
		CPPUNIT_ASSERT(parse(api, prg) && api.endProgram());
		CPPUNIT_ASSERT(ctx.master()->isTrue(posLit(1)));
		CPPUNIT_ASSERT(ctx.master()->isFalse(posLit(2)));
		CPPUNIT_ASSERT(ctx.master()->isFalse(posLit(3)));
		CPPUNIT_ASSERT(ctx.master()->isFalse(posLit(4)));
	}
	void testPBProject() {
		std::stringstream prg;
		prg << "* #variable= 6 #constraint= 0\n"
			<< "* project x1 x2\n"
			<< "* project x4\n";
		CPPUNIT_ASSERT(parse(api, prg, ParserOptions().enableProject()) && api.endProgram());
		CPPUNIT_ASSERT(ctx.output.projectMode() == OutputTable::project_explicit);
		CPPUNIT_ASSERT(std::distance(ctx.output.proj_begin(), ctx.output.proj_end()) == 3u);
	}
	void testPBAssume() {
		std::stringstream prg;
		prg << "* #variable= 6 #constraint= 0\n"
			  << "* assume x1 -x5\n";
		CPPUNIT_ASSERT(parse(api, prg, ParserOptions().enableAssume()) && api.endProgram());
		LitVec ass;
		api.getAssumptions(ass);
		CPPUNIT_ASSERT(ass.size() == 2);
		CPPUNIT_ASSERT(ass[0] == posLit(1));
		CPPUNIT_ASSERT(ass[1] == negLit(5));
	}
	void testPBOutput() {
		std::stringstream prg;
		prg << "* #variable= 6 #constraint= 0\n"
			<< "* output range x2 x4\n";
		CPPUNIT_ASSERT(parse(api, prg, ParserOptions().enableOutput()) && api.endProgram());
		CPPUNIT_ASSERT(*ctx.output.vars_begin()  == 2);
		CPPUNIT_ASSERT(*(ctx.output.vars_end()-1)== 4);
	}
	void testPBOutputTable() {
		std::stringstream prg;
		prg << "* #variable= 6 #constraint= 0\n"
		  << "* output x1 var(1)\n"
		  << "* output -x2 not_var(2)\n"
		  << "* 0\n";
		CPPUNIT_ASSERT(parse(api, prg, ParserOptions().enableOutput()) && api.endProgram());
		CPPUNIT_ASSERT(ctx.output.vars_begin() == ctx.output.vars_end());
		CPPUNIT_ASSERT(ctx.output.size() == 2);
		for (OutputTable::pred_iterator it = ctx.output.pred_begin(), end = ctx.output.pred_end(); it != end; ++it) {
			CPPUNIT_ASSERT(
				(it->name.c_str() == std::string("var(1)") && it->cond == posLit(1))
				||
				(it->name.c_str() == std::string("not_var(2)") && it->cond == negLit(2))
				);
		}
	}
private:
	SharedContext ctx;
	PBBuilder     api;
};

CPPUNIT_TEST_SUITE_REGISTRATION(SmodelsParserTest);
CPPUNIT_TEST_SUITE_REGISTRATION(ClaspParserTest);
CPPUNIT_TEST_SUITE_REGISTRATION(DimacsParserTest);
CPPUNIT_TEST_SUITE_REGISTRATION(OPBParserTest);

} }
