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
#include <sstream>
#include <clasp/parser.h>
#include <clasp/logic_program.h>
#include <clasp/minimize_constraint.h>
#include <clasp/solver.h>
namespace Clasp { namespace Test {

class LparseParserTest : public CppUnit::TestFixture {

  CPPUNIT_TEST_SUITE(LparseParserTest);
	CPPUNIT_TEST(testEmptyLparse);
	CPPUNIT_TEST(testSingleFact);
	CPPUNIT_TEST(testComputeStatementAssumptions);
	CPPUNIT_TEST(testTransformSimpleConstraintRule);
	CPPUNIT_TEST(testTransformSimpleWeightRule);
	CPPUNIT_TEST(testTransformSimpleChoiceRule);
	CPPUNIT_TEST(testSimpleConstraintRule);
	CPPUNIT_TEST(testSimpleWeightRule);
	CPPUNIT_TEST(testSimpleChoiceRule);
	CPPUNIT_TEST_SUITE_END();

public:
	void setUp() {
		api.start(ctx, Asp::LogicProgram::AspOptions().noScc());
	}
	void testEmptyLparse() {
		std::stringstream empty("0\n0\nB+\n0\nB-\n0\n1\n");
		CPPUNIT_ASSERT_EQUAL(true, Input_t::parseLparse(empty, api));
		empty.clear();
		std::stringstream out;
		api.endProgram();
		api.write(out);
		CPPUNIT_ASSERT_EQUAL(empty.str(), out.str());
	}
	
	void testSingleFact() {
		std::stringstream prg("1 1 0 0 \n0\n1 a\n0\nB+\n0\nB-\n0\n1\n");
		CPPUNIT_ASSERT_EQUAL(true, Input_t::parseLparse(prg, api));
		api.endProgram();
		CPPUNIT_ASSERT_EQUAL(0u, ctx.numVars());
		CPPUNIT_ASSERT_EQUAL('a', ctx.symbolTable()[1].name[0]);
	}
	void testComputeStatementAssumptions() {
		std::stringstream prg;
		prg << "1 1 1 1 2 \n" // d:-not c.
		    << "1 2 1 1 3 \n" // c:-not a.
		    << "1 3 1 1 4 \n" // a:-not b.
		    << "1 4 1 1 3 \n" // b:-not a.
		    << "0\n1 d\n2 c\n3 a\n4 b\n"
		    << "0\nB+\n0\nB-\n2\n0\n1\n"; // B-: c
		
		CPPUNIT_ASSERT_EQUAL(true, Input_t::parseLparse(prg, api));
		api.endProgram() && ctx.endInit();
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isTrue(ctx.symbolTable()[3].lit));
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isTrue(ctx.symbolTable()[1].lit));
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isFalse(ctx.symbolTable()[2].lit));
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isFalse(ctx.symbolTable()[4].lit));
	}

	
	void testTransformSimpleConstraintRule() {
		std::stringstream prg;
		prg << "2 1 3 1 2 3 2 4 \n"// a :- 2 {not c, b, d}
		    << "1 2 1 1 3 \n"      // b :- not c.
		    << "1 3 1 1 2 \n"      // c :- not b.
		    << "1 4 1 1 3 \n"      // d :- not c.
		    << "0\n1 a\n2 b\n3 c\n4 d\n"
		    << "0\nB+\n0\nB-\n0\n1\n";

		std::stringstream exp, out;
		api.setExtendedRuleMode(Asp::LogicProgram::mode_transform_weight);
		CPPUNIT_ASSERT_EQUAL(true, Input_t::parseLparse(prg, api));
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram());
		CPPUNIT_ASSERT(ctx.symbolTable()[2].lit == ctx.symbolTable()[1].lit);
		CPPUNIT_ASSERT(ctx.symbolTable()[4].lit == ctx.symbolTable()[1].lit);
		exp << "1 1 1 1 3 \n" // a :- not c.
		    << "1 3 1 1 1 \n" // c :- not b.
		    << "1 2 1 0 1 \n" // b :- a.
		    << "1 4 1 0 1 \n" // d :- a.
		    << "0\n1 a\n2 b\n3 c\n4 d\n0\n"
		    << "B+\n0\nB-\n0\n1\n"
		;
		api.write(out);
		CPPUNIT_ASSERT_EQUAL(exp.str(), out.str());
	}

	void testTransformSimpleWeightRule() {
		std::stringstream prg;
		prg << "5 1 2 3 1 3 2 4 2 1 3\n"// a :- 2 [b=1, not c=2, d=3]
		    << "1 2 1 1 3 \n" // b :- not c.
		    << "1 3 1 1 2 \n" // c :- not b.
		    << "1 4 1 1 3 \n" // d :- not c.
		    << "0\n1 a\n2 b\n3 c\n4 d\n"
		    << "0\nB+\n0\nB-\n0\n1\n";
		api.setExtendedRuleMode(Asp::LogicProgram::mode_transform_weight);
		CPPUNIT_ASSERT_EQUAL(true, Input_t::parseLparse(prg, api));
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram());
		CPPUNIT_ASSERT_EQUAL(1u, ctx.numVars());
		
		std::stringstream exp, out;
		exp << "1 1 1 1 3 \n" // a :- not c.
		    << "1 3 1 1 1 \n" // c :- not a.
		    << "1 2 1 0 1 \n" // b :- a.
		    << "1 4 1 0 1 \n" // d :- a.
		    << "0\n1 a\n2 b\n3 c\n4 d\n0\n"
		    << "B+\n0\nB-\n0\n1\n"
		;
		api.write(out);
		CPPUNIT_ASSERT_EQUAL(exp.str(), out.str());		
	}

	void testTransformSimpleChoiceRule() {
		std::stringstream prg;
		prg << "3 3 1 2 3 2 1 3 2 \n"// {a,b,c} :- b, not c.
		    << "1 2 1 1 1 \n" // b :- not a.
		    << "1 3 1 1 2 \n" // c :- not b.
		    << "0\n1 a\n2 b\n3 c\n"
		    << "0\nB+\n0\nB-\n0\n1\n";
		api.setExtendedRuleMode(Asp::LogicProgram::mode_transform_choice);
		CPPUNIT_ASSERT_EQUAL(true, Input_t::parseLparse(prg, api));
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram());
		std::stringstream exp, out;
		exp << "1 2 0 0 \n"   // b.
		    << "1 4 1 0 2 \n" // _a :- b
		    << "0\n2 b\n0\n"
		    << "B+\n2\n0\nB-\n0\n1\n"
		;
		api.write(out);
		CPPUNIT_ASSERT_EQUAL(exp.str(), out.str());		
	}

	void testSimpleConstraintRule() {
		std::stringstream prg;
		prg << "2 1 3 0 2 3 2 4 \n"// a :- 2 {c, b, d}
		    << "1 2 1 1 3 \n" // b :- not c.
		    << "1 3 1 1 2 \n" // c :- not b.
		    << "1 4 1 1 3 \n" // d :- not c.
		    << "0\n1 a\n2 b\n3 c\n4 d\n"
		    << "0\nB+\n0\nB-\n0\n1\n";

		std::stringstream exp, out;
		api.setExtendedRuleMode(Asp::LogicProgram::mode_transform_choice);
		CPPUNIT_ASSERT_EQUAL(true, Input_t::parseLparse(prg, api));
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram());
		CPPUNIT_ASSERT_EQUAL(2u, ctx.numVars());
		
		exp << "5 1 2 2 0 3 2 1 2 \n"// a :- 2 [c = 1, b = 2]
		    << "1 2 1 1 3 \n" // b :- not c.
		    << "1 3 1 1 2 \n" // c :- not b.
		    << "1 4 1 0 2 \n" // d :- b.
		    << "0\n1 a\n2 b\n3 c\n4 d\n0\n"
		    << "B+\n0\nB-\n0\n1\n"
		;
		api.write(out);
		CPPUNIT_ASSERT_EQUAL(exp.str(), out.str());
	}

	void testSimpleWeightRule() {
		std::stringstream prg;
		prg << "5 1 2 3 0 3 2 4 2 1 3\n"// a :- 2 [c = 2, b = 1, d = 3], but (d = 3 -> d = 2)
		    << "1 2 1 1 3 \n" // b :- not c.
		    << "1 3 1 1 2 \n" // c :- not b.
		    << "1 4 1 1 3 \n" // d :- not c.
		    << "0\n1 a\n2 b\n3 c\n4 d\n"
		    << "0\nB+\n0\nB-\n0\n1\n";

		std::stringstream exp, out;
		api.setExtendedRuleMode(Asp::LogicProgram::mode_transform_choice);
		CPPUNIT_ASSERT_EQUAL(true, Input_t::parseLparse(prg, api));
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram());
		CPPUNIT_ASSERT_EQUAL(2u, ctx.numVars());
		
		exp << "5 1 2 2 0 3 2 2 3 \n"// a :- 2 [c = 2, b = 3]
		    << "1 2 1 1 3 \n" // b :- not c.
		    << "1 3 1 1 2 \n" // c :- not b.
		    << "1 4 1 0 2 \n" // d :- b.
		    << "0\n1 a\n2 b\n3 c\n4 d\n0\n"
		    << "B+\n0\nB-\n0\n1\n"
		;
		api.write(out);
		CPPUNIT_ASSERT_EQUAL(exp.str(), out.str());
	}

	void testSimpleChoiceRule() {
		std::stringstream prg;
		prg << "3 3 1 2 3 2 1 3 2 \n"// {a,b,c} :- b, not c.
		    << "1 2 1 1 1 \n" // b :- not a.
		    << "1 3 1 1 2 \n" // c :- not b.
		    << "0\n1 a\n2 b\n3 c\n"
		    << "0\nB+\n0\nB-\n0\n1\n";
		
		api.setExtendedRuleMode(Asp::LogicProgram::mode_transform_weight);
		CPPUNIT_ASSERT_EQUAL(true, Input_t::parseLparse(prg, api));
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram());
		std::stringstream exp, out;
		prg.clear();
		prg.seekg(0);
		exp << "1 2 0 0 \n"// b.
		    << "0\n2 b\n"
		    << "0\n"
		    << "B+\n2\n0\nB-\n0\n1\n";
		api.write(out);
		CPPUNIT_ASSERT_EQUAL(exp.str(), out.str());		
	}
private:
	SharedContext     ctx;
	Asp::LogicProgram api;
};

class DimacsParserTest : public CppUnit::TestFixture {

  CPPUNIT_TEST_SUITE(DimacsParserTest);
	CPPUNIT_TEST(testDimacs);
	CPPUNIT_TEST(testDimacsDontAddTaut);
	CPPUNIT_TEST(testDimacsDontAddDupLit);
	CPPUNIT_TEST(testDimacsBadVars);

	CPPUNIT_TEST(testWcnf);
	CPPUNIT_TEST(testPartialWcnf);
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
		CPPUNIT_ASSERT(Input_t::parseDimacs(prg, api) && api.endProgram());
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
		CPPUNIT_ASSERT(Input_t::parseDimacs(prg, api) && api.endProgram());
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
		CPPUNIT_ASSERT(Input_t::parseDimacs(prg, api) && api.endProgram());
		CPPUNIT_ASSERT(ctx.numVars() == 2);
		CPPUNIT_ASSERT(ctx.numConstraints() == 4);
		CPPUNIT_ASSERT(ctx.numBinary() == 4);
	}

	void testDimacsBadVars() {
		std::stringstream prg;
		prg << "p cnf 2 1\n"
		    << "3 4 0\n";
		CPPUNIT_ASSERT_THROW(Input_t::parseDimacs(prg, api), ParseError);
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
		CPPUNIT_ASSERT(Input_t::parseDimacs(prg, api) && api.endProgram());
		CPPUNIT_ASSERT(ctx.numVars() == 7);
		CPPUNIT_ASSERT(ctx.symbolTable().size() == 4);
		CPPUNIT_ASSERT(ctx.numConstraints() == 4);

		SharedMinimizeData* wLits = api.getMinimizeConstraint();
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
		CPPUNIT_ASSERT(Input_t::parseDimacs(prg, api) && api.endProgram());
		CPPUNIT_ASSERT(ctx.numVars() == 7);
		CPPUNIT_ASSERT(ctx.symbolTable().size() == 5);
		CPPUNIT_ASSERT(ctx.numConstraints() == 5);
		SharedMinimizeData* wLits = api.getMinimizeConstraint();
		CPPUNIT_ASSERT(wLits->numRules() == 1);
		CPPUNIT_ASSERT(wLits->lits[0].second == 8);
		CPPUNIT_ASSERT(wLits->lits[1].second == 4);
		CPPUNIT_ASSERT(wLits->lits[2].second == 1);
	}
private:
	SharedContext ctx;
	SatBuilder    api;
};

class OPBParserTest : public CppUnit::TestFixture {

  CPPUNIT_TEST_SUITE(OPBParserTest);
	CPPUNIT_TEST(testWBO);
	CPPUNIT_TEST(testNLC);
	CPPUNIT_TEST(testNLCUnsorted);
	CPPUNIT_TEST(testPBEqualityBug);
	CPPUNIT_TEST_SUITE_END();

public:
	void setUp() {
		api.startProgram(ctx);
	}
	void testWBO() {
		std::stringstream prg;
		prg << "* #variable= 1 #constraint= 2 #soft= 2 mincost= 2 maxcost= 3 sumcost= 5\n"
		    << "soft: 6 ;\n"
		    << "[2] +1 x1 >= 1 ;\n"
		    << "[3] -1 x1 >= 0 ;\n";
		CPPUNIT_ASSERT(Input_t::parseOPB(prg, api) && api.endProgram());
		CPPUNIT_ASSERT(ctx.numVars() == 3);
		CPPUNIT_ASSERT(ctx.numConstraints() == 0 || ctx.numConstraints() == 2);
		CPPUNIT_ASSERT(ctx.symbolTable().size() == 2);
		SumVec bound;
		SharedMinimizeData* wLits = api.getMinimizeConstraint(&bound);
		CPPUNIT_ASSERT(wLits && wLits->numRules() == 1);
		CPPUNIT_ASSERT(wLits->adjust(0) == 2);
		CPPUNIT_ASSERT(bound.size() == 1 && bound[0] == 5);
	}

	void testNLC() {
		std::stringstream prg;
		prg << "* #variable= 5 #constraint= 4 #product= 5 sizeproduct= 13\n"
		    << "1 x1 +4 x1 ~x2 -2 x5 >=1;\n"
		    << "-1 x1 +4 x2 -2 x5 >= 3;\n"
		    << "10 x4 +4 x3 >= 10;\n"
		    << "2 x2 x3 +3 x4 ~x5 +2 ~x1 x2 +3 ~x1 x2 x3 ~x4 ~x5 >= 1 ;\n";
		CPPUNIT_ASSERT(Input_t::parseOPB(prg, api) && api.endProgram());
		CPPUNIT_ASSERT(ctx.numVars() == 10);
		CPPUNIT_ASSERT(ctx.numConstraints() >= 4);
		CPPUNIT_ASSERT(ctx.symbolTable().size() == 6);
	}

	void testNLCUnsorted() {
		std::stringstream prg;
		prg << "* #variable= 4 #constraint= 2 #product= 2 sizeproduct= 8\n"
		    << "1 x1 +1 x2 x1 >=1;\n"
		    << "1 x1 +1 x2 x3 x4 ~x4 x2 x3 >=1;\n";
		CPPUNIT_ASSERT(Input_t::parseOPB(prg, api) && api.endProgram());
		CPPUNIT_ASSERT(ctx.numVars() == 6);
		CPPUNIT_ASSERT(ctx.master()->isTrue(posLit(1)));
		CPPUNIT_ASSERT(ctx.master()->isFalse(posLit(6)));
	}

	void testPBEqualityBug() {
		std::stringstream prg;
		prg << "* #variable= 4 #constraint= 2\n"
		    << "+1 x1 = 1;\n"
		    << "+1 x1 +1 x2 +1 x3 +1 x4 = 1;\n";
		CPPUNIT_ASSERT(Input_t::parseOPB(prg, api) && api.endProgram());
		CPPUNIT_ASSERT(ctx.master()->isTrue(posLit(1)));
		CPPUNIT_ASSERT(ctx.master()->isFalse(posLit(2)));
		CPPUNIT_ASSERT(ctx.master()->isFalse(posLit(3)));
		CPPUNIT_ASSERT(ctx.master()->isFalse(posLit(4)));
	}
private:
	SharedContext ctx;
	PBBuilder     api;
};

CPPUNIT_TEST_SUITE_REGISTRATION(LparseParserTest);
CPPUNIT_TEST_SUITE_REGISTRATION(DimacsParserTest);
CPPUNIT_TEST_SUITE_REGISTRATION(OPBParserTest);

} } 
