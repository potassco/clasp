//
// Copyright (c) 2012, Benjamin Kaufmann
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
#include <clasp/solver.h>
#include <clasp/logic_program.h>
#include <clasp/unfounded_check.h>
#include <sstream>
using namespace std;
namespace Clasp { namespace Test {
using namespace Clasp::Asp;
class DlpBuilderTest : public CppUnit::TestFixture {
	CPPUNIT_TEST_SUITE(DlpBuilderTest);
	CPPUNIT_TEST(testSimpleChoice);
	CPPUNIT_TEST(testNotAChoice);
	CPPUNIT_TEST(testStillAChoice);
	CPPUNIT_TEST(testSubsumedChoice);
	CPPUNIT_TEST(testSubsumedByChoice);
	CPPUNIT_TEST(testChoiceDisjBug);
	CPPUNIT_TEST(testTautOverOne);
	CPPUNIT_TEST(testSimpleLoop);
	CPPUNIT_TEST(testSimpleLoopNoGamma);
	CPPUNIT_TEST(testComputeTrue);
	CPPUNIT_TEST(testComputeFalse);
	CPPUNIT_TEST(testIncremental);
	CPPUNIT_TEST(testSimplify);
	CPPUNIT_TEST(testSimplifyNoRemove);

	CPPUNIT_TEST(testNoDupGamma);
	CPPUNIT_TEST(testPreNoGamma);
	CPPUNIT_TEST(testPreNoGamma2);
	CPPUNIT_TEST(testRecAgg);
	CPPUNIT_TEST(testPropagateSource);
	CPPUNIT_TEST_SUITE_END();
public:
	void setUp() {
		a = 1, b = 2, c = 3, d = 4, e = 5, f = 6;
	}
	void tearDown(){
		ctx.reset();
	}
	void testSimpleChoice() {
		lpAdd(lp.start(ctx), "a | b.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(lp.stats.disjunctions[0] == 1);
		CPPUNIT_ASSERT(lp.getLiteral(a) != lp.getLiteral(b));
		ctx.master()->assume(lp.getLiteral(a)) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(b)));
		ctx.master()->undoUntil(0);
		ctx.master()->assume(lp.getLiteral(b)) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(a)));
	}
	void testNotAChoice() {
		lpAdd(lp.start(ctx), "a | b. a :- not c.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(lp.stats.disjunctions[0] == 1);
		CPPUNIT_ASSERT(lp.getLiteral(b) == lp.getLiteral(c));
		CPPUNIT_ASSERT(lp.getLiteral(a) == lit_true());
	}

	void testStillAChoice() {
		lpAdd(lp.start(ctx), "a|b. {b}.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(lp.stats.disjunctions[0] == 1);
		CPPUNIT_ASSERT(lp.getLiteral(a) != lp.getLiteral(b));
		ctx.master()->assume(lp.getLiteral(a)) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(b)));
		ctx.master()->undoUntil(0);
		ctx.master()->assume(lp.getLiteral(b)) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(a)));
	}

	void testSubsumedChoice() {
		lpAdd(lp.start(ctx, LogicProgram::AspOptions().iterations(-1)),
			"a | b.\n"
			"a | b | c | d.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(lp.stats.disjunctions[0] == 2);
		CPPUNIT_ASSERT(lp.getLiteral(c) == lit_false() || !(ctx.master()->assume(lp.getLiteral(c)) && ctx.master()->propagate()));
		ctx.master()->undoUntil(0);
		CPPUNIT_ASSERT(lp.getLiteral(d) == lit_false() || !(ctx.master()->assume(lp.getLiteral(d)) && ctx.master()->propagate()));
	}

	void testSubsumedByChoice() {
		lpAdd(lp.start(ctx),
			"a | b.\n"
			"{a,b}.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(lp.stats.disjunctions[0] == 1);
		ctx.master()->assume(~lp.getLiteral(a)) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isTrue(lp.getLiteral(b)));
	}
	void testChoiceDisjBug() {
		lpAdd(lp.start(ctx),
			"a | b.\n"
			"{a,b,b}.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(lp.stats.disjunctions[0] == 1);

		ctx.master()->assume(lp.getLiteral(c)) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->value(lp.getLiteral(a).var()) == value_free);
		CPPUNIT_ASSERT(ctx.master()->value(lp.getLiteral(b).var()) == value_free);
		ctx.master()->assume(~lp.getLiteral(a)) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isTrue(lp.getLiteral(b)));
		ctx.master()->undoUntil(0);
		ctx.master()->assume(lp.getLiteral(a)) && ctx.master()->propagate();
		ctx.master()->assume(lp.getLiteral(b)) && ctx.master()->propagate();
		ctx.master()->assume(lp.getLiteral(c)) && ctx.master()->propagate();
		CPPUNIT_ASSERT(!ctx.master()->hasConflict() && ctx.master()->numFreeVars() == 0);
	}

	void testTautOverOne() {
		lpAdd(lp.start(ctx),
			"{b}.\n"
			"c :- b.\n"
			"a | b :- c.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(lp.stats.disjunctions[0] == 1);

		CPPUNIT_ASSERT(lp.getLiteral(a) == lit_false() && !(ctx.master()->assume(lp.getLiteral(a)) && ctx.master()->propagate()));
	}

	void testSimpleLoop() {
		lpAdd(lp.start(ctx),
			"a | b."
			"a :- b."
			"b :- a.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.sccGraph.get());
		CPPUNIT_ASSERT(lp.stats.disjunctions[0] == 1);
		ctx.master()->addPost(new DefaultUnfoundedCheck(*ctx.sccGraph));
		CPPUNIT_ASSERT_EQUAL(true, ctx.endInit());

		CPPUNIT_ASSERT(lp.getLiteral(a) != lp.getLiteral(b));
		CPPUNIT_ASSERT(ctx.master()->assume(lp.getLiteral(a)) && ctx.master()->propagate());
		CPPUNIT_ASSERT(!ctx.master()->isFalse(lp.getLiteral(b)));
		ctx.master()->undoUntil(0);
		CPPUNIT_ASSERT(ctx.master()->assume(lp.getLiteral(b)) && ctx.master()->propagate());
		CPPUNIT_ASSERT(!ctx.master()->isFalse(lp.getLiteral(a)));
	}

	void testSimpleLoopNoGamma() {
		lpAdd(lp.start(ctx, LogicProgram::AspOptions().disableGamma()),
			"a | b.\n"
			"a :- b.\n"
			"b :- a.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(lp.stats.disjunctions[0] == 1);

		CPPUNIT_ASSERT(!(ctx.master()->assume(~lp.getLiteral(a)) && ctx.master()->propagate()) || ctx.master()->isTrue(lp.getLiteral(b)));
	}
	void testComputeTrue() {
		lpAdd(lp.start(ctx, LogicProgram::AspOptions().noScc()),
			"a | b.\n"
			"a :- b.\n"
			":- not a.\n");
		CPPUNIT_ASSERT(lp.getAtom(a)->value() == value_true);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(lp.stats.disjunctions[0] == 1);

		CPPUNIT_ASSERT(ctx.master()->isTrue(lp.getLiteral(a)));
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(b)));
	}
	void testComputeFalse() {
		lpAdd(lp.start(ctx),
			"a | b | c.\n"
			"a :- c.\n"
			" :- a.");
		CPPUNIT_ASSERT(lp.getAtom(a)->value() == value_false);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(lp.stats.disjunctions[0] == 1);

		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(a)));
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(c)));
		CPPUNIT_ASSERT(ctx.master()->isTrue(lp.getLiteral(b)));
	}
	void testIncremental() {
		lp.start(ctx);
		lp.updateProgram();
		lpAdd(lp,
			"% Step 0:\n"
			"a | b :- c.\n"
			"a :- b.\n"
			"b :- a.\n"
			"#external c.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(lp.stats.disjunctions[0] == 1);
		CPPUNIT_ASSERT(lp.stats.sccs == 1);
		CPPUNIT_ASSERT(lp.stats.nonHcfs == 1);

		lp.update();
		lpAdd(lp,
			"% Step 1:\n"
			"d | e :- a, f.\n"
			"d :- e, b.\n"
			"e :- d, a.\n"
			"#external f.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(lp.stats.disjunctions[0] == 1);
		CPPUNIT_ASSERT(lp.stats.sccs == 1);
		CPPUNIT_ASSERT(lp.stats.nonHcfs == 1);
	}

	void testSimplify() {
		lp.start(ctx);
		lp.updateProgram();
		lpAdd(lp,
			"a | b :- d.\n"
			"a :- b.\n"
			"b :- c.\n"
			"c :- a,e.\n"
			"{d,e}.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(lp.stats.disjunctions[0] == 1);
		CPPUNIT_ASSERT(lp.stats.sccs == 1);
		CPPUNIT_ASSERT(lp.stats.nonHcfs == 1);
		DG& graph = *ctx.sccGraph;
		CPPUNIT_ASSERT(graph.numNonHcfs() == 1);
		ctx.addUnary(~lp.getLiteral(a));
		ctx.master()->propagate();
		graph.simplify(*ctx.master());
		CPPUNIT_ASSERT(graph.numNonHcfs() == 0);
	}
	void testSimplifyNoRemove() {
		ctx.setConcurrency(2);
		lp.start(ctx);
		lp.updateProgram();
		lpAdd(lp,
			"a | b :- d.\n"
			"a :- b.\n"
			"b :- c.\n"
			"c :- a,e.\n"
			"{d,e}.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		Solver& s2= ctx.pushSolver();
		CPPUNIT_ASSERT(ctx.endInit(true));
		DG& graph = *ctx.sccGraph;
		CPPUNIT_ASSERT(graph.numNonHcfs() == 1);
		Literal u = ~lp.getLiteral(a);
		ctx.master()->add(ClauseRep::create(&u, 1, Constraint_t::Conflict));
		ctx.master()->simplify() && s2.simplify();
		graph.simplify(*ctx.master());
		graph.simplify(s2);
		CPPUNIT_ASSERT(graph.numNonHcfs() == 1);
		const DG::NonHcfComponent* c = *graph.nonHcfBegin();

		LitVec temp;
		VarVec ufs;
		c->assumptionsFromAssignment(*ctx.master(), temp);
		CPPUNIT_ASSERT_EQUAL(true, c->test(*ctx.master(), temp, ufs) && ufs.empty());

		temp.clear();
		c->assumptionsFromAssignment(s2, temp);
		CPPUNIT_ASSERT_EQUAL(true, c->test(s2, temp, ufs) && ufs.empty());
	}
	void testNoDupGamma() {
		lpAdd(lp.start(ctx),
			"a | b.\n"
			"a :- b.\n"
			"b :- a.\n"
			"a :- not b.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(lp.numBodies() == 5); // + b :- not a.
		CPPUNIT_ASSERT(lp.stats.gammas == 1);
		std::stringstream exp("1 1 1 1 2\n1 1 1 1 2");
		CPPUNIT_ASSERT_EQUAL(false, findSmodels(exp, lp));
	}
	void testPreNoGamma() {
		lpAdd(lp.start(ctx),
			"a | b.\n"
			"a :- b.\n"
			"b :- a.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		std::stringstream exp("1 1 1 1 2");
		CPPUNIT_ASSERT_EQUAL(false, findSmodels(exp, lp));
	}
	void testPreNoGamma2() {
		lpAdd(lp.start(ctx, LogicProgram::AspOptions().disableGamma()),
			"a | b.\n"
			"a :- b.\n"
			"b :- a.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		std::stringstream exp("3 2 1 2 0 0");
		CPPUNIT_ASSERT_EQUAL(false, findSmodels(exp, lp));
	}
	void testRecAgg() {
		lpAdd(lp.start(ctx),
			"{c}.\n"
			"a | b.\n"
			"a :- 1 {c, b}.\n"
			"b :- 1 {c, a}.");
		CPPUNIT_ASSERT(lp.stats.disjunctions[0] == 1);
		CPPUNIT_ASSERT(lp.stats.bodies[0][Body_t::Count] == 2);
		std::stringstream exp("2 2 2 0 1 3 1");
		CPPUNIT_ASSERT_EQUAL(true, findSmodels(exp, lp));
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		exp.clear(); exp.seekg(0);
		std::stringstream str;
		AspParser::write(lp, str, AspParser::format_smodels);
		CPPUNIT_ASSERT_EQUAL(false, findProgram(exp, str));
		exp.clear();  exp.str("");
		str.clear(); str.seekg(0);
		exp << "1 1 1 0 3\n" << "1 2 1 0 3\n";
		CPPUNIT_ASSERT_EQUAL(true, findProgram(exp, str));
	}
	void testPropagateSource() {
		lpAdd(lp.start(ctx),
			"d; c.\n"
			"b; a:-c.\n"
			"b; a.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(lp.getLiteral(a) != lp.getLiteral(b));
		CPPUNIT_ASSERT(lp.getLiteral(b) != lp.getLiteral(c));
		CPPUNIT_ASSERT(lp.getLiteral(c) != lp.getLiteral(d));
	}
private:
	typedef Asp::PrgDepGraph DG;
	SharedContext ctx;
	LogicProgram  lp;
	Var           a, b, c, d, e, f;
};
CPPUNIT_TEST_SUITE_REGISTRATION(DlpBuilderTest);
 } }

