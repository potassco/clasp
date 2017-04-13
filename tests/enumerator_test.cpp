//
// Copyright (c) 2006-2017 Benjamin Kaufmann
//
// This file is part of Clasp. See http://www.cs.uni-potsdam.de/clasp/
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
#include "test.h"
#include "lpcompare.h"
#include <clasp/solver.h>
#include <clasp/program_builder.h>
#include <clasp/unfounded_check.h>
#include <clasp/minimize_constraint.h>
#include <clasp/model_enumerators.h>
#include <sstream>
using namespace std;
namespace Clasp { namespace Test {
using namespace Clasp::Asp;
class EnumeratorTest : public CppUnit::TestFixture {
  CPPUNIT_TEST_SUITE(EnumeratorTest);
	CPPUNIT_TEST(testProjectToOutput);
	CPPUNIT_TEST(testProjectExplicit);

	CPPUNIT_TEST(testMiniProject);
	CPPUNIT_TEST(testProjectBug);
	CPPUNIT_TEST(testProjectRestart);
	CPPUNIT_TEST(testProjectWithBacktracking);
	CPPUNIT_TEST(testTerminateRemovesWatches);
	CPPUNIT_TEST(testParallelRecord);
	CPPUNIT_TEST(testParallelUpdate);
	CPPUNIT_TEST(testTagLiteral);
	CPPUNIT_TEST(testIgnoreTagLiteralInPath);
	CPPUNIT_TEST(testSplittable);
	CPPUNIT_TEST(testLearnStepLiteral);
	CPPUNIT_TEST(testAssignStepLiteral);
	CPPUNIT_TEST(testModelHeuristicIsUsed);
	CPPUNIT_TEST(testDomCombineDef);
	CPPUNIT_TEST(testDomRecComplementShow);
	CPPUNIT_TEST(testDomRecComplementAll);
	CPPUNIT_TEST(testDomRecAssume);
	CPPUNIT_TEST(testNotAttached);
	CPPUNIT_TEST_SUITE_END();
public:
	void testProjectToOutput() {
		SharedContext ctx;
		Var v1 = ctx.addVar(Var_t::Atom);
		Var v2 = ctx.addVar(Var_t::Atom);
		Var v3 = ctx.addVar(Var_t::Atom);
		ctx.output.add("a", posLit(v1));
		ctx.output.add("_aux", posLit(v2));
		ctx.output.add("b", posLit(v3));
		ctx.startAddConstraints();
		ModelEnumerator e;
		e.setStrategy(ModelEnumerator::strategy_backtrack, ModelEnumerator::project_enable_simple, '_');
		e.init(ctx);
		ctx.endInit();
		CPPUNIT_ASSERT(ctx.output.projectMode() == OutputTable::project_output);
		CPPUNIT_ASSERT(e.project(v1));
		CPPUNIT_ASSERT(e.project(v3));

		ctx.detach(0);
	}
	void testProjectExplicit() {
		SharedContext ctx;
		Var v1 = ctx.addVar(Var_t::Atom);
		Var v2 = ctx.addVar(Var_t::Atom);
		Var v3 = ctx.addVar(Var_t::Atom);
		ctx.output.add("a", posLit(v1));
		ctx.output.add("_aux", posLit(v2));
		ctx.output.add("b", posLit(v3));
		ctx.output.addProject(posLit(v2));
		ctx.output.addProject(posLit(v3));
		CPPUNIT_ASSERT(ctx.output.projectMode() == OutputTable::project_explicit);

		ctx.startAddConstraints();
		ModelEnumerator e;
		e.setStrategy(ModelEnumerator::strategy_backtrack, ModelEnumerator::project_enable_simple, '_');
		e.init(ctx);
		ctx.endInit();
		CPPUNIT_ASSERT(!e.project(v1));
		CPPUNIT_ASSERT(e.project(v2));
		CPPUNIT_ASSERT(e.project(v3));
		ctx.detach(0);
	}
	void testMiniProject() {
		SharedContext ctx;
		Solver& solver = *ctx.master();
		lpAdd(builder.start(ctx, LogicProgram::AspOptions().noEq().noScc()),
			"{x1;x2;x3}.\n"
			"x3 :- not x1.\n"
			"x3 :- not x2.\n"
			"#minimize{x3}.");
		builder.addOutput("a", 1);
		builder.addOutput("b", 2);
		builder.addOutput("_ignore_in_project", 3);
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		ModelEnumerator e;
		e.setStrategy(ModelEnumerator::strategy_backtrack, ModelEnumerator::project_enable_simple);
		e.init(ctx);
		ctx.endInit();

		solver.assume(builder.getLiteral(1));
		solver.propagate();
		solver.assume(builder.getLiteral(2));
		solver.propagate();
		solver.assume(builder.getLiteral(3));
		solver.propagate();
		CPPUNIT_ASSERT(solver.numVars() == solver.numAssignedVars());
		e.commitModel(solver);
		bool ok = e.update(solver) && solver.propagate();
		CPPUNIT_ASSERT(!ok);
		solver.backtrack();
		CPPUNIT_ASSERT(false == solver.propagate() && !solver.resolveConflict());
	}

	void testProjectBug() {
		SharedContext ctx;
		Solver& solver = *ctx.master();
		lpAdd(builder.start(ctx, LogicProgram::AspOptions().noEq().noScc()),
			"{x1;x2;x4}.\n"
			"x5 :- x1, x4.\n"
			"x6 :- x2, x4.\n"
			"x3 :- x5, x6.\n");
		Var x = 1, y = 2, z = 3, _p = 4;
		builder.addOutput("x", x).addOutput("y", y).addOutput("z", z).addOutput("_p", _p);
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		ModelEnumerator e;
		e.setStrategy(ModelEnumerator::strategy_backtrack, ModelEnumerator::project_enable_full);
		e.init(ctx);
		ctx.endInit();

		solver.assume(builder.getLiteral(x));
		solver.propagate();
		solver.assume(builder.getLiteral(y));
		solver.propagate();
		solver.assume(builder.getLiteral(_p));
		solver.propagate();
		CPPUNIT_ASSERT(solver.numVars() == solver.numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, e.commitModel(solver) && e.update(solver));

		solver.undoUntil(0);
		uint32 numT = 0;
		if (solver.value(builder.getLiteral(x).var()) == value_free) {
			solver.assume(builder.getLiteral(x)) && solver.propagate();
			++numT;
		}
		else if (solver.isTrue(builder.getLiteral(x))) {
			++numT;
		}
		if (solver.value(builder.getLiteral(y).var()) == value_free) {
			solver.assume(builder.getLiteral(y)) && solver.propagate();
			++numT;
		}
		else if (solver.isTrue(builder.getLiteral(y))) {
			++numT;
		}
		if (solver.value(builder.getLiteral(_p).var()) == value_free) {
			solver.assume(builder.getLiteral(_p)) && solver.propagate();
		}
		if (solver.isTrue(builder.getLiteral(z))) {
			++numT;
		}
		CPPUNIT_ASSERT(numT < 3);
	}

	void testProjectRestart() {
		SharedContext ctx;
		Solver& solver = *ctx.master();
		lpAdd(builder.start(ctx, LogicProgram::AspOptions().noEq().noScc()), "{x1;x2;x3}.");
		builder.addOutput("a", 1).addOutput("b", 2);
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		ModelEnumerator e;
		e.setStrategy(ModelEnumerator::strategy_backtrack, ModelEnumerator::project_enable_full);
		e.init(ctx);
		ctx.endInit();


		solver.assume(builder.getLiteral(1));
		solver.propagate();
		solver.assume(builder.getLiteral(2));
		solver.propagate();
		solver.assume(builder.getLiteral(3));
		solver.propagate();
		solver.strategies().restartOnModel = true;
		CPPUNIT_ASSERT(solver.numVars() == solver.numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, e.commitModel(solver));
		CPPUNIT_ASSERT_EQUAL(true, e.update(solver));
		CPPUNIT_ASSERT(solver.isFalse(builder.getLiteral(2)));
	}
	void testProjectWithBacktracking() {
		SharedContext ctx;
		Solver& solver = *ctx.master();
		lpAdd(builder.start(ctx, LogicProgram::AspOptions().noEq().noScc()),
			"{x1, x2, x3}."
			"#output a : x1.");
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		ModelEnumerator e;
		e.setStrategy(ModelEnumerator::strategy_backtrack, ModelEnumerator::project_enable_full);
		e.init(ctx);
		ctx.endInit();

		solver.assume(builder.getLiteral(2));
		solver.propagate();
		solver.assume(builder.getLiteral(3));
		solver.propagate();
		// x2@1 -x3
		solver.backtrack();
		// x1@1 -x3 a@2
		solver.assume(builder.getLiteral(1));
		solver.propagate();
		CPPUNIT_ASSERT(solver.numVars() == solver.numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, e.commitModel(solver));
		e.update(solver);
		solver.undoUntil(0);
		while (solver.backtrack()) { ; }
		CPPUNIT_ASSERT(solver.isFalse(builder.getLiteral(1)));
	}
	void testTerminateRemovesWatches() {
		SharedContext ctx; Solver& solver = *ctx.master();
		lpAdd(builder.start(ctx, LogicProgram::AspOptions().noEq().noScc()), "{x1;x2;x3;x4}.");
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		ModelEnumerator e(ModelEnumerator::strategy_record);
		e.init(ctx);
		CPPUNIT_ASSERT_EQUAL(true, ctx.endInit());


		solver.assume(builder.getLiteral(1)) && solver.propagate();
		solver.assume(builder.getLiteral(2)) && solver.propagate();
		solver.assume(builder.getLiteral(3)) && solver.propagate();
		solver.assume(builder.getLiteral(4)) && solver.propagate();
		CPPUNIT_ASSERT_EQUAL(uint32(0), solver.numFreeVars());
		e.commitModel(solver) && e.update(solver);
		uint32 numW = solver.numWatches(builder.getLiteral(1)) + solver.numWatches(builder.getLiteral(2)) + solver.numWatches(builder.getLiteral(3)) + solver.numWatches(builder.getLiteral(4));
		CPPUNIT_ASSERT(numW > 0);
		ctx.detach(solver);
		numW = solver.numWatches(builder.getLiteral(1)) + solver.numWatches(builder.getLiteral(2)) + solver.numWatches(builder.getLiteral(3)) + solver.numWatches(builder.getLiteral(4));
		CPPUNIT_ASSERT(numW == 0);
	}

	void testParallelRecord() {
		SharedContext ctx; Solver& solver = *ctx.master();
		lpAdd(builder.start(ctx, LogicProgram::AspOptions().noEq().noScc()), "{x1;x2;x3;x4}.");
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		ctx.setConcurrency(2);
		ModelEnumerator e(ModelEnumerator::strategy_record);
		e.init(ctx);
		Solver& solver2 = ctx.pushSolver();
		ctx.endInit(true);

		solver.assume(builder.getLiteral(1)) && solver.propagate();
		solver.assume(builder.getLiteral(2)) && solver.propagate();
		solver.assume(builder.getLiteral(3)) && solver.propagate();
		solver.assume(builder.getLiteral(4)) && solver.propagate();
		CPPUNIT_ASSERT_EQUAL(uint32(0), solver.numFreeVars());
		e.commitModel(solver) && e.update(solver);
		solver.undoUntil(0);

		CPPUNIT_ASSERT_EQUAL(true, e.update(solver2));

		solver2.assume(builder.getLiteral(1)) && solver2.propagate();
		solver2.assume(builder.getLiteral(2)) && solver2.propagate();
		solver2.assume(builder.getLiteral(3)) && solver2.propagate();
		CPPUNIT_ASSERT(solver2.isFalse(builder.getLiteral(4)) && solver2.propagate());
		CPPUNIT_ASSERT_EQUAL(uint32(0), solver2.numFreeVars());
		e.commitModel(solver2) && e.update(solver2);
		solver.undoUntil(0);

		CPPUNIT_ASSERT_EQUAL(true, e.update(solver));

		solver.assume(builder.getLiteral(1)) && solver.propagate();
		solver.assume(builder.getLiteral(2)) && solver.propagate();
		CPPUNIT_ASSERT(solver.isFalse(builder.getLiteral(3)));

		ctx.detach(solver2);
		ctx.detach(solver);
		solver2.undoUntil(0);
		ctx.attach(solver2);
		solver2.assume(builder.getLiteral(1)) && solver2.propagate();
		solver2.assume(builder.getLiteral(2)) && solver2.propagate();
		solver2.assume(builder.getLiteral(3)) && solver2.propagate();
		CPPUNIT_ASSERT(solver2.value(builder.getLiteral(4).var()) == value_free);
	}

	void testParallelUpdate() {
		SharedContext ctx; Solver& solver = *ctx.master();
		lpAdd(builder.start(ctx, LogicProgram::AspOptions().noEq().noScc()), "{x1;x2;x3}. #minimize{x2}.");
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		ctx.setConcurrency(2);
		ModelEnumerator e(ModelEnumerator::strategy_record);
		e.init(ctx);

		Solver& solver2 = ctx.pushSolver();
		ctx.endInit(true);

		// x1
		solver.assume(builder.getLiteral(1));
		solver.pushRootLevel(1);
		solver.propagate();
		// ~x2
		solver2.assume(~builder.getLiteral(1));
		solver2.pushRootLevel(1);
		solver2.propagate();

		// M1: ~x2, x3
		solver.assume(~builder.getLiteral(2));
		solver.propagate();
		solver.assume(builder.getLiteral(3));
		solver.propagate();
		CPPUNIT_ASSERT_EQUAL(uint32(0), solver.numFreeVars());
		e.commitModel(solver);
		solver.undoUntil(0);
		e.update(solver);

		// M2: ~x2, ~x3
		solver2.assume(~builder.getLiteral(2));
		solver2.propagate();
		solver2.assume(~builder.getLiteral(3));
		solver2.propagate();
		// M2 is NOT VALID!
		CPPUNIT_ASSERT_EQUAL(false, e.update(solver2));
	}

	void testTagLiteral() {
		ModelEnumerator e;
		SharedContext ctx;
		ctx.addVar(Var_t::Atom);
		ctx.addVar(Var_t::Atom);
		ctx.startAddConstraints();
		e.init(ctx);
		ctx.endInit();
		CPPUNIT_ASSERT(2 == ctx.numVars());
		e.start(*ctx.master());
		ctx.master()->pushTagVar(true);
		CPPUNIT_ASSERT(2 == ctx.numVars());
		CPPUNIT_ASSERT(3 == ctx.master()->numVars());
		CPPUNIT_ASSERT(ctx.master()->isTrue(ctx.master()->tagLiteral()));
	}
	void testIgnoreTagLiteralInPath() {
		SharedContext ctx;
		Var a = ctx.addVar(Var_t::Atom);
		ctx.addVar(Var_t::Atom);
		Solver& s1 = ctx.startAddConstraints();
		Solver& s2 = ctx.pushSolver();
		ctx.endInit();
		ctx.attach(s2);
		s1.pushRoot(posLit(a));
		s1.pushTagVar(true);
		CPPUNIT_ASSERT(s1.rootLevel() == 2 && s1.isTrue(s1.tagLiteral()));
		LitVec path;
		s1.copyGuidingPath(path);
		CPPUNIT_ASSERT(path.size() == 1 && path.back() == posLit(a));
	}
	void testSplittable() {
		SharedContext ctx;
		Var a = ctx.addVar(Var_t::Atom);
		Var b = ctx.addVar(Var_t::Atom);
		Var c = ctx.addVar(Var_t::Atom);
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		s.pushRoot(posLit(a));
		CPPUNIT_ASSERT(!s.splittable());
		s.assume(posLit(b)) && s.propagate();
		CPPUNIT_ASSERT(s.splittable());
		s.pushTagVar(true);
		CPPUNIT_ASSERT(!s.splittable());
		s.assume(posLit(c)) && s.propagate();
		CPPUNIT_ASSERT(s.splittable());
		s.pushRootLevel();
		Var aux = s.pushAuxVar();
		s.assume(posLit(aux)) && s.propagate();
		CPPUNIT_ASSERT(!s.splittable());
	}
	void testLearnStepLiteral() {
		SharedContext ctx;
		ctx.requestStepVar();
		Var a = ctx.addVar(Var_t::Atom);
		ctx.addVar(Var_t::Atom);
		Solver& s1 = ctx.startAddConstraints();
		ctx.pushSolver();
		ctx.endInit(true);
		ClauseCreator cc(&s1);
		cc.start(Constraint_t::Conflict).add(posLit(a)).add(~ctx.stepLiteral()).end();
		ctx.unfreeze();
		ctx.endInit(true);
		s1.pushRoot(negLit(a));
		CPPUNIT_ASSERT(s1.value(ctx.stepLiteral().var()) == value_free);
	}

	void testAssignStepLiteral() {
		SharedContext ctx;
		ctx.requestStepVar();
		ctx.addVar(Var_t::Atom);
		ctx.addVar(Var_t::Atom);
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		CPPUNIT_ASSERT(s.value(ctx.stepLiteral().var()) == value_free);
		ctx.addUnary(ctx.stepLiteral());
		CPPUNIT_ASSERT(s.value(ctx.stepLiteral().var()) != value_free);
		ctx.unfreeze();
		ctx.endInit();
		CPPUNIT_ASSERT(s.value(ctx.stepLiteral().var()) == value_free);
	}

	void testModelHeuristicIsUsed() {
		SharedContext ctx;
		BasicSatConfig config;
		config.addSolver(0).opt.heus = OptParams::heu_model;
		ctx.setConfiguration(&config, Ownership_t::Retain);
		Solver& solver = *ctx.master();
		lpAdd(builder.start(ctx),
			"{x1;x2;x3}.\n"
			"#minimize{x3}.");
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		ModelEnumerator e;
		e.setStrategy(ModelEnumerator::strategy_backtrack, ModelEnumerator::project_enable_simple);
		e.init(ctx);
		ctx.endInit();
		e.start(solver);
		solver.assume(builder.getLiteral(1)) && solver.propagate();
		e.constraint(solver)->modelHeuristic(solver);
		CPPUNIT_ASSERT(solver.isFalse(builder.getLiteral(3)));
	}
	void testDomCombineDef() {
		SharedContext ctx;
		BasicSatConfig config;
		config.addSolver(0).heuId = Heuristic_t::Domain;
		config.addSolver(0).heuristic.domMod = HeuParams::mod_false;
		config.addSolver(0).heuristic.domPref = HeuParams::pref_min|HeuParams::pref_show;
		ctx.setConfiguration(&config, Ownership_t::Retain);
		lpAdd(builder.start(ctx),
			"{x1;x2;x3}.     \n"
			"#output a : x1. \n"
			"#output b : x2. \n"
			"#output c : x3. \n"
			"#minimize {not x1, not x2}.\n");
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		ModelEnumerator e;
		e.setStrategy(ModelEnumerator::strategy_record);
		e.init(ctx);
		ctx.endInit();
		Solver& solver = *ctx.master();
		e.start(solver);
		solver.search(-1, -1);
		CPPUNIT_ASSERT(solver.isTrue(builder.getLiteral(1)));
		CPPUNIT_ASSERT(solver.isTrue(builder.getLiteral(2)));
	}
	void testDomRecComplementShow() {
		SharedContext ctx;
		BasicSatConfig config;
		config.addSolver(0).heuId = Heuristic_t::Domain;
		config.addSolver(0).heuristic.domMod  = HeuParams::mod_false;
		config.addSolver(0).heuristic.domPref = HeuParams::pref_show;
		ctx.setConfiguration(&config, Ownership_t::Retain);
		lpAdd(builder.start(ctx),
			"{x1}.\n"
			"#output a : x1.\n"
			"#output b : not x1.\n");
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		ModelEnumerator e;
		e.setStrategy(ModelEnumerator::strategy_record, ModelEnumerator::project_dom_lits);
		e.init(ctx);
		ctx.endInit();
		CPPUNIT_ASSERT(e.project(builder.getLiteral(1).var()));
		Literal models[][1] = {{~builder.getLiteral(1)}, {builder.getLiteral(1)}};
		Solver& solver = *ctx.master();
		e.start(solver);
		checkModels(solver, e, 2, models);
	}
	void testDomRecComplementAll() {
		SharedContext ctx;
		BasicSatConfig config;
		config.addSolver(0).heuId = Heuristic_t::Domain;
		config.addSolver(0).heuristic.domMod = HeuParams::mod_false;
		config.addSolver(0).heuristic.domPref = HeuParams::pref_atom;
		ctx.setConfiguration(&config, Ownership_t::Retain);
		lpAdd(builder.start(ctx),
			"{x1}.\n"
			"#output a : x1.\n"
			"#output b : not x1.\n");
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		ModelEnumerator e;
		e.setStrategy(ModelEnumerator::strategy_record, ModelEnumerator::project_dom_lits);
		e.init(ctx);
		ctx.endInit();
		CPPUNIT_ASSERT(e.project(builder.getLiteral(1).var()));
		Solver& solver = *ctx.master();
		Literal models[][1] = {{~builder.getLiteral(1)}, {builder.getLiteral(1)}};
		e.start(solver);
		checkModels(solver, e, 2, models);
	}
	void testDomRecAssume() {
		SharedContext ctx;
		BasicSatConfig config;
		config.addSolver(0).heuId = Heuristic_t::Domain;
		ctx.setConfiguration(&config, Ownership_t::Retain);
		builder.start(ctx);
		builder.update();
		lpAdd(builder,
			"#external x3.\n"
			"{x1;x2}.\n"
			":- not x1, not x2.\n"
			"#heuristic x1 : x3.     [2,false]\n"
			"#heuristic x2 : x3.     [1,false]\n"
			"#heuristic x1 : not x3. [2,true]\n"
			"#heuristic x2 : not x3. [1,true]\n");
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		Literal x1 = builder.getLiteral(1);
		Literal x2 = builder.getLiteral(2);
		Literal x3 = builder.getLiteral(3);
		LitVec assume;
		builder.getAssumptions(assume);
		ctx.requestStepVar();
		ModelEnumerator e;
		e.setStrategy(ModelEnumerator::strategy_record, ModelEnumerator::project_dom_lits);
		Solver& solver = *ctx.master();
		Literal model[][2] = {
			{x1, x2},
			{~x1, x2},
			{~x2, x1},
		};
		{
			CPPUNIT_ASSERT(assume.size() == 1 && assume[0] == ~x3);
			ctx.heuristic.assume = &assume;
			e.init(ctx);
			ctx.endInit();
			e.start(solver, assume);
			checkModels(solver, e, 1, model);
		}
		builder.update();
		lpAdd(builder, "#external x3. [true]\n");
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		assume.clear();
		builder.getAssumptions(assume);
		ctx.heuristic.assume = &assume;
		CPPUNIT_ASSERT(assume.size() == 1 && assume[0] == x3);
		e.init(ctx);
		ctx.endInit();
		e.start(solver, assume);
		checkModels(solver, e, 2, model + 1);
	}
	void testNotAttached() {
		SharedContext ctx;
		ctx.addVar(Var_t::Atom);
		ctx.addVar(Var_t::Atom);
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		ModelEnumerator e;
		CPPUNIT_ASSERT_THROW(e.start(s), std::logic_error);
	}
private:
	template <size_t S>
	void checkModels(Solver& s, Enumerator& e, uint32 expected, Literal (*x)[S]) {
		for (uint32 seenModels = 0;; ++x, e.update(s)) {
			ValueRep val = s.search(-1, -1);
			if (val == value_true) {
				CPPUNIT_ASSERT(++seenModels <= expected);
				e.commitModel(s);
				for (size_t i = 0; i != S; ++i) {
					CPPUNIT_ASSERT(s.isTrue(x[0][i]));
				}
			}
			else {
				CPPUNIT_ASSERT(seenModels == expected);
				break;
			}
		}
	}
	LogicProgram builder;
	stringstream str;
};
CPPUNIT_TEST_SUITE_REGISTRATION(EnumeratorTest);
 } }
