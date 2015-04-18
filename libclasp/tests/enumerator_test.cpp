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
	CPPUNIT_TEST(testMiniProject);
	CPPUNIT_TEST(testProjectBug);
	CPPUNIT_TEST(testProjectRestart);
	CPPUNIT_TEST(testTerminateRemovesWatches);
	CPPUNIT_TEST(testParallelRecord);
	CPPUNIT_TEST(testParallelUpdate);
	CPPUNIT_TEST(testTagLiteral);
	CPPUNIT_TEST(testIgnoreTagLiteralInPath);
	CPPUNIT_TEST(testSplittable);
	CPPUNIT_TEST(testLearnStepLiteral);
	CPPUNIT_TEST(testAssignStepLiteral);
	CPPUNIT_TEST_SUITE_END();	
public:
	void testMiniProject() {
		SharedContext ctx;
		Solver& solver = *ctx.master();
		builder.start(ctx, LogicProgram::AspOptions().noEq().noScc())
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "_x")
			.startRule(CHOICERULE).addHead(1).addHead(2).addHead(3).endRule()
			.startRule().addHead(3).addToBody(1, false).endRule()
			.startRule().addHead(3).addToBody(2, false).endRule()
			.startRule(OPTIMIZERULE).addToBody(3, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		ModelEnumerator e;
		e.setStrategy(ModelEnumerator::strategy_backtrack, ModelEnumerator::project_enable_simple);
		e.init(ctx, builder.getMinimizeConstraint()->share());
		ctx.endInit();
		SymbolTable& index = ctx.symbolTable();
		solver.assume(index[1].lit);
		solver.propagate();
		solver.assume(index[2].lit);
		solver.propagate();
		solver.assume(index[3].lit);
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
		builder.start(ctx, LogicProgram::AspOptions().noEq().noScc())
			.setAtomName(1, "x").setAtomName(2, "y").setAtomName(3, "z").setAtomName(4, "_p").setAtomName(5, "_q").setAtomName(6, "_r")
			.startRule(CHOICERULE).addHead(1).addHead(2).addHead(4).endRule() // {x,y,_p}
			.startRule().addHead(5).addToBody(1, true).addToBody(4, true).endRule() // _q :- x,_p.
			.startRule().addHead(6).addToBody(2, true).addToBody(4, true).endRule() // _r :- y,_p.
			.startRule().addHead(3).addToBody(5, true).addToBody(6, true).endRule() // z :- _q,_r.
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		ModelEnumerator e;
		e.setStrategy(ModelEnumerator::strategy_backtrack, ModelEnumerator::project_enable_full);
		e.init(ctx, 0);
		ctx.endInit();
		SymbolTable& index = ctx.symbolTable();
		solver.assume(index[1].lit);
		solver.propagate();
		solver.assume(index[2].lit);
		solver.propagate();
		solver.assume(index[4].lit);
		solver.propagate();
		CPPUNIT_ASSERT(solver.numVars() == solver.numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, e.commitModel(solver) && e.update(solver));

		solver.undoUntil(0);
		uint32 numT = 0;
		if (solver.value(index[1].lit.var()) == value_free) {
			solver.assume(index[1].lit) && solver.propagate();
			++numT;
		}
		else if (solver.isTrue(index[1].lit)) {
			++numT;
		}
		if (solver.value(index[2].lit.var()) == value_free) {
			solver.assume(index[2].lit) && solver.propagate();
			++numT;
		}
		else if (solver.isTrue(index[2].lit)) {
			++numT;
		}
		if (solver.value(index[4].lit.var()) == value_free) {
			solver.assume(index[4].lit) && solver.propagate();
		}
		if (solver.isTrue(index[3].lit)) {
			++numT;
		}
		CPPUNIT_ASSERT(numT < 3);
	}
	
	void testProjectRestart() {
		SharedContext ctx;
		Solver& solver = *ctx.master();
		builder.start(ctx, LogicProgram::AspOptions().noEq().noScc())
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "_c")
			.startRule(CHOICERULE).addHead(1).addHead(2).addHead(3).endRule() // {a,b,_c}
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		ModelEnumerator e;
		e.setStrategy(ModelEnumerator::strategy_backtrack, ModelEnumerator::project_enable_full);
		e.init(ctx, 0);
		ctx.endInit();
		
		SymbolTable& index = ctx.symbolTable();
		solver.assume(index[1].lit);
		solver.propagate();
		solver.assume(index[2].lit);
		solver.propagate();
		solver.assume(index[3].lit);
		solver.propagate();
		solver.strategies().restartOnModel = true;
		CPPUNIT_ASSERT(solver.numVars() == solver.numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, e.commitModel(solver));
		CPPUNIT_ASSERT_EQUAL(true, e.update(solver));
		CPPUNIT_ASSERT(solver.isFalse(index[2].lit));
	}

	void testTerminateRemovesWatches() {
		SharedContext ctx; Solver& solver = *ctx.master();
		builder.start(ctx, LogicProgram::AspOptions().noEq().noScc())
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "d")
			.startRule(CHOICERULE).addHead(1).addHead(2).addHead(3).addHead(4).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		ModelEnumerator e(ModelEnumerator::strategy_record);
		e.init(ctx, 0);
		CPPUNIT_ASSERT_EQUAL(true, ctx.endInit());
		
		SymbolTable& index = ctx.symbolTable();
		solver.assume(index[1].lit) && solver.propagate();
		solver.assume(index[2].lit) && solver.propagate();
		solver.assume(index[3].lit) && solver.propagate();
		solver.assume(index[4].lit) && solver.propagate();
		CPPUNIT_ASSERT_EQUAL(uint32(0), solver.numFreeVars());
		e.commitModel(solver) && e.update(solver);
		uint32 numW = solver.numWatches(index[1].lit) + solver.numWatches(index[2].lit) + solver.numWatches(index[3].lit) + solver.numWatches(index[4].lit);
		CPPUNIT_ASSERT(numW > 0);
		ctx.detach(solver);
		numW = solver.numWatches(index[1].lit) + solver.numWatches(index[2].lit) + solver.numWatches(index[3].lit) + solver.numWatches(index[4].lit);
		CPPUNIT_ASSERT(numW == 0);
	}

	void testParallelRecord() {
		SharedContext ctx; Solver& solver = *ctx.master();
		builder.start(ctx, LogicProgram::AspOptions().noEq().noScc())
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "d")
			.startRule(CHOICERULE).addHead(1).addHead(2).addHead(3).addHead(4).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		ctx.setConcurrency(2);
		ModelEnumerator e(ModelEnumerator::strategy_record);
		e.init(ctx, 0);
		Solver& solver2 = ctx.addSolver();
		ctx.endInit(true);
		SymbolTable& index = ctx.symbolTable();
		solver.assume(index[1].lit) && solver.propagate();
		solver.assume(index[2].lit) && solver.propagate();
		solver.assume(index[3].lit) && solver.propagate();
		solver.assume(index[4].lit) && solver.propagate();
		CPPUNIT_ASSERT_EQUAL(uint32(0), solver.numFreeVars());
		e.commitModel(solver) && e.update(solver);
		solver.undoUntil(0);
		
		CPPUNIT_ASSERT_EQUAL(true, e.update(solver2));

		solver2.assume(index[1].lit) && solver2.propagate();
		solver2.assume(index[2].lit) && solver2.propagate();
		solver2.assume(index[3].lit) && solver2.propagate();
		CPPUNIT_ASSERT(solver2.isFalse(index[4].lit) && solver2.propagate());
		CPPUNIT_ASSERT_EQUAL(uint32(0), solver2.numFreeVars());
		e.commitModel(solver2) && e.update(solver2);
		solver.undoUntil(0);

		CPPUNIT_ASSERT_EQUAL(true, e.update(solver));

		solver.assume(index[1].lit) && solver.propagate();
		solver.assume(index[2].lit) && solver.propagate();
		CPPUNIT_ASSERT(solver.isFalse(index[3].lit));

		ctx.detach(solver2);
		ctx.detach(solver);
		solver2.undoUntil(0);
		ctx.attach(solver2);
		solver2.assume(index[1].lit) && solver2.propagate();
		solver2.assume(index[2].lit) && solver2.propagate();
		solver2.assume(index[3].lit) && solver2.propagate();
		CPPUNIT_ASSERT(solver2.value(index[4].lit.var()) == value_free);
	}

	void testParallelUpdate() {
		SharedContext ctx; Solver& solver = *ctx.master();
		builder.start(ctx, LogicProgram::AspOptions().noEq().noScc())
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c")
			.startRule(CHOICERULE).addHead(1).addHead(2).addHead(3).endRule()
			.startRule(OPTIMIZERULE).addToBody(2, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		ctx.setConcurrency(2);
		ModelEnumerator e(ModelEnumerator::strategy_record);
		e.init(ctx, builder.getMinimizeConstraint()->share());
		
		Solver& solver2 = ctx.addSolver();
		ctx.endInit(true);
		SymbolTable& index = ctx.symbolTable();

		// a
		solver.assume(index[1].lit);
		solver.pushRootLevel(1);
		solver.propagate();
		// ~a
		solver2.assume(~index[1].lit);
		solver2.pushRootLevel(1);
		solver2.propagate();

		// M1: ~b, c
		solver.assume(~index[2].lit);
		solver.propagate();
		solver.assume(index[3].lit);
		solver.propagate();	
		CPPUNIT_ASSERT_EQUAL(uint32(0), solver.numFreeVars());
		e.commitModel(solver);
		solver.undoUntil(0);
		e.update(solver);
		
		// M2: ~b, ~c 
		solver2.assume(~index[2].lit);
		solver2.propagate();
		solver2.assume(~index[3].lit);
		solver2.propagate();	
		// M2 is NOT VALID!
		CPPUNIT_ASSERT_EQUAL(false, e.update(solver2));
	}

	void testTagLiteral() {
		ModelEnumerator e;
		SharedContext ctx;
		ctx.addVar(Var_t::atom_var);
		ctx.addVar(Var_t::atom_var);
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
		Var a = ctx.addVar(Var_t::atom_var);
		ctx.addVar(Var_t::atom_var);
		Solver& s1 = ctx.startAddConstraints();
		Solver& s2 = ctx.addSolver();
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
		Var a = ctx.addVar(Var_t::atom_var);
		Var b = ctx.addVar(Var_t::atom_var);
		Var c = ctx.addVar(Var_t::atom_var);
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
		Var a = ctx.addVar(Var_t::atom_var);
		ctx.addVar(Var_t::atom_var);
		Solver& s1 = ctx.startAddConstraints();
		ctx.addSolver();
		ctx.endInit(true);
		ClauseCreator cc(&s1);
		cc.start(Constraint_t::learnt_conflict).add(posLit(a)).add(~ctx.stepLiteral()).end();
		ctx.unfreeze();
		ctx.endInit(true);
		s1.pushRoot(negLit(a));
		CPPUNIT_ASSERT(s1.value(ctx.stepLiteral().var()) == value_free);
	}

	void testAssignStepLiteral() {
		SharedContext ctx;
		ctx.requestStepVar();
		Var a = ctx.addVar(Var_t::atom_var);
		ctx.addVar(Var_t::atom_var);
		Solver& s = ctx.startAddConstraints();
		CPPUNIT_ASSERT(s.value(ctx.stepLiteral().var()) == value_free);
		ctx.addUnary(ctx.stepLiteral());
		ctx.endInit();
		CPPUNIT_ASSERT(s.value(ctx.stepLiteral().var()) != value_free);
		ctx.unfreeze();
		ctx.endInit();
		CPPUNIT_ASSERT(s.value(ctx.stepLiteral().var()) == value_free);
	}
private:
	LogicProgram builder;
	stringstream str;
	Model model;
};
CPPUNIT_TEST_SUITE_REGISTRATION(EnumeratorTest);
 } } 
