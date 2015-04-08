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
#include <clasp/solver.h>
#include <clasp/program_builder.h>
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
	CPPUNIT_TEST_SUITE_END();	
public:
	void tearDown(){
		ctx.reset();
	}
	void testSimpleChoice() {
		// a | b.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule(DISJUNCTIVERULE).addHead(1).addHead(2).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(builder.stats.rules(DISJUNCTIVERULE).first == 1);
		const SymbolTable& index = ctx.symbolTable();
		CPPUNIT_ASSERT(index[1].lit != index[2].lit);
		ctx.master()->assume(index[1].lit) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(index[2].lit));
		ctx.master()->undoUntil(0);
		ctx.master()->assume(index[2].lit) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(index[1].lit));
	}
	void testNotAChoice() {
		// a | b.
		// a :- not x.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "x")
			.startRule(DISJUNCTIVERULE).addHead(1).addHead(2).endRule()
			.startRule().addHead(1).addToBody(3, false).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(builder.stats.rules(DISJUNCTIVERULE).first == 1);
		const SymbolTable& index = ctx.symbolTable();
		CPPUNIT_ASSERT(index[2].lit == index[3].lit);
		CPPUNIT_ASSERT(index[1].lit == posLit(0));
	}

	void testStillAChoice() {
		// a | b.
		// {b}.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule(DISJUNCTIVERULE).addHead(1).addHead(2).endRule()
			.startRule(CHOICERULE).addHead(2).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(builder.stats.rules(DISJUNCTIVERULE).first == 1);
		const SymbolTable& index = ctx.symbolTable();
		CPPUNIT_ASSERT(index[1].lit != index[2].lit);
		ctx.master()->assume(index[1].lit) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(index[2].lit));
		ctx.master()->undoUntil(0);
		ctx.master()->assume(index[2].lit) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(index[1].lit));
	}

	void testSubsumedChoice() {
		// a | b.
		// a | b | c | d.
		builder.start(ctx, LogicProgram::AspOptions().iterations(-1))
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "d")
			.startRule(DISJUNCTIVERULE).addHead(1).addHead(2).endRule()
			.startRule(DISJUNCTIVERULE).addHead(1).addHead(2).addHead(3).addHead(4).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(builder.stats.rules(DISJUNCTIVERULE).first == 2);
		const SymbolTable& index = ctx.symbolTable();
		CPPUNIT_ASSERT(index[3].lit == negLit(0) || !(ctx.master()->assume(index[3].lit) && ctx.master()->propagate()));
		ctx.master()->undoUntil(0);
		CPPUNIT_ASSERT(index[4].lit == negLit(0) || !(ctx.master()->assume(index[4].lit) && ctx.master()->propagate()));
	}
	
	void testSubsumedByChoice() {
		// a | b.
		// {a,b}.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule(DISJUNCTIVERULE).addHead(1).addHead(2).endRule()
			.startRule(CHOICERULE).addHead(1).addHead(2).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(builder.stats.rules(DISJUNCTIVERULE).first == 1);
		const SymbolTable& index = ctx.symbolTable();
		ctx.master()->assume(~index[1].lit) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isTrue(index[2].lit));
	}
	void testChoiceDisjBug() {
		// a | b.
		// {a,b,b}.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c")
			.startRule(DISJUNCTIVERULE).addHead(1).addHead(2).endRule()
			.startRule(CHOICERULE).addHead(1).addHead(2).addHead(3).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(builder.stats.rules(DISJUNCTIVERULE).first == 1);
		const SymbolTable& index = ctx.symbolTable();
		ctx.master()->assume(index[3].lit) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->value(index[1].lit.var()) == value_free);
		CPPUNIT_ASSERT(ctx.master()->value(index[2].lit.var()) == value_free);
		ctx.master()->assume(~index[1].lit) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isTrue(index[2].lit));
		ctx.master()->undoUntil(0);
		ctx.master()->assume(index[1].lit) && ctx.master()->propagate();
		ctx.master()->assume(index[2].lit) && ctx.master()->propagate();
		ctx.master()->assume(index[3].lit) && ctx.master()->propagate();
		CPPUNIT_ASSERT(!ctx.master()->hasConflict() && ctx.master()->numFreeVars() == 0);
	}

	void testTautOverOne() {
		// {x}.
		// y :- x.
		// a | x :- y.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "x").setAtomName(3, "y")
			.startRule(DISJUNCTIVERULE).addHead(1).addHead(2).addToBody(3, true).endRule()
			.startRule(CHOICERULE).addHead(2).endRule()
			.startRule().addHead(3).addToBody(2, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(builder.stats.rules(DISJUNCTIVERULE).first == 1);
		const SymbolTable& index = ctx.symbolTable();
		CPPUNIT_ASSERT(index[1].lit == negLit(0) && !(ctx.master()->assume(index[1].lit) && ctx.master()->propagate()));
	}
	
	void testSimpleLoop() {
		// a | b.
		// a :- b.
		// b :- a.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule(DISJUNCTIVERULE).addHead(1).addHead(2).endRule()
			.startRule().addHead(1).addToBody(2, true).endRule()
			.startRule().addHead(2).addToBody(1, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(builder.stats.rules(DISJUNCTIVERULE).first == 1);
		ctx.master()->addPost(new DefaultUnfoundedCheck());
		CPPUNIT_ASSERT_EQUAL(true, ctx.endInit());
		const SymbolTable& index = ctx.symbolTable();
		CPPUNIT_ASSERT(index[1].lit != index[2].lit);
		CPPUNIT_ASSERT(ctx.master()->assume(index[1].lit) && ctx.master()->propagate());
		CPPUNIT_ASSERT(!ctx.master()->isFalse(index[2].lit));
		ctx.master()->undoUntil(0);
		CPPUNIT_ASSERT(ctx.master()->assume(index[2].lit) && ctx.master()->propagate());
		CPPUNIT_ASSERT(!ctx.master()->isFalse(index[1].lit));
	}

	void testSimpleLoopNoGamma() {
		// a | b.
		// a :- b.
		// b :- a.
		builder.start(ctx, LogicProgram::AspOptions().disableGamma())
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule(DISJUNCTIVERULE).addHead(1).addHead(2).endRule()
			.startRule().addHead(1).addToBody(2, true).endRule()
			.startRule().addHead(2).addToBody(1, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(builder.stats.rules(DISJUNCTIVERULE).first == 1);
		const SymbolTable& index = ctx.symbolTable();
		CPPUNIT_ASSERT(!(ctx.master()->assume(~index[1].lit) && ctx.master()->propagate()) || ctx.master()->isTrue(index[2].lit));
	}
	void testComputeTrue() {
		// a | x.
		// :- not a.
		// a :- x.
		builder.start(ctx, LogicProgram::AspOptions().noScc())
			.setAtomName(1, "a").setAtomName(2, "x")
			.startRule(DISJUNCTIVERULE).addHead(1).addHead(2).endRule()
			.startRule().addHead(1).addToBody(2, true).endRule()
			.setCompute(1, true);
		;
		CPPUNIT_ASSERT(builder.getAtom(1)->value() == value_true);
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(builder.stats.rules(DISJUNCTIVERULE).first == 1);
		const SymbolTable& index = ctx.symbolTable();
		CPPUNIT_ASSERT(ctx.master()->isTrue(index[1].lit));
		CPPUNIT_ASSERT(ctx.master()->isFalse(index[2].lit));
	}
	void testComputeFalse() {
		// a | b | x.
		// :- a.
		// a :- x.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "x")
			.startRule(DISJUNCTIVERULE).addHead(1).addHead(2).addHead(3).endRule()
			.startRule().addHead(1).addToBody(3, true).endRule()
			.setCompute(1, false);
		;
		CPPUNIT_ASSERT(builder.getAtom(1)->value() == value_false);
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(builder.stats.rules(DISJUNCTIVERULE).first == 1);
		const SymbolTable& index = ctx.symbolTable();
		CPPUNIT_ASSERT(ctx.master()->isFalse(index[1].lit));
		CPPUNIT_ASSERT(ctx.master()->isFalse(index[3].lit));
		CPPUNIT_ASSERT(ctx.master()->isTrue(index[2].lit));
	}
	void testIncremental() {
		// Step 0:
		// a | b :- x.
		// a :- b.
		// b :- a.
		// freeze x.
		builder.start(ctx);
		builder.updateProgram();
		builder.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "x")
			.startRule(DISJUNCTIVERULE).addHead(1).addHead(2).addToBody(3,true).endRule()
			.startRule().addHead(1).addToBody(2, true).endRule()
			.startRule().addHead(2).addToBody(1, true).endRule()
			.freeze(3);
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(builder.stats.rules(DISJUNCTIVERULE).first == 1);
		CPPUNIT_ASSERT(builder.stats.sccs == 1);
		CPPUNIT_ASSERT(builder.stats.nonHcfs == 1);

		// Step 1:
		// c | d :- a, y.
		// c :- d, b.
		// d :- c, a.
		// freeze y.
		builder.update();
		builder.setAtomName(4, "c").setAtomName(5, "d").setAtomName(6, "y")
			.startRule(DISJUNCTIVERULE).addHead(4).addHead(5).addToBody(1,true).addToBody(6,true).endRule()
			.startRule().addHead(4).addToBody(5, true).addToBody(2, true).endRule()
			.startRule().addHead(5).addToBody(4, true).addToBody(1, true).endRule()
			.freeze(6);
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(builder.stats.rules(DISJUNCTIVERULE).first == 1);
		CPPUNIT_ASSERT(builder.stats.sccs == 1);
		CPPUNIT_ASSERT(builder.stats.nonHcfs == 1);
	}

	void testSimplify() {
		// a | b :- x.
		// a :- b.
		// b :- c.
		// c :- a,y.
		// {x,y}.
		builder.start(ctx);
		builder.updateProgram();
		builder.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "x").setAtomName(5, "y")
			.startRule(DISJUNCTIVERULE).addHead(1).addHead(2).addToBody(4,true).endRule()
			.startRule().addHead(1).addToBody(2, true).endRule()
			.startRule().addHead(2).addToBody(3, true).endRule()
			.startRule().addHead(3).addToBody(1, true).addToBody(5,true).endRule()
			.startRule(Asp::CHOICERULE).addHead(4).addHead(5).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(builder.stats.rules(DISJUNCTIVERULE).first == 1);
		CPPUNIT_ASSERT(builder.stats.sccs == 1);
		CPPUNIT_ASSERT(builder.stats.nonHcfs == 1);
		DG& graph = *ctx.sccGraph;
		CPPUNIT_ASSERT(graph.numNonHcfs() == 1);
		ctx.addUnary(~builder.getAtom(1)->literal());
		ctx.master()->propagate();
		graph.simplify(*ctx.master());
		CPPUNIT_ASSERT(graph.numNonHcfs() == 0);
	}
	void testSimplifyNoRemove() {
		ctx.setConcurrency(2);
		builder.start(ctx);
		builder.updateProgram();
		builder.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "x").setAtomName(5, "y")
			.startRule(DISJUNCTIVERULE).addHead(1).addHead(2).addToBody(4,true).endRule()
			.startRule().addHead(1).addToBody(2, true).endRule()
			.startRule().addHead(2).addToBody(3, true).endRule()
			.startRule().addHead(3).addToBody(1, true).addToBody(5,true).endRule()
			.startRule(Asp::CHOICERULE).addHead(4).addHead(5).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		Solver& s2= ctx.addSolver();
		CPPUNIT_ASSERT(ctx.endInit(true));
		DG& graph = *ctx.sccGraph;
		CPPUNIT_ASSERT(graph.numNonHcfs() == 1);
		Literal u = ~builder.getAtom(1)->literal();
		ctx.master()->add(ClauseRep::create(&u, 1, Constraint_t::learnt_conflict));
		ctx.master()->simplify() && s2.simplify();
		CPPUNIT_ASSERT(graph.numNonHcfs() == 1);
		const DG::ComponentPair& c = *graph.nonHcfBegin();
		
		CPPUNIT_ASSERT_EQUAL(false, c.second->simplify(c.first, *ctx.master()));
		CPPUNIT_ASSERT_EQUAL(true , c.second->simplify(c.first, s2));

		LitVec temp;
		VarVec ufs;
		c.second->assumptionsFromAssignment(*ctx.master(), temp);
		CPPUNIT_ASSERT_EQUAL(true, c.second->test(c.first, *ctx.master(), temp, ufs) && ufs.empty());

		temp.clear();
		c.second->assumptionsFromAssignment(s2, temp);
		CPPUNIT_ASSERT_EQUAL(true, c.second->test(c.first, s2, temp, ufs) && ufs.empty());
	}
	void testNoDupGamma() {
		// a | b.
		// a :- b.
		// b :- a.
		// a :- not b.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule(DISJUNCTIVERULE).addHead(1).addHead(2).endRule()
			.startRule().addHead(1).addToBody(2, true).endRule()
			.startRule().addHead(2).addToBody(1, true).endRule()
			.startRule().addHead(1).addToBody(2, false).endRule()
			;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(builder.numBodies() == 5); // + b :- not a.
		CPPUNIT_ASSERT(builder.stats.gammas == 1);
		stringstream  str;
		builder.write(str);
		std::string x = str.str();
		std::size_t p = x.find("1 1 1 1 2");
		CPPUNIT_ASSERT(p != std::string::npos);
		p = x.find("1 1 1 1 2", p + std::strlen("1 1 1 1 2") + 1);
		CPPUNIT_ASSERT(p == std::string::npos);
	}
	void testPreNoGamma() {
		// a | b.
		// a :- b.
		// b :- a.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule(DISJUNCTIVERULE).addHead(1).addHead(2).endRule()
			.startRule().addHead(1).addToBody(2, true).endRule()
			.startRule().addHead(2).addToBody(1, true).endRule()
			;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		stringstream  str;
		builder.write(str);
		CPPUNIT_ASSERT(str.str().find("1 1 1 1 2") == std::string::npos);
	}
	void testPreNoGamma2() {
		// a | b.
		// a :- b.
		// b :- a.
		builder.start(ctx, LogicProgram::AspOptions().disableGamma())
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule(DISJUNCTIVERULE).addHead(1).addHead(2).endRule()
			.startRule().addHead(1).addToBody(2, true).endRule()
			.startRule().addHead(2).addToBody(1, true).endRule()
			;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		stringstream  str;
		builder.write(str);
		CPPUNIT_ASSERT(str.str().find("3 2 1 2 0 0") == std::string::npos);
	}
private:
	typedef SharedDependencyGraph DG;
	SharedContext ctx;
	LogicProgram  builder;
	stringstream  str;
};
CPPUNIT_TEST_SUITE_REGISTRATION(DlpBuilderTest);
 } } 
