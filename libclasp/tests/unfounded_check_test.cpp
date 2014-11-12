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
#include <clasp/unfounded_check.h>
#include <clasp/program_builder.h>
#include <clasp/clause.h>
#include <memory>

namespace Clasp { namespace Test {
	using namespace Clasp::Asp;
	class UnfoundedCheckTest : public CppUnit::TestFixture {
	CPPUNIT_TEST_SUITE(UnfoundedCheckTest);
	CPPUNIT_TEST(testAllUncoloredNoUnfounded);
	CPPUNIT_TEST(testAlternativeSourceNotUnfounded);
	CPPUNIT_TEST(testOnlyOneSourceUnfoundedIfMinus);
	
	CPPUNIT_TEST(testWithSimpleCardinalityConstraint);
	CPPUNIT_TEST(testWithSimpleWeightConstraint);
	
	CPPUNIT_TEST(testNtExtendedBug);
	CPPUNIT_TEST(testNtExtendedFalse);
	
	CPPUNIT_TEST(testDependentExtReason);
	CPPUNIT_TEST(testEqBodyDiffType);
	CPPUNIT_TEST(testChoiceCardInterplay);
	CPPUNIT_TEST(testCardInterplayOnBT);

	CPPUNIT_TEST(testInitNoSource);

	CPPUNIT_TEST(testIncrementalUfs);
	CPPUNIT_TEST(testInitialStopConflict);
	CPPUNIT_TEST(testIncrementalLearnFact);

	CPPUNIT_TEST(testDetachRemovesWatches);

	CPPUNIT_TEST(testApproxUfs);
	CPPUNIT_TEST_SUITE_END(); 
public:
	class WrapDefaultUnfoundedCheck : public DefaultUnfoundedCheck {
	public:
		bool propagate(Solver& s) { return DefaultUnfoundedCheck::propagateFixpoint(s, 0); }
	};
	UnfoundedCheckTest() : ufs(0) { }
	void setUp() { 
		ufs   = new WrapDefaultUnfoundedCheck();
	}
	void tearDown() {
		ufs   = 0;
	}
	Solver& solver() { return *ctx.master(); }
	void testAllUncoloredNoUnfounded() {
		setupSimpleProgram();
		uint32 x = solver().numAssignedVars();
		CPPUNIT_ASSERT_EQUAL(true, ufs->propagate(solver()));
		CPPUNIT_ASSERT_EQUAL(x, solver().numAssignedVars());
	}
	
	void testAlternativeSourceNotUnfounded() {
		setupSimpleProgram();
		solver().assume( ctx.symbolTable()[6].lit );
		solver().propagateUntil(ufs.get());
		uint32 old = solver().numAssignedVars();
		CPPUNIT_ASSERT_EQUAL(true, ufs->propagate(solver()));
		CPPUNIT_ASSERT_EQUAL(old, solver().numAssignedVars());
	}
	
	void testOnlyOneSourceUnfoundedIfMinus() {
		setupSimpleProgram();
		solver().assume( ctx.symbolTable()[6].lit );
		solver().assume( ctx.symbolTable()[5].lit );
		solver().propagateUntil(ufs.get());
		uint32 old = solver().numAssignedVars();
		uint32 oldC = ctx.numConstraints();
		CPPUNIT_ASSERT_EQUAL(true, ufs->propagate(solver()));
		CPPUNIT_ASSERT(old < solver().numAssignedVars());
		CPPUNIT_ASSERT(solver().isFalse(ctx.symbolTable()[4].lit));
		CPPUNIT_ASSERT(solver().isFalse(ctx.symbolTable()[1].lit));
		CPPUNIT_ASSERT(!solver().isFalse(ctx.symbolTable()[2].lit));
		CPPUNIT_ASSERT(oldC+1 == ctx.numConstraints() + ctx.numLearntShort());
	}
	
	void testWithSimpleCardinalityConstraint() {
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule(CHOICERULE).addHead(2).endRule()
			.startRule(CONSTRAINTRULE, 1).addHead(1).addToBody(1, true).addToBody(2,true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		attachUfs();
		
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(2u, solver().numVars());
		CPPUNIT_ASSERT_EQUAL(0u, solver().numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, ufs->propagate(solver()) );
		CPPUNIT_ASSERT_EQUAL(0u, solver().numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, solver().assume(~ctx.symbolTable()[2].lit));
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(1u, solver().numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, ufs->propagate(solver()) );
		CPPUNIT_ASSERT_EQUAL(2u, solver().numAssignedVars());
		LitVec r;
		solver().reason(~ctx.symbolTable()[1].lit, r);
		CPPUNIT_ASSERT(1 == r.size());
		CPPUNIT_ASSERT(r[0] == ~ctx.symbolTable()[2].lit);
	}
	void testWithSimpleWeightConstraint() {
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c")
			.startRule(CHOICERULE).addHead(2).addHead(3).endRule()
			.startRule(WEIGHTRULE, 2).addHead(1).addToBody(1, true, 2).addToBody(2,true, 2).addToBody(3, true, 1).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		attachUfs();
		
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(3u, solver().numVars());
		CPPUNIT_ASSERT_EQUAL(0u, solver().numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, ufs->propagate(solver()) );
		CPPUNIT_ASSERT_EQUAL(0u, solver().numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, solver().assume(~ctx.symbolTable()[3].lit));
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(1u, solver().numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, ufs->propagate(solver()) );
		CPPUNIT_ASSERT_EQUAL(1u, solver().numAssignedVars());

		CPPUNIT_ASSERT_EQUAL(true, solver().assume(~ctx.symbolTable()[2].lit));
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(2u, solver().numAssignedVars());

		CPPUNIT_ASSERT_EQUAL(true, ufs->propagate(solver()) );
		CPPUNIT_ASSERT_EQUAL(3u, solver().numAssignedVars());
		
		LitVec r;
		solver().reason(~ctx.symbolTable()[1].lit, r);
		CPPUNIT_ASSERT(2 == r.size());
		CPPUNIT_ASSERT(r[0] == ~ctx.symbolTable()[2].lit);
		CPPUNIT_ASSERT(r[1] == ~ctx.symbolTable()[3].lit);

		solver().undoUntil(0);
		CPPUNIT_ASSERT_EQUAL(true, solver().assume(~ctx.symbolTable()[2].lit));
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(1u, solver().numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, ufs->propagate(solver()) );
		CPPUNIT_ASSERT_EQUAL(2u, solver().numAssignedVars());
		r.clear();
		solver().reason(~ctx.symbolTable()[1].lit, r);
		CPPUNIT_ASSERT(1 == r.size());
		CPPUNIT_ASSERT(r[0] == ~ctx.symbolTable()[2].lit);
	}
	
	void testNtExtendedBug() {
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "t").setAtomName(5, "x")
			.startRule(CHOICERULE).addHead(1).addHead(2).addHead(3).endRule() // {a,b,c}.
			.startRule(CONSTRAINTRULE, 2).addHead(4).addToBody(2, true).addToBody(4, true).addToBody(5,true).endRule()
			.startRule().addHead(5).addToBody(4,true).addToBody(3,true).endRule()
			.startRule().addHead(5).addToBody(1,true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		attachUfs();
		
		// T: {t,c}
		solver().assume(Literal(6, false));
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(true, ufs->propagate(solver()));
		solver().assume(~ctx.symbolTable()[1].lit);
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(false, ufs->propagate(solver()));  // {x, t} are unfounded!
		
		solver().undoUntil(0);
		ufs->reset();

		// F: {t,c}
		solver().assume(Literal(6, true));
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		// F: a
		solver().assume(~ctx.symbolTable()[1].lit);
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		// x is false because both of its bodies are false
		CPPUNIT_ASSERT_EQUAL(true, solver().isFalse(ctx.symbolTable()[5].lit));
	
		// t is now unfounded but its defining body is not
		CPPUNIT_ASSERT_EQUAL(true, ufs->propagate(solver()));
		CPPUNIT_ASSERT_EQUAL(true, solver().isFalse(ctx.symbolTable()[4].lit));
		LitVec r;
		solver().reason(~ctx.symbolTable()[4].lit, r);
		CPPUNIT_ASSERT(r.size() == 1 && r[0] == ~ctx.symbolTable()[5].lit);
	}
	
	void testNtExtendedFalse() {
		// {z}.
		// r :- 2 {x, y, s}
		// s :- r, z.
		// r :- s, z.
		// x :- not z.
		// y :- not z.
		builder.start(ctx, LogicProgram::AspOptions().noEq())
			.setAtomName(1, "x").setAtomName(2, "y").setAtomName(3, "z").setAtomName(4, "r").setAtomName(5, "s")
			.startRule(CHOICERULE).addHead(3).endRule() // {z}.
			.startRule().addHead(1).addToBody(3,false).endRule()
			.startRule().addHead(2).addToBody(3,false).endRule()
			.startRule(CONSTRAINTRULE, 2).addHead(4).addToBody(1, true).addToBody(2, true).addToBody(5,true).endRule()
			.startRule().addHead(5).addToBody(4,true).addToBody(3,true).endRule()
			.startRule().addHead(4).addToBody(5,true).addToBody(3,true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		attachUfs();
		
		solver().assume(ctx.symbolTable()[3].lit);
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(true, ufs->propagate(solver()));
		CPPUNIT_ASSERT(solver().numVars() == solver().numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, solver().isFalse(ctx.symbolTable()[4].lit));
		CPPUNIT_ASSERT_EQUAL(true, solver().isFalse(ctx.symbolTable()[5].lit));

		solver().backtrack();
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(true, ufs->propagate(solver()));
		CPPUNIT_ASSERT(solver().numVars() == solver().numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, solver().isTrue(ctx.symbolTable()[4].lit));
		CPPUNIT_ASSERT_EQUAL(true, solver().isFalse(ctx.symbolTable()[5].lit));
	}

	void testDependentExtReason() {
		// {z, q, r}.
		// x :- not q.
		// x :- 2 {x, y, z}.
		// x :- y, z.
		// y :- x, r.
		builder.start(ctx, LogicProgram::AspOptions().noEq())
			.setAtomName(1, "x").setAtomName(2, "y").setAtomName(3, "z").setAtomName(4, "q").setAtomName(5, "r")
			.startRule(CHOICERULE).addHead(3).addHead(4).addHead(5).endRule()
			.startRule().addHead(1).addToBody(4,false).endRule()
			.startRule(CONSTRAINTRULE, 2).addHead(1).addToBody(1, true).addToBody(2, true).addToBody(3, true).endRule()
			.startRule().addHead(1).addToBody(2,true).addToBody(3, true).endRule()
			.startRule().addHead(2).addToBody(1,true).addToBody(5, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		attachUfs();
		
		// assume ~B1, where B1 = 2 {x, y, z}
		const SharedDependencyGraph::AtomNode& a = ufs->graph()->getAtom(builder.getAtom(1)->id());
		Literal x = ufs->graph()->getBody(a.body(1)).lit;

		solver().assume(~x);
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()) && ufs->propagate(solver()));
		CPPUNIT_ASSERT_EQUAL(value_free, solver().value(ctx.symbolTable()[1].lit.var()));
		CPPUNIT_ASSERT_EQUAL(value_free, solver().value(ctx.symbolTable()[2].lit.var()));
		// B1
		CPPUNIT_ASSERT_EQUAL(1u, solver().numAssignedVars());
		
		// assume q
		solver().assume(ctx.symbolTable()[4].lit);
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		// B1 + q (hence {not q})
		CPPUNIT_ASSERT_EQUAL(2u, solver().numAssignedVars());

		// U = {x, y}.
		CPPUNIT_ASSERT_EQUAL(true, ufs->propagate(solver()));
		CPPUNIT_ASSERT_EQUAL(true, solver().isFalse(ctx.symbolTable()[1].lit));
		CPPUNIT_ASSERT_EQUAL(true, solver().isFalse(ctx.symbolTable()[2].lit));
		Literal extBody = ufs->graph()->getBody(a.body(0)).lit;
		LitVec r;
		solver().reason(~ctx.symbolTable()[1].lit, r);
		CPPUNIT_ASSERT(r.size() == 1u && r[0] == ~extBody);
	}

	void testEqBodyDiffType() { 
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "x").setAtomName(5,"y")
			.startRule(CHOICERULE).addHead(1).addHead(4).addHead(5).endRule()
			.startRule(CHOICERULE).addHead(2).addToBody(1,true).endRule()
			.startRule().addHead(3).addToBody(1,true).endRule()
			.startRule().addHead(2).addToBody(3,true).addToBody(4, true).endRule()
			.startRule().addHead(3).addToBody(2,true).addToBody(5,true).endRule()
		.endProgram();
		CPPUNIT_ASSERT(builder.stats.sccs == 1);
		attachUfs();
		
		solver().assume(~ctx.symbolTable()[1].lit);
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(true, ufs->propagate(solver()));
		CPPUNIT_ASSERT_EQUAL(true, solver().isFalse(ctx.symbolTable()[2].lit));
		CPPUNIT_ASSERT_EQUAL(true, solver().isFalse(ctx.symbolTable()[3].lit));
	}

	void testChoiceCardInterplay() {  
		builder.start(ctx, LogicProgram::AspOptions().noEq())
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "x")
			.startRule(CHOICERULE).addHead(4).endRule() // {x}.
			.startRule(CHOICERULE).addHead(1).addToBody(4, true).endRule()  // {a} :- x.
			.startRule(CONSTRAINTRULE,1).addHead(2).addToBody(1, true).addToBody(3, true).endRule() // b :- 1{a,c}
			.startRule().addHead(3).addToBody(2,true).endRule() // c :- b.
			.startRule(CHOICERULE).addHead(1).addToBody(3,true).endRule() // {a} :- c.
		.endProgram();
		CPPUNIT_ASSERT(builder.stats.sccs == 1);
		attachUfs();
		
		solver().assume(~ctx.symbolTable()[1].lit);
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(true, ufs->propagate(solver()));
		CPPUNIT_ASSERT_EQUAL(true, solver().isFalse(ctx.symbolTable()[2].lit));
		CPPUNIT_ASSERT_EQUAL(true, solver().isFalse(ctx.symbolTable()[3].lit));
	}

	void testCardInterplayOnBT() {  
		builder.start(ctx, LogicProgram::AspOptions().noEq())
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "d").setAtomName(5,"z")
			.startRule(CHOICERULE).addHead(1).addHead(5).endRule()                                  // {a,z}.
			.startRule(CONSTRAINTRULE,1).addHead(2).addToBody(1, true).addToBody(3, true).endRule() // b :- 1{a,c}
			.startRule(BASICRULE).addHead(2).addToBody(4, true).endRule()                           // b :- d.
			.startRule(BASICRULE).addHead(4).addToBody(2, true).endRule()                           // d :- b.
			.startRule(BASICRULE).addHead(4).addToBody(5, true).endRule()                           // d :- z.
			.startRule(BASICRULE).addHead(3).addToBody(2,true).addToBody(4,true).endRule()          // c :- b,d.      
		.endProgram();
		CPPUNIT_ASSERT(builder.stats.sccs == 1);
		attachUfs();
		
		solver().assume(~ctx.symbolTable()[1].lit);
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()) && ufs->propagate(solver()));
		CPPUNIT_ASSERT_EQUAL(false, solver().isFalse(ctx.symbolTable()[2].lit));
		CPPUNIT_ASSERT_EQUAL(false, solver().isFalse(ctx.symbolTable()[3].lit));
		solver().undoUntil(0);
		
		solver().assume(~ctx.symbolTable()[5].lit);
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()) && ufs->propagate(solver()));
		CPPUNIT_ASSERT_EQUAL(false, solver().isFalse(ctx.symbolTable()[2].lit));
		CPPUNIT_ASSERT_EQUAL(false, solver().isFalse(ctx.symbolTable()[3].lit));
	}
	
	void testInitNoSource() {
		builder.start(ctx, LogicProgram::AspOptions().noEq())
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "x")
			.startRule(CHOICERULE).addHead(3).endRule()                                  // {x}.
			.startRule(CHOICERULE).addHead(1).addHead(2).addToBody(3, true).endRule()    // {a,b} :- x.
			.startRule(BASICRULE).addHead(1).addToBody(2, true).endRule()                // a :- b.
			.startRule(BASICRULE).addHead(2).addToBody(1, true).endRule()                // b :- a.
		.endProgram();
		CPPUNIT_ASSERT(builder.stats.sccs == 1);
		
		solver().force(~ctx.symbolTable()[3].lit);
		attachUfs();
		CPPUNIT_ASSERT(solver().isFalse(ctx.symbolTable()[1].lit));
	}

	void testIncrementalUfs() {
		builder.start(ctx, LogicProgram::AspOptions().noEq());
		// I1:
		// a :- not b.
		// b :- not a.
		// freeze(c).
		builder.updateProgram();
		builder.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c")
			.startRule().addHead(1).addToBody(2, false).endRule()
			.startRule().addHead(2).addToBody(1, false).endRule()
			.freeze(3)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.sccGraph.get() == 0);
		
		// I2:
		// {c, z}
		// x :- not c.
		// x :- y, z.
		// y :- x, z.
		builder.updateProgram();
		builder.setAtomName(4, "x").setAtomName(5, "y").setAtomName(6, "z")
			.startRule(CHOICERULE).addHead(3).addHead(6).endRule()
			.startRule().addHead(4).addToBody(3, false).endRule()
			.startRule().addHead(4).addToBody(5, true).addToBody(6, true).endRule()
			.startRule().addHead(5).addToBody(4, true).addToBody(6, true).endRule()
			.unfreeze(3)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(6u == ctx.sccGraph.get()->nodes());
		CPPUNIT_ASSERT(1 == builder.stats.sccs);
		attachUfs();
		CPPUNIT_ASSERT(6u == ufs->nodes());

		// I3:
		// a :- x, not r.
		// r :- not a.
		// a :- b.
		// b :- a, not z.
		builder.updateProgram();
		builder.setAtomName(7, "a").setAtomName(8, "b").setAtomName(9, "r")
			.startRule().addHead(7).addToBody(4, true).addToBody(9, false).endRule()
			.startRule().addHead(9).addToBody(7, false).endRule()
			.startRule().addHead(7).addToBody(8, true).endRule()
			.startRule().addHead(8).addToBody(7, true).addToBody(6, false).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(11u == ctx.sccGraph.get()->nodes());
		CPPUNIT_ASSERT(1 == builder.stats.sccs);
		ctx.endInit();
		CPPUNIT_ASSERT(11u == ufs->nodes());
		CPPUNIT_ASSERT(builder.getAtom(7)->scc() != builder.getAtom(4)->scc());
	}

	void testInitialStopConflict() {
		builder.start(ctx);
		// I1:
		// {x,y}.
		// a :- {x, y}.
		// a :- b,y.
		// b :- a,y.
		builder.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "x").setAtomName(4, "y")
			.startRule(CHOICERULE).addHead(3).addHead(4).endRule()
			.startRule().addHead(1).addToBody(3, true).addToBody(4, true).endRule()
			.startRule().addHead(1).addToBody(2, true).addToBody(4, true).endRule()
			.startRule().addHead(2).addToBody(1, true).addToBody(4, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(builder.stats.sccs == 1);
		struct M : PostPropagator {			
			uint32 priority() const { return priority_reserved_msg; }
			bool propagateFixpoint(Solver& s, PostPropagator*) {
				s.setStopConflict();
				return false;
			}
		} m;
		solver().addPost(&m);
		ctx.addUnary(~builder.getAtom(3)->literal());
		attachUfs();
		CPPUNIT_ASSERT(solver().hasStopConflict());
		solver().removePost(&m);
		solver().popRootLevel();
		solver().propagate();
		CPPUNIT_ASSERT(solver().isFalse(builder.getAtom(3)->literal()));
		CPPUNIT_ASSERT(solver().isFalse(builder.getAtom(1)->literal()) && solver().isFalse(builder.getAtom(2)->literal()));
	}

	void testIncrementalLearnFact() {
		builder.start(ctx);
		builder.update();
		// I1:
		// {x,y}.
		// a :- {x, y}.
		// a :- b,y.
		// b :- a,y.
		builder.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "x").setAtomName(4, "y")
			.startRule(CHOICERULE).addHead(3).addHead(4).endRule()
			.startRule().addHead(1).addToBody(3, true).addToBody(4, true).endRule()
			.startRule().addHead(1).addToBody(2, true).addToBody(4, true).endRule()
			.startRule().addHead(2).addToBody(1, true).addToBody(4, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		attachUfs();
		builder.update();
		builder.endProgram();
		ctx.addUnary(~builder.getAtom(3)->literal());
		CPPUNIT_ASSERT(solver().propagate());
		CPPUNIT_ASSERT(ctx.endInit());
		CPPUNIT_ASSERT(solver().isFalse(builder.getAtom(3)->literal()));
		CPPUNIT_ASSERT(solver().isFalse(builder.getAtom(1)->literal()) && solver().isFalse(builder.getAtom(2)->literal()));
	}

	void testDetachRemovesWatches() {
		builder.start(ctx, LogicProgram::AspOptions().noEq())
			.setAtomName(1, "x").setAtomName(2, "y").setAtomName(3, "z").setAtomName(4, "q").setAtomName(5, "r")
			.startRule(CHOICERULE).addHead(3).addHead(4).addHead(5).endRule()
			.startRule().addHead(1).addToBody(4,false).endRule()
			.startRule(CONSTRAINTRULE, 2).addHead(1).addToBody(1, true).addToBody(2, true).addToBody(3, true).endRule()
			.startRule().addHead(1).addToBody(2,true).addToBody(3, true).endRule()
			.startRule().addHead(2).addToBody(1,true).addToBody(5, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		ctx.endInit();
		uint32 numW = 0;
		for (uint32 i = 1; i <= solver().numVars(); ++i) {
			numW += solver().numWatches(posLit(i));
			numW += solver().numWatches(negLit(i));
		}
		solver().addPost(ufs.release());
		ufs->destroy(&solver(), true);
		CPPUNIT_ASSERT(!solver().getPost(PostPropagator::priority_reserved_ufs));
		for (uint32 i = 1; i <= solver().numVars(); ++i) {
			numW -= solver().numWatches(posLit(i));
			numW -= solver().numWatches(negLit(i));
		}
		CPPUNIT_ASSERT(numW == 0);
	}
	
	void testApproxUfs() {
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "d").setAtomName(5,"e")
			.startRule(DISJUNCTIVERULE).addHead(1).addHead(2).endRule() // a | b.
			.startRule(DISJUNCTIVERULE).addHead(3).addHead(4).endRule() // c | d.
			.startRule(DISJUNCTIVERULE).addHead(3).addHead(5).addToBody(2, true).endRule() // c | e :- b.
			.startRule(DISJUNCTIVERULE).addHead(2).addHead(4).addToBody(3, true).endRule() // b | d :- c.
			.startRule().addHead(3).addToBody(4,true).addToBody(2, false).endRule() // c :- d, not b.
			.startRule().addHead(3).addToBody(5,true).endRule()                     // c :- e.
			.startRule().addHead(4).addToBody(5,true).addToBody(1, false).endRule() // d :- e, not a.
			.startRule().addHead(5).addToBody(3,true).addToBody(4, true).endRule()  // e :- c, d.
		.endProgram();
		CPPUNIT_ASSERT(builder.stats.sccs == 1);
		CPPUNIT_ASSERT(builder.getAtom(1)->scc() == PrgNode::noScc);
		CPPUNIT_ASSERT(5u == ctx.sccGraph.get()->numAtoms());
		CPPUNIT_ASSERT(8u == ctx.sccGraph.get()->numBodies());
		attachUfs();
		CPPUNIT_ASSERT_EQUAL(true, solver().assume(ctx.symbolTable()[2].lit) && solver().propagate());
		solver().assume(ctx.symbolTable()[3].lit);
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		
		CPPUNIT_ASSERT(solver().value(ctx.symbolTable()[4].lit.var()) == value_free);
		CPPUNIT_ASSERT_EQUAL(true, ufs->propagate(solver()));
		CPPUNIT_ASSERT_MESSAGE("TODO: Implement approx. ufs!", solver().isFalse(ctx.symbolTable()[4].lit));
		
	}
private:
	SharedContext ctx;
	SingleOwnerPtr<WrapDefaultUnfoundedCheck> ufs;
	LogicProgram builder;
	void attachUfs() {
		solver().addPost(ufs.release());
		ctx.endInit();
	}
	void setupSimpleProgram() {
		builder.startProgram(ctx);
		builder
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "f")
			.setAtomName(5, "x").setAtomName(6, "y").setAtomName(7, "z")
			.startRule(CHOICERULE).addHead(5).addHead(6).addHead(7).addHead(3).endRule()
			.startRule().addHead(2).addToBody(1, true).endRule()                    // b :- a.
			.startRule().addHead(1).addToBody(2, true).addToBody(4, true).endRule() // a :- b,f.
			.startRule().addHead(4).addToBody(1, true).addToBody(3, true).endRule() // f :- a,c.
			.startRule().addHead(1).addToBody(5, false).endRule()                   // a :- not x.
			.startRule().addHead(2).addToBody(7, false).endRule()                   // b :- not z.
			.startRule().addHead(4).addToBody(6, false).endRule()                   // f :- not y.
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		attachUfs();
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
	}
};
CPPUNIT_TEST_SUITE_REGISTRATION(UnfoundedCheckTest);
} } 
