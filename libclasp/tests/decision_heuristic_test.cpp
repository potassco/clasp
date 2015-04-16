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
#include <clasp/heuristics.h>
#include <clasp/lookahead.h>
#include <clasp/logic_program.h>
#include <clasp/clause.h>
#include <clasp/solver.h>
namespace Clasp { namespace Test {
using namespace Clasp::Asp;
class DecisionHeuristicTest : public CppUnit::TestFixture {
  CPPUNIT_TEST_SUITE(DecisionHeuristicTest);
	CPPUNIT_TEST(testTrivial);
	CPPUNIT_TEST(testBodyLookahead);
	CPPUNIT_TEST(testAtomLookahead);
	CPPUNIT_TEST(testLookaheadBugNoSimplify);
	CPPUNIT_TEST(testLookaheadBugDepsNotCleared);
	CPPUNIT_TEST(testLookaheadBugNoDeps);
	CPPUNIT_TEST(testLookaheadBugNoNant);
	CPPUNIT_TEST(testLookaheadStopConflict);

	CPPUNIT_TEST(testBerkmin);
	CPPUNIT_TEST(testVmtf);
	CPPUNIT_TEST(testVsids);
	CPPUNIT_TEST(testVsidsAux);
	CPPUNIT_TEST(testResurrect);
	CPPUNIT_TEST(testStrangeLookSeq);
	CPPUNIT_TEST(testStrangeLookSeq2);
	CPPUNIT_TEST(testRestrictDetach);

	CPPUNIT_TEST(testDomSignPos);
	CPPUNIT_TEST(testDomSignNeg);
	CPPUNIT_TEST(testDomSignInv);

	CPPUNIT_TEST(testDomLevel);
	CPPUNIT_TEST(testDomDynamic);
	CPPUNIT_TEST(testDomPrio);
	CPPUNIT_TEST(testDomPrio2);
	CPPUNIT_TEST(testDomInit);
	CPPUNIT_TEST(testDomInc);
	CPPUNIT_TEST(testDomIncPrio);
	CPPUNIT_TEST(testDomReinit);
	CPPUNIT_TEST(testDomMinBug);
	CPPUNIT_TEST(testDomSignPrio);
	CPPUNIT_TEST(testDomPrefixBug);
	CPPUNIT_TEST(testDomSameVar);
	CPPUNIT_TEST_SUITE_END();
public:
	void testTrivial() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new UnitHeuristic());
		ctx.startAddConstraints();
		CPPUNIT_ASSERT_EQUAL(true, ctx.endInit());
	}
	void testBodyLookahead() {
		SharedContext ctx;
		Solver& s = ctx.addSolver();
		LogicProgram api;
		api.start(ctx, LogicProgram::AspOptions().noEq().noScc())
			.setAtomName(1, "x").setAtomName(2, "a1").setAtomName(3, "a2").setAtomName(4, "a3")
			.setAtomName(5, "b1").setAtomName(6, "b2").setAtomName(7, "b3")
			.startRule().addHead(1).addToBody(1, false).endRule()
			.startRule().addHead(1).addToBody(2, false).addToBody(5, false).endRule()
			.startRule().addHead(2).addToBody(5, false).endRule()
			.startRule().addHead(5).addToBody(2, false).endRule()
			.startRule().addHead(1).addToBody(3, false).addToBody(6, false).endRule()
			.startRule().addHead(3).addToBody(6, false).endRule()
			.startRule().addHead(6).addToBody(3, false).endRule()
			.startRule().addHead(1).addToBody(4, false).addToBody(7, false).endRule()
			.startRule().addHead(4).addToBody(7, false).endRule()
			.startRule().addHead(7).addToBody(4, false).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram() && ctx.endInit());
		s.addPost(new Lookahead(Lookahead::Params(Lookahead::body_lookahead).addImps(false)));
		CPPUNIT_ASSERT_EQUAL(false, ctx.attach(s));
		ctx.detach(s, true);
		s.addPost(new Lookahead(Lookahead::Params(Lookahead::atom_lookahead).addImps(false)));
		CPPUNIT_ASSERT_EQUAL(true, ctx.attach(s));
		ctx.detach(s, true);
		s.addPost(new Lookahead(Lookahead::Params(Lookahead::hybrid_lookahead).addImps(false)));
		CPPUNIT_ASSERT_EQUAL(false, ctx.attach(s));
	}
	void testAtomLookahead() {
		SharedContext ctx;
		Solver& s = ctx.addSolver();
		LogicProgram api;
		api.start(ctx, LogicProgram::AspOptions().noEq().noScc())
			.setAtomName(1, "x").setAtomName(2, "c1").setAtomName(3, "c2").setAtomName(4, "c3")
			.setAtomName(5, "a1").setAtomName(6, "a2").setAtomName(7, "a3")
			.setAtomName(8, "b1").setAtomName(9, "b2").setAtomName(10, "b3")
			.startRule().addHead(1).addToBody(2, true).addToBody(3, true).addToBody(4, true).addToBody(1, false).endRule()
			.startRule().addHead(2).addToBody(5, false).endRule()
			.startRule().addHead(2).addToBody(8, false).endRule()
			.startRule().addHead(5).addToBody(8, false).endRule()
			.startRule().addHead(8).addToBody(5, false).endRule()
			.startRule().addHead(3).addToBody(6, false).endRule()
			.startRule().addHead(3).addToBody(9, false).endRule()
			.startRule().addHead(6).addToBody(9, false).endRule()
			.startRule().addHead(9).addToBody(6, false).endRule()
			.startRule().addHead(4).addToBody(7, false).endRule()
			.startRule().addHead(4).addToBody(10, false).endRule()
			.startRule().addHead(7).addToBody(10, false).endRule()
			.startRule().addHead(10).addToBody(7, false).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram() && ctx.endInit());
		Lookahead::Params p; p.addImps(false);
		s.addPost(new Lookahead(p.lookahead(Lookahead::body_lookahead)));
		CPPUNIT_ASSERT_EQUAL(true, ctx.attach(s));
		ctx.detach(s, true);
		s.addPost(new Lookahead(p.lookahead(Lookahead::atom_lookahead)));
		CPPUNIT_ASSERT_EQUAL(false, ctx.attach(s));
		ctx.detach(s, true);
		s.addPost(new Lookahead(p.lookahead(Lookahead::hybrid_lookahead)));
		CPPUNIT_ASSERT_EQUAL(false, ctx.attach(s));
	}

	void testLookaheadBugNoSimplify() {
		DecisionHeuristic* unit = new UnitHeuristic();
		SharedContext ctx;
		ctx.master()->setHeuristic(unit);
		Literal a = posLit(ctx.addVar(Var_t::atom_var));
		Literal b = posLit(ctx.addVar(Var_t::atom_var));
		Literal e = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints(10);
		ctx.addBinary(a,  b);
		s.addPost(new Lookahead(Lookahead::atom_lookahead));
		ctx.endInit();
		ctx.addBinary(a, ~b);
		s.assume(e) && s.propagate();
		CPPUNIT_ASSERT(unit->select(s));
		CPPUNIT_ASSERT(s.isTrue(a));	
		CPPUNIT_ASSERT(s.seen(a.var()));
		CPPUNIT_ASSERT(s.decisionLevel() == 1);
	}
	void testLookaheadBugDepsNotCleared() {
		DecisionHeuristic* unit = new UnitHeuristic();
		SharedContext ctx;
		ctx.master()->setHeuristic(unit);
		Literal a = posLit(ctx.addVar(Var_t::atom_var));
		Literal b = posLit(ctx.addVar(Var_t::atom_var));
		Literal c = posLit(ctx.addVar(Var_t::atom_var));
		Literal e = posLit(ctx.addVar(Var_t::atom_var));
		Literal f = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		ctx.addBinary(a, b);
		ctx.addBinary(b, c);
		ctx.addBinary(c, f);
		ctx.addUnary(e);
		s.addPost(new Lookahead(Lookahead::atom_lookahead));
		ctx.endInit();
		// Assume without using lookahead (e.g. a random choice)
		s.assume(b);
		s.propagate();
		// Deps not cleared
		CPPUNIT_ASSERT(unit->select(s));
		CPPUNIT_ASSERT(s.isFalse(c) || s.isFalse(f));
	}
	void testLookaheadBugNoDeps() {
		DecisionHeuristic* unit = new UnitHeuristic();
		SharedContext ctx;
		ctx.master()->setHeuristic(unit);
		Literal a = posLit(ctx.addVar(Var_t::atom_var));
		Literal b = posLit(ctx.addVar(Var_t::atom_var));
		Literal c = posLit(ctx.addVar(Var_t::atom_var));
		Literal e = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		s.addPost(new Lookahead(Lookahead::atom_lookahead));
		ctx.addBinary(a, b);
		ctx.addBinary(b, c);
		ctx.addUnary(e);
		ctx.endInit();
		CPPUNIT_ASSERT(unit->select(s));
		CPPUNIT_ASSERT(s.isFalse(b));
		s.undoUntil(0);
		s.simplify();
		CPPUNIT_ASSERT(unit->select(s));
		CPPUNIT_ASSERT(s.isFalse(b));
	}
	void testLookaheadBugNoNant() {
		Clasp::Lookahead::Params p(Lookahead::atom_lookahead);
		p.restrictNant = true;
		DecisionHeuristic* unit = new UnitHeuristic();
		SharedContext ctx;
		ctx.master()->setHeuristic(unit);
		Literal a = posLit(ctx.addVar(Var_t::atom_var));
		Literal b = posLit(ctx.addVar(Var_t::atom_var));
		Literal c = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		s.addPost(new Lookahead(p));
		ctx.addBinary(a, b);
		ctx.addBinary(b, c);
		ctx.addBinary(~a, ~b);
		ctx.addBinary(~b, ~c);
		ctx.endInit();
		uint32 n = s.numFreeVars();
		CPPUNIT_ASSERT(unit->select(s) && s.numFreeVars() != n);
	}
	
	void testLookaheadStopConflict() {
		DecisionHeuristic* unit = new UnitHeuristic();
		SharedContext ctx;
		ctx.master()->setHeuristic(unit);
		Literal a = posLit(ctx.addVar(Var_t::atom_var));
		Literal b = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		ctx.addBinary(a, b);
		s.addPost(new Lookahead(Lookahead::atom_lookahead));
		ctx.endInit();
		struct StopConflict : public PostPropagator {
			bool propagateFixpoint(Solver& s, PostPropagator*) { s.setStopConflict(); return false; }
			uint32 priority() const   { return PostPropagator::priority_class_simple; }
		}* x = new StopConflict;
		s.addPost(x);
		CPPUNIT_ASSERT(!unit->select(s) && s.hasConflict());
		CPPUNIT_ASSERT(s.search(0,0) == value_false);
	}

	void testBerkmin() {
		ClaspBerkmin* berkmin = new ClaspBerkmin(0, HeuParams().other(3).init(1));
		SharedContext ctx;
		ctx.master()->setHeuristic(berkmin);
		Literal a = posLit(ctx.addVar(Var_t::atom_var));
		Literal b = posLit(ctx.addVar(Var_t::atom_var));
		Literal c = posLit(ctx.addVar(Var_t::atom_var));
		Literal d = posLit(ctx.addVar(Var_t::atom_var));
		Literal e = posLit(ctx.addVar(Var_t::atom_var));
		Literal f = posLit(ctx.addVar(Var_t::atom_var));
		Literal g = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		s.stats.conflicts = 1;
		LitVec up;
		berkmin->updateReason(s, up, Literal() );
		up.push_back(a);
		berkmin->updateReason( s,up,a );
		up.clear();
		up.push_back(b);
		up.push_back(b);
		berkmin->updateReason( s,up,b );
		up.clear();
		berkmin->updateReason( s,up,e );
		s.assume( ~b );
		s.assume( ~c );
		s.assume( ~d );
		ClauseCreator cc(&s);
		cc.start(Constraint_t::learnt_conflict).add(a).add(b).add(c).add(d).end();
		s.undoUntil(0);
		s.assume( ~e );
		s.assume( ~f );
		s.assume( ~g );
		cc.start(Constraint_t::learnt_loop).add(d).add(e).add(f).add(g).end();
		s.undoUntil(0);
		CPPUNIT_ASSERT_EQUAL(0u, s.numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, berkmin->select(s));
		CPPUNIT_ASSERT_EQUAL(b, s.trail().back());	// from conflict clause
		s.propagate();
		CPPUNIT_ASSERT_EQUAL(true, berkmin->select(s));
		CPPUNIT_ASSERT_EQUAL(e, s.trail().back());	// from loop clause
		s.propagate();
		CPPUNIT_ASSERT_EQUAL(true, berkmin->select(s));
		CPPUNIT_ASSERT_EQUAL(a.var(), s.trail().back().var());	// highest activity
	}
	void testVmtf() {
		ClaspVmtf* vmtf = new ClaspVmtf;
		SharedContext ctx;
		ctx.master()->setHeuristic(vmtf);
		ctx.addVar(Var_t::atom_var);
		ctx.addVar(Var_t::atom_var);
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		CPPUNIT_ASSERT_EQUAL(true, vmtf->select(s));
		s.propagate();
		CPPUNIT_ASSERT_EQUAL(true, vmtf->select(s));
		s.propagate(); 
		CPPUNIT_ASSERT_EQUAL(false, vmtf->select(s));
	}

	void testVsids() {
		ClaspVsids* vsids = new ClaspVsids;
		SharedContext ctx;
		ctx.master()->setHeuristic(vsids);
		Literal a = posLit(ctx.addVar(Var_t::atom_var));
		Literal b = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		LitVec up;
		up.push_back(a);
		vsids->updateReason( s,up,a );
		CPPUNIT_ASSERT_EQUAL(true, vsids->select(s));
		CPPUNIT_ASSERT_EQUAL(true, s.trail().back() == ~a && s.propagate());
		CPPUNIT_ASSERT_EQUAL(true, vsids->select(s));
		CPPUNIT_ASSERT_EQUAL(true, s.trail().back() == ~b && s.propagate());
		CPPUNIT_ASSERT_EQUAL(false, vsids->select(s));
	}
	void testVsidsAux() {
		ClaspVsids* vsids = new ClaspVsids;
		SharedContext ctx;
		ctx.master()->setHeuristic(vsids);
		ctx.addVar(Var_t::atom_var);
		ctx.addVar(Var_t::atom_var);
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		Var v = s.pushAuxVar();
		LitVec up;
		vsids->updateReason(s,up,posLit(v));
		CPPUNIT_ASSERT_EQUAL(true, vsids->select(s));
		CPPUNIT_ASSERT(s.value(v) != value_free);
		s.popAuxVar(1);
		CPPUNIT_ASSERT_EQUAL(true, vsids->select(s));
		CPPUNIT_ASSERT(s.trail().back().var() != v);
	}

	void testStrangeLookSeq() {
		SharedContext ctx;
		Lookahead::Params p(Lookahead::body_lookahead); p.limit(3);
		ctx.master()->setHeuristic(UnitHeuristic::restricted(new SelectFirst));
		Literal a = posLit(ctx.addVar(Var_t::body_var));
		Literal b = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		s.addPost(new Lookahead(p));
		ctx.endInit();
		s.force(a);
		s.simplify();
		bool x = s.decideNextBranch();
		CPPUNIT_ASSERT(x == true && s.value(b.var()) != value_free);
	}

	void testStrangeLookSeq2() {
		SharedContext ctx;
		Lookahead::Params p(Lookahead::atom_lookahead); p.limit(2);
		ctx.master()->setHeuristic(UnitHeuristic::restricted(new SelectFirst));
		Literal a = posLit(ctx.addVar(Var_t::atom_var));
		Literal b = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		s.addPost(new Lookahead(p));
		ctx.addBinary(a, b);
		ctx.addBinary(a, ~b);
		ctx.addBinary(~a, b);
		ctx.endInit();
		bool x = ctx.master()->decideNextBranch();
		CPPUNIT_ASSERT(x == false && s.decisionLevel() == 0 && s.numFreeVars() == 0);
	}

	void testRestrictDetach() {
		SharedContext ctx;
		Lookahead::Params p(Lookahead::atom_lookahead); p.limit(3);
		ctx.master()->setHeuristic(UnitHeuristic::restricted(new SelectFirst));
		Literal a = posLit(ctx.addVar(Var_t::atom_var));
		Literal b = posLit(ctx.addVar(Var_t::atom_var));
		Literal c = posLit(ctx.addVar(Var_t::atom_var));
		Literal d = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		s.addPost(new Lookahead(p));
		ctx.addBinary(a, b);
		ctx.endInit();
		bool x = ctx.master()->decideNextBranch();
		CPPUNIT_ASSERT(x == true && s.decisionLevel() == 1);
		s.propagate();
		CPPUNIT_ASSERT(s.getPost(PostPropagator::priority_reserved_look) != 0);
		s.setHeuristic(new SelectFirst);
		while (s.getPost(PostPropagator::priority_reserved_look) != 0) {
			s.propagate();
			s.decideNextBranch();
		}
	}

	void testResurrect() {
		/*
		typedef std::pair<const char*, DecisionHeuristic*> Heu;
		Heu heus[3] = {
			Heu("Berkmin", new ClaspBerkmin()),
			Heu("Vmtf", new ClaspVmtf()),
			Heu("Vsids", new ClaspVsids())
		};
		for (uint32 i = 0; i != 3; ++i) {
			SharedContext ctx;
			ctx.master()->strategy.heuristic.reset(heus[i].second);
			Var v1 = ctx.addVar(Var_t::atom_var);
			Var v2 = ctx.addVar(Var_t::atom_var);
			Var v3 = ctx.addVar(Var_t::atom_var);
			ctx.startAddConstraints();
			ctx.endInit();
			Solver& s = *ctx.master();
			s.eliminate(v1, true);
			while (s.strategy.heuristic->select(s) && s.propagate()) { ; }
			CPPUNIT_ASSERT(2u == s.stats.choices);
			CPPUNIT_ASSERT_EQUAL_MESSAGE(heus[i].first, 0u, s.numFreeVars());
			s.eliminate(v1, false);
			CPPUNIT_ASSERT_EQUAL(value_free, s.value(v1));
			CPPUNIT_ASSERT_EQUAL_MESSAGE(heus[i].first, true, s.strategy.heuristic->select(s));
			CPPUNIT_ASSERT_MESSAGE(heus[i].first, value_free != s.value(v1));
		}
		*/
		CPPUNIT_FAIL("TODO - Resurrection not yet supported!");
	}

	void testDomSignPos() {
		DomainHeuristic* dom = new DomainHeuristic;
		SharedContext ctx;
		ctx.master()->setHeuristic(dom);
		Solver& s = *ctx.master();
		LogicProgram api;
		api.start(ctx).setAtomName(1, "a").startRule(Asp::CHOICERULE).addHead(1).endRule();
		addDomRule(api, "_heuristic(a,sign,1)");
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram() && ctx.endInit());
		
		CPPUNIT_ASSERT(dom->select(s));
		CPPUNIT_ASSERT(s.trail().back() == api.getAtom(1)->literal());
	}
	void testDomSignNeg() {
		DomainHeuristic* dom = new DomainHeuristic;
		SharedContext ctx;
		ctx.master()->setHeuristic(dom);
		Solver& s = *ctx.master();
		LogicProgram api;
		api.start(ctx).setAtomName(1, "a").startRule(Asp::CHOICERULE).addHead(1).endRule();
		addDomRule(api, "_heuristic(a,sign,-1)");
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram() && ctx.endInit());
		
		CPPUNIT_ASSERT(dom->select(s));
		CPPUNIT_ASSERT(s.trail().back() == ~api.getAtom(1)->literal());
	}
	void testDomSignInv() {
		DomainHeuristic* dom = new DomainHeuristic;
		SharedContext ctx;
		ctx.master()->setHeuristic(dom);
		Solver& s = *ctx.master();
		LogicProgram api;
		api.start(ctx).setAtomName(1, "a")
			.startRule().addHead(2).addToBody(1, false).endRule()
			.startRule().addHead(1).addToBody(2, false).endRule();
		addDomRule(api, "_heuristic(a,sign,1)");
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram() && ctx.endInit());
		
		CPPUNIT_ASSERT(dom->select(s));
		CPPUNIT_ASSERT(s.isTrue(api.getAtom(1)->literal()));
	}
	void testDomLevel() {
		DomainHeuristic* dom = new DomainHeuristic;
		SharedContext ctx;
		ctx.master()->setHeuristic(dom);
		Solver& s = *ctx.master();
		LogicProgram api;
		api.start(ctx).setAtomName(1, "a").setAtomName(2,"b").startRule(Asp::CHOICERULE).addHead(1).addHead(2).endRule();
		addDomRule(api, "_heuristic(a,sign,1)");
		addDomRule(api, "_heuristic(b,sign,1)");
		addDomRule(api, "_heuristic(a,level,10)");
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram() && ctx.endInit());
		
		CPPUNIT_ASSERT(dom->select(s));
		CPPUNIT_ASSERT(s.trail().back() == api.getAtom(1)->literal());
	}

	void testDomDynamic() {
		DomainHeuristic* dom = new DomainHeuristic;
		SharedContext ctx;
		ctx.master()->setHeuristic(dom);
		Solver& s = *ctx.master();
		LogicProgram api;
		api.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c")
			.startRule(Asp::CHOICERULE).addHead(1).addHead(2).addHead(3).endRule()
			.startRule().addHead(4).addToBody(1, true).addToBody(2,true).endRule()
			.setCompute(4, false);
		addDomRule(api, "_heuristic(a,sign,1)");
		addDomRule(api, "_heuristic(b,sign,1)");
		addDomRule(api, "_heuristic(a,level,10)");
		addDomRule(api, "_heuristic(c,sign,1)", posLit(2));
		addDomRule(api, "_heuristic(c,sign,-1)", negLit(2));
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(dom->select(s));
		CPPUNIT_ASSERT(s.trail().back() == api.getAtom(1)->literal());
		s.propagate();
		CPPUNIT_ASSERT(s.isFalse(api.getAtom(2)->literal()));
		CPPUNIT_ASSERT(dom->select(s));
		CPPUNIT_ASSERT(s.trail().back() == ~api.getAtom(3)->literal());
		s.clearAssumptions();
		uint32 n = s.numWatches(posLit(2));
		// test removal of watches
		ctx.master()->setHeuristic(new SelectFirst());
		CPPUNIT_ASSERT_MESSAGE("Heuristic not detached", s.numWatches(posLit(2)) != n);
	}

	void testDomPrio() {
		DomainHeuristic* dom = new DomainHeuristic;
		SharedContext ctx;
		ctx.master()->setHeuristic(dom);
		Solver& s = *ctx.master();
		LogicProgram api;
		api.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c")
			.startRule(Asp::CHOICERULE).addHead(1).addHead(2).addHead(3).endRule()
			.startRule().addHead(4).addToBody(1, true).addToBody(2,true).endRule()
			.setCompute(4, false);
		addDomRule(api, "_heuristic(b,sign,1)");
		addDomRule(api, "_heuristic(a,true,10)");
		addDomRule(api, "_heuristic(c,sign,1,10)");
		addDomRule(api, "_heuristic(c,sign,-1,20)", negLit(2));
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(dom->select(s));
		CPPUNIT_ASSERT(s.trail().back() == api.getAtom(1)->literal());
		s.propagate();
		CPPUNIT_ASSERT(s.isFalse(api.getAtom(2)->literal()));
		CPPUNIT_ASSERT(dom->select(s));
		CPPUNIT_ASSERT(s.trail().back() == ~api.getAtom(3)->literal());
	}
	void testDomPrio2() {
		DomainHeuristic* dom = new DomainHeuristic;
		SharedContext ctx;
		ctx.master()->setHeuristic(dom);
		Solver& s = *ctx.master();
		LogicProgram api;
		api.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c")
			.startRule(Asp::CHOICERULE).addHead(1).addHead(2).addHead(3).endRule()
			.startRule().addHead(4).addToBody(1, true).addToBody(2,true).endRule()
			.setCompute(4, false);
		addDomRule(api, "_heuristic(b,sign,1)");
		addDomRule(api, "_heuristic(a,true,10)");
		addDomRule(api, "_heuristic(c,sign,1,30)");
		addDomRule(api, "_heuristic(c,sign,-1,20)", negLit(2));
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(dom->select(s));
		CPPUNIT_ASSERT(s.trail().back() == api.getAtom(1)->literal());
		s.propagate();
		CPPUNIT_ASSERT(s.isFalse(api.getAtom(2)->literal()));
		CPPUNIT_ASSERT(dom->select(s));
		CPPUNIT_ASSERT(s.trail().back() == api.getAtom(3)->literal());
	}
	void testDomInit() {
		DomainHeuristic* dom = new DomainHeuristic;
		SharedContext ctx;
		ctx.master()->setHeuristic(dom);
		Solver& s = *ctx.master();
		LogicProgram api;
		api.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule(Asp::CHOICERULE).addHead(1).addHead(2).endRule();
		addDomRule(api, "_heuristic(a,init,10,20)");
		addDomRule(api, "_heuristic(a,init,50,10)");
		addDomRule(api, "_heuristic(b,init,10,10)");
		addDomRule(api, "_heuristic(b,init,30,20)");
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(dom->select(s));
		CPPUNIT_ASSERT(s.trail().back().var() == api.getAtom(2)->var());
	}
	void testDomInc() {
		SharedContext ctx;
		Solver& s = *ctx.master();
		
		LogicProgram api;
		api.start(ctx).updateProgram();
		api.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "x").setAtomName(4, "y")
			.startRule(Asp::CHOICERULE).addHead(1).addHead(2).addHead(3).addHead(4).endRule();
		addDomRule(api, "_heuristic(a,level,1)", posLit(3));
		addDomRule(api, "_heuristic(b,level,1)", posLit(4));
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram() && ctx.endInit());
		uint32 n = s.numWatches(posLit(3));
		DomainHeuristic* dom = new DomainHeuristic;
		dom->startInit(s);
		dom->endInit(s);
		s.setHeuristic(dom);
		CPPUNIT_ASSERT(s.numWatches(posLit(3)) > n);
		CPPUNIT_ASSERT(api.updateProgram());
		Var c = api.newAtom();
		api.setAtomName(c, "c").startRule(Asp::CHOICERULE).addHead(c).endRule();
		addDomRule(api, "_heuristic(c,level,1)", posLit(3));
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram() && ctx.endInit());
		s.setHeuristic(new SelectFirst());
		CPPUNIT_ASSERT_MESSAGE("Heuristic not detached", s.numWatches(posLit(3)) == n);
	}
	void testDomIncPrio() {
		SharedContext ctx;
		Solver& s = *ctx.master();
		
		LogicProgram api;
		api.start(ctx).updateProgram();
		api.setAtomName(1, "a").startRule(Asp::CHOICERULE).addHead(1).endRule();
		addDomRule(api, "_heuristic(a,false,3)");
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram() && ctx.endInit());
		DomainHeuristic* dom = new DomainHeuristic;
		dom->startInit(s);
		dom->endInit(s);
		dom->select(s);
		CPPUNIT_ASSERT(s.isFalse(api.getAtom(1)->literal()));
		s.undoUntil(0);
		CPPUNIT_ASSERT(api.updateProgram());
		Var b = api.newAtom();
		api.setAtomName(b, "b").startRule(Asp::CHOICERULE).addHead(b).endRule();
		addDomRule(api, "_heuristic(a,false,1)");
		addDomRule(api, "_heuristic(b,false,2)");
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram() && ctx.endInit());
		dom->startInit(s);
		dom->endInit(s);
		dom->select(s);
		CPPUNIT_ASSERT(s.isFalse(api.getAtom(1)->literal()));
	}
	void testDomReinit() {
		SharedContext ctx;
		Solver& s = *ctx.master();
		
		LogicProgram api;
		api.start(ctx).updateProgram();
		api.setAtomName(1, "a").setAtomName(2, "b").startRule(Asp::CHOICERULE).addHead(1).addHead(2).endRule();
		addDomRule(api, "_heuristic(b,level,1)");
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram() && ctx.endInit());
		DomainHeuristic* dom = new DomainHeuristic;
		dom->startInit(s);
		dom->endInit(s);
		s.setHeuristic(dom);
		dom->select(s);
		CPPUNIT_ASSERT(s.value(s.sharedContext()->symbolTable()[2].lit.var()) != value_free);
		CPPUNIT_ASSERT(api.updateProgram());
		Var c = api.newAtom();
		api.setAtomName(c, "c").startRule(Asp::CHOICERULE).addHead(c).endRule();
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram() && ctx.endInit());

		dom = new DomainHeuristic;
		dom->startInit(s);
		dom->endInit(s);
		s.setHeuristic(dom);
		dom->select(s);
		CPPUNIT_ASSERT(s.value(s.sharedContext()->symbolTable()[2].lit.var()) != value_free);
	}

	void testDomMinBug() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new DomainHeuristic);
		Solver& s = *ctx.master();
		
		LogicProgram api;
		api.start(ctx).setAtomName(1, "a").setAtomName(2, "b")
			.startRule().addHead(1).addToBody(2, false).endRule()
			.startRule().addHead(2).addToBody(1, false).endRule()
		;
		addDomRule(api, "_heuristic(a,false,1)");
		addDomRule(api, "_heuristic(b,false,1)");
		
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram() && ctx.endInit());

		CPPUNIT_ASSERT(ctx.symbolTable().domLits.size() == 2);
	}
	void testDomSignPrio() {
		SharedContext ctx;
		DecisionHeuristic* dom;
		ctx.master()->setHeuristic(dom = new DomainHeuristic);
		Solver& s = *ctx.master();

		LogicProgram api;
		api.start(ctx).setAtomName(1, "a").setAtomName(2, "b")
			.startRule(Asp::CHOICERULE).addHead(1).addHead(2).endRule()
			;
		// implicit prio
		addDomRule(api, "_heuristic(a,sign,100)");
		addDomRule(api, "_heuristic(a,sign,-10)");
		// explicit prio
		addDomRule(api, "_heuristic(b,sign,100,100)");
		addDomRule(api, "_heuristic(b,sign,-10,10)");

		CPPUNIT_ASSERT_EQUAL(true, api.endProgram() && ctx.endInit());

		Literal a = api.getLiteral(1);
		Literal b = api.getLiteral(2);

		Literal x = dom->doSelect(s);
		s.assume(x) && s.propagate();
		Literal y = dom->doSelect(s);
		s.assume(y) && s.propagate();
		CPPUNIT_ASSERT(x != y);
		CPPUNIT_ASSERT(x == a || x == b);
		CPPUNIT_ASSERT(y == a || y == b);
	}
	void testDomPrefixBug() {
		DomainHeuristic* dom = new DomainHeuristic;
		SharedContext ctx;
		ctx.master()->setHeuristic(dom);
		Solver& s = *ctx.master();
		LogicProgram api;
		api.start(ctx).setAtomName(1, "a").setAtomName(2,"ab").setAtomName(3,"abc").startRule(Asp::CHOICERULE).addHead(1).addHead(2).addHead(3).endRule();
		addDomRule(api, "_heuristic(ab,level,1)");
		addDomRule(api, "_heuristic(ab,factor,2)");
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram() && ctx.endInit());
		const DomScore& scA = dom->score(api.getLiteral(1).var());
		const DomScore& scB = dom->score(api.getLiteral(2).var());
		const DomScore& scC = dom->score(api.getLiteral(3).var());
		CPPUNIT_ASSERT(scA.level < scB.level);
		CPPUNIT_ASSERT(scC.level < scB.level);
		CPPUNIT_ASSERT(scA.factor < scB.factor);
		CPPUNIT_ASSERT(scC.factor < scB.factor);
	}
	void testDomSameVar() {
		DecisionHeuristic* dom = new DomainHeuristic;
		SharedContext ctx;
		ctx.master()->setHeuristic(dom);
		Solver& s = *ctx.master();
		LogicProgram api;
		api.start(ctx).setAtomName(1, "a").setAtomName(2, "b")
			.startRule().addHead(1).addToBody(2, false).endRule()
			.startRule().addHead(2).addToBody(1, false).endRule();
		addDomRule(api, "_heuristic(a,true,2)");
		addDomRule(api, "_heuristic(b,true,1)");
		CPPUNIT_ASSERT_EQUAL(true, api.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(api.getLiteral(1).var() == api.getLiteral(2).var());
		Literal x = dom->doSelect(s);
		CPPUNIT_ASSERT(x == api.getLiteral(1));
	}
	void addDomRule(LogicProgram& prg, const char* heu, Literal pre = posLit(0)) {
		Var h = prg.newAtom();
		prg.setAtomName(h, heu);
		prg.startRule().addHead(h);
		if (pre != posLit(0)) prg.addToBody(pre.var(), pre.sign() == false);
		prg.endRule();
	}
};

CPPUNIT_TEST_SUITE_REGISTRATION(DecisionHeuristicTest);

} } 
