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
#include <clasp/heuristics.h>
#include <clasp/lookahead.h>
#include <clasp/logic_program.h>
#include <clasp/clause.h>
#include <clasp/solver.h>
namespace Clasp { namespace Test {
using namespace Clasp::Asp;
class DecisionHeuristicTest : public CppUnit::TestFixture {
  CPPUNIT_TEST_SUITE(DecisionHeuristicTest);
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
	CPPUNIT_TEST(testDomPrio3);
	CPPUNIT_TEST(testDomInit);
	CPPUNIT_TEST(testDomInc);
	CPPUNIT_TEST(testDomIncPrio);
	CPPUNIT_TEST(testDomIncDynPrio);
	CPPUNIT_TEST(testDomReinit);
	CPPUNIT_TEST(testDomMinBug);
	CPPUNIT_TEST(testDomSameVar);

	CPPUNIT_TEST(testDomEqAtomLevel);
	CPPUNIT_TEST(testDomEqAtomSign);
	CPPUNIT_TEST(testDomCompAtomLevel);
	CPPUNIT_TEST(testDomCompAtomSign);
	CPPUNIT_TEST(testDomCompAtomTF);

	CPPUNIT_TEST(testDomDefault);

	CPPUNIT_TEST(testDomAtomicPrio);
	CPPUNIT_TEST(testDomEqVarDiffLevel);
	CPPUNIT_TEST(testDomEqVarDiffLevelInc);
	CPPUNIT_TEST(testDomEqVarDiffLevelCond);

	CPPUNIT_TEST_SUITE_END();

	LogicProgram lp;
public:
	void testBodyLookahead() {
		SharedContext ctx;
		Solver& s = ctx.pushSolver();
		lpAdd(lp.start(ctx, LogicProgram::AspOptions().noEq().noScc()),
			"x1 :- not x1.\n"
			"x1 :- not x2, not x5.\n"
			"x2 :- not x5.\n"
			"x5 :- not x2.\n"
			"x1 :- not x3, not x6.\n"
			"x3 :- not x6.\n"
			"x6 :- not x3.\n"
			"x1 :- not x4, not x7.\n"
			"x4 :- not x7.\n"
			"x7 :- not x4.\n");

		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		s.addPost(new Lookahead(Lookahead::Params(Var_t::Body).addImps(false)));
		CPPUNIT_ASSERT_EQUAL(false, ctx.attach(s));
		ctx.detach(s, true);
		s.addPost(new Lookahead(Lookahead::Params(Var_t::Atom).addImps(false)));
		CPPUNIT_ASSERT_EQUAL(true, ctx.attach(s));
		ctx.detach(s, true);
		s.addPost(new Lookahead(Lookahead::Params(Var_t::Hybrid).addImps(false)));
		CPPUNIT_ASSERT_EQUAL(false, ctx.attach(s));
	}
	void testAtomLookahead() {
		SharedContext ctx;
		Solver& s = ctx.pushSolver();
		lpAdd(lp.start(ctx, LogicProgram::AspOptions().noEq().noScc()),
			"x1 :- x2, x3, x4, not x1.\n"
			"x2 :- not x5.\n"
			"x2 :- not x8.\n"
			"x5 :- not x8.\n"
			"x8 :- not x5.\n"
			"x3 :- not x6.\n"
			"x3 :- not x9.\n"
			"x6 :- not x9.\n"
			"x9 :- not x6.\n"
			"x4 :- not x7.\n"
			"x4 :- not x10.\n"
			"x7 :- not x10.\n"
			"x10 :- not x7.\n");

		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		Lookahead::Params p; p.addImps(false);
		s.addPost(new Lookahead(p.lookahead(Var_t::Body)));
		CPPUNIT_ASSERT_EQUAL(true, ctx.attach(s));
		ctx.detach(s, true);
		s.addPost(new Lookahead(p.lookahead(Var_t::Atom)));
		CPPUNIT_ASSERT_EQUAL(false, ctx.attach(s));
		ctx.detach(s, true);
		s.addPost(new Lookahead(p.lookahead(Var_t::Hybrid)));
		CPPUNIT_ASSERT_EQUAL(false, ctx.attach(s));
	}

	void testLookaheadBugNoSimplify() {
		UnitHeuristic unit;
		SharedContext ctx;
		ctx.master()->setHeuristic(&unit, Ownership_t::Retain);
		Literal a = posLit(ctx.addVar(Var_t::Atom));
		Literal b = posLit(ctx.addVar(Var_t::Atom));
		Literal e = posLit(ctx.addVar(Var_t::Atom));
		Solver& s = ctx.startAddConstraints(10);
		ctx.addBinary(a,  b);
		s.addPost(new Lookahead(Var_t::Atom));
		ctx.endInit();
		ctx.addBinary(a, ~b);
		s.assume(e) && s.propagate();
		CPPUNIT_ASSERT(unit.select(s));
		CPPUNIT_ASSERT(s.isTrue(a));
		CPPUNIT_ASSERT(s.seen(a.var()));
		CPPUNIT_ASSERT(s.decisionLevel() == 1);
	}
	void testLookaheadBugDepsNotCleared() {
		UnitHeuristic unit;
		SharedContext ctx;
		ctx.master()->setHeuristic(&unit, Ownership_t::Retain);
		Literal a = posLit(ctx.addVar(Var_t::Atom));
		Literal b = posLit(ctx.addVar(Var_t::Atom));
		Literal c = posLit(ctx.addVar(Var_t::Atom));
		Literal e = posLit(ctx.addVar(Var_t::Atom));
		Literal f = posLit(ctx.addVar(Var_t::Atom));
		Solver& s = ctx.startAddConstraints();
		ctx.addBinary(a, b);
		ctx.addBinary(b, c);
		ctx.addBinary(c, f);
		ctx.addUnary(e);
		s.addPost(new Lookahead(Var_t::Atom));
		ctx.endInit();
		// Assume without using lookahead (e.g. a random choice)
		s.assume(b);
		s.propagate();
		// Deps not cleared
		CPPUNIT_ASSERT(unit.select(s));
		CPPUNIT_ASSERT(s.isFalse(c) || s.isFalse(f));
	}
	void testLookaheadBugNoDeps() {
		UnitHeuristic unit;
		SharedContext ctx;
		ctx.master()->setHeuristic(&unit, Ownership_t::Retain);
		Literal a = posLit(ctx.addVar(Var_t::Atom));
		Literal b = posLit(ctx.addVar(Var_t::Atom));
		Literal c = posLit(ctx.addVar(Var_t::Atom));
		Literal e = posLit(ctx.addVar(Var_t::Atom));
		Solver& s = ctx.startAddConstraints();
		s.addPost(new Lookahead(Var_t::Atom));
		ctx.addBinary(a, b);
		ctx.addBinary(b, c);
		ctx.addUnary(e);
		ctx.endInit();
		CPPUNIT_ASSERT(unit.select(s));
		CPPUNIT_ASSERT(s.isFalse(b));
		s.undoUntil(0);
		s.simplify();
		CPPUNIT_ASSERT(unit.select(s));
		CPPUNIT_ASSERT(s.isFalse(b));
	}
	void testLookaheadBugNoNant() {
		Clasp::Lookahead::Params p(Var_t::Atom);
		p.restrictNant = true;
		UnitHeuristic unit;
		SharedContext ctx;
		ctx.master()->setHeuristic(&unit, Ownership_t::Retain);
		Literal a = posLit(ctx.addVar(Var_t::Atom));
		Literal b = posLit(ctx.addVar(Var_t::Atom));
		Literal c = posLit(ctx.addVar(Var_t::Atom));
		Solver& s = ctx.startAddConstraints();
		s.addPost(new Lookahead(p));
		ctx.addBinary(a, b);
		ctx.addBinary(b, c);
		ctx.addBinary(~a, ~b);
		ctx.addBinary(~b, ~c);
		ctx.endInit();
		uint32 n = s.numFreeVars();
		CPPUNIT_ASSERT(unit.select(s) && s.numFreeVars() != n);
	}

	void testLookaheadStopConflict() {
		UnitHeuristic unit;
		SharedContext ctx;
		ctx.master()->setHeuristic(&unit, Ownership_t::Retain);
		Literal a = posLit(ctx.addVar(Var_t::Atom));
		Literal b = posLit(ctx.addVar(Var_t::Atom));
		Solver& s = ctx.startAddConstraints();
		ctx.addBinary(a, b);
		s.addPost(new Lookahead(Var_t::Atom));
		ctx.endInit();
		struct StopConflict : public PostPropagator {
			bool propagateFixpoint(Solver& s, PostPropagator*) { s.setStopConflict(); return false; }
			uint32 priority() const   { return PostPropagator::priority_class_simple; }
		}* x = new StopConflict;
		s.addPost(x);
		CPPUNIT_ASSERT(!unit.select(s) && s.hasConflict());
		CPPUNIT_ASSERT(s.search(0,0) == value_false);
	}

	void testBerkmin() {
		ClaspBerkmin berkmin;
		SharedContext ctx;
		ctx.master()->setHeuristic(&berkmin, Ownership_t::Retain);
		Literal a = posLit(ctx.addVar(Var_t::Atom));
		Literal b = posLit(ctx.addVar(Var_t::Atom));
		Literal c = posLit(ctx.addVar(Var_t::Atom));
		Literal d = posLit(ctx.addVar(Var_t::Atom));
		Literal e = posLit(ctx.addVar(Var_t::Atom));
		Literal f = posLit(ctx.addVar(Var_t::Atom));
		Literal g = posLit(ctx.addVar(Var_t::Atom));
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		s.stats.conflicts = 1;
		LitVec up;
		berkmin.updateReason(s, up, Literal() );
		up.push_back(a);
		berkmin.updateReason( s,up,a );
		up.clear();
		up.push_back(b);
		up.push_back(b);
		berkmin.updateReason( s,up,b );
		up.clear();
		berkmin.updateReason( s,up,e );
		s.assume( ~b );
		s.assume( ~c );
		s.assume( ~d );
		ClauseCreator cc(&s);
		cc.start(Constraint_t::Conflict).add(a).add(b).add(c).add(d).end();
		s.undoUntil(0);
		s.assume( ~e );
		s.assume( ~f );
		s.assume( ~g );
		cc.start(Constraint_t::Loop).add(d).add(e).add(f).add(g).end();
		s.undoUntil(0);
		CPPUNIT_ASSERT_EQUAL(0u, s.numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, berkmin.select(s));
		CPPUNIT_ASSERT_EQUAL(b, s.trail().back());	// from conflict clause
		s.propagate();
		CPPUNIT_ASSERT_EQUAL(true, berkmin.select(s));
		CPPUNIT_ASSERT_EQUAL(e, s.trail().back());	// from loop clause
		s.propagate();
		CPPUNIT_ASSERT_EQUAL(true, berkmin.select(s));
		CPPUNIT_ASSERT_EQUAL(a.var(), s.trail().back().var());	// highest activity
	}
	void testVmtf() {
		ClaspVmtf vmtf;
		SharedContext ctx;
		ctx.master()->setHeuristic(&vmtf, Ownership_t::Retain);
		ctx.addVar(Var_t::Atom);
		ctx.addVar(Var_t::Atom);
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		CPPUNIT_ASSERT_EQUAL(true, vmtf.select(s));
		s.propagate();
		CPPUNIT_ASSERT_EQUAL(true, vmtf.select(s));
		s.propagate();
		CPPUNIT_ASSERT_EQUAL(false, vmtf.select(s));
	}

	void testVsids() {
		ClaspVsids vsids;
		SharedContext ctx;
		ctx.master()->setHeuristic(&vsids, Ownership_t::Retain);
		Literal a = posLit(ctx.addVar(Var_t::Atom));
		Literal b = posLit(ctx.addVar(Var_t::Atom));
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		LitVec up;
		up.push_back(a);
		vsids.updateReason( s,up,a );
		CPPUNIT_ASSERT_EQUAL(true, vsids.select(s));
		CPPUNIT_ASSERT_EQUAL(true, s.trail().back() == ~a && s.propagate());
		CPPUNIT_ASSERT_EQUAL(true, vsids.select(s));
		CPPUNIT_ASSERT_EQUAL(true, s.trail().back() == ~b && s.propagate());
		CPPUNIT_ASSERT_EQUAL(false, vsids.select(s));
	}
	void testVsidsAux() {
		ClaspVsids vsids;
		SharedContext ctx;
		ctx.master()->setHeuristic(&vsids, Ownership_t::Retain);
		ctx.addVar(Var_t::Atom);
		ctx.addVar(Var_t::Atom);
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		Var v = s.pushAuxVar();
		LitVec up;
		vsids.updateReason(s,up,posLit(v));
		CPPUNIT_ASSERT_EQUAL(true, vsids.select(s));
		CPPUNIT_ASSERT(s.value(v) != value_free);
		s.popAuxVar(1);
		CPPUNIT_ASSERT_EQUAL(true, vsids.select(s));
		CPPUNIT_ASSERT(s.trail().back().var() != v);
	}

	void testStrangeLookSeq() {
		SharedContext ctx;
		Lookahead::Params p(Var_t::Body); p.limit(3);
		ctx.master()->setHeuristic(UnitHeuristic::restricted(new SelectFirst), Ownership_t::Acquire);
		Literal a = posLit(ctx.addVar(Var_t::Body));
		Literal b = posLit(ctx.addVar(Var_t::Atom));
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
		Lookahead::Params p(Var_t::Atom); p.limit(2);
		ctx.master()->setHeuristic(UnitHeuristic::restricted(new SelectFirst), Ownership_t::Acquire);
		Literal a = posLit(ctx.addVar(Var_t::Atom));
		Literal b = posLit(ctx.addVar(Var_t::Atom));
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
		Lookahead::Params p(Var_t::Atom); p.limit(3);
		ctx.master()->setHeuristic(UnitHeuristic::restricted(new SelectFirst), Ownership_t::Acquire);
		Literal a = posLit(ctx.addVar(Var_t::Atom));
		Literal b = posLit(ctx.addVar(Var_t::Atom));
		posLit(ctx.addVar(Var_t::Atom));
		posLit(ctx.addVar(Var_t::Atom));
		Solver& s = ctx.startAddConstraints();
		s.addPost(new Lookahead(p));
		ctx.addBinary(a, b);
		ctx.endInit();
		bool x = ctx.master()->decideNextBranch();
		CPPUNIT_ASSERT(x == true && s.decisionLevel() == 1);
		s.propagate();
		CPPUNIT_ASSERT(s.getPost(PostPropagator::priority_reserved_look) != 0);
		s.setHeuristic(new SelectFirst, Ownership_t::Acquire);
		while (s.getPost(PostPropagator::priority_reserved_look) != 0) {
			s.propagate();
			s.decideNextBranch();
		}
	}
	void testDomSignPos() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);
		Solver& s = *ctx.master();
		Var a = 1;
		lp.start(ctx).addRule(Head_t::Choice, Potassco::toSpan(&a, 1), Potassco::toSpan<Potassco::Lit_t>());
		lp.addDomHeuristic(a, DomModType::Sign, 1, 1);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());

		CPPUNIT_ASSERT(s.decideNextBranch());
		CPPUNIT_ASSERT(s.isTrue(lp.getLiteral(a)));
	}
	void testDomSignNeg() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);
		Solver& s = *ctx.master();
		Var a = 1;
		lp.start(ctx).addRule(Head_t::Choice, Potassco::toSpan(&a, 1), Potassco::toSpan<Potassco::Lit_t>());
		lp.addDomHeuristic(a, DomModType::Sign, -1, 1);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());

		CPPUNIT_ASSERT(s.decideNextBranch());
		CPPUNIT_ASSERT(s.isTrue(~lp.getLiteral(a)));
	}
	void testDomSignInv() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);
		Solver& s = *ctx.master();
		Var a = 1;
		lpAdd(lp.start(ctx), "a :- not b.\n"
			"b :- not a.\n");
		lp.addDomHeuristic(a, DomModType::Sign, 1, 1);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());

		CPPUNIT_ASSERT(s.decideNextBranch());
		CPPUNIT_ASSERT(s.isTrue(lp.getLiteral(a)));
	}
	void testDomLevel() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);
		Solver& s = *ctx.master();
		Var a = 1, b = 2;
		lpAdd(lp.start(ctx), "{a;b}.");
		lp.addDomHeuristic(a, DomModType::Sign, 1, 1);
		lp.addDomHeuristic(b, DomModType::Sign, 1, 1);
		lp.addDomHeuristic(a, DomModType::Level, 10, 10);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());

		CPPUNIT_ASSERT(s.decideNextBranch());
		CPPUNIT_ASSERT(s.isTrue(lp.getLiteral(a)));
	}

	void testDomDynamic() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);
		Solver& s = *ctx.master();
		Var a = 1, b = 2, c = 3;
		lpAdd(lp.start(ctx), "{a;b;c}.\n"
			"d :- a, b.\n"
			":- d.\n");

		lp.addDomHeuristic(a, DomModType::Sign, 1, 1);
		lp.addDomHeuristic(b, DomModType::Sign, 1, 1);
		lp.addDomHeuristic(a, DomModType::Level, 10, 10);
		lp.addDomHeuristic(c, DomModType::Sign, 1, 1, b);
		lp.addDomHeuristic(c, DomModType::Sign, -1, 1, Potassco::neg(b));

		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(s.decideNextBranch());
		CPPUNIT_ASSERT(s.isTrue(lp.getLiteral(a)));
		s.propagate();
		CPPUNIT_ASSERT(s.isFalse(lp.getLiteral(b)));

		CPPUNIT_ASSERT(s.decideNextBranch());
		CPPUNIT_ASSERT(s.isTrue(~lp.getLiteral(c)));

		s.clearAssumptions();
		uint32 n = s.numWatches(posLit(2));
		// test removal of watches
		ctx.master()->setHeuristic(new SelectFirst(), Ownership_t::Acquire);
		CPPUNIT_ASSERT_MESSAGE("Heuristic not detached", s.numWatches(posLit(2)) != n);
	}

	void testDomPrio() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);
		Solver& s = *ctx.master();
		LogicProgram api;
		lpAdd(lp.start(ctx), "{a;b;c}.\n"
			"d :- a, b.\n"
			":- d.\n"
			"#heuristic b.         [1@1,sign]\n"
			"#heuristic a.         [10@10,true]\n"
			"#heuristic c.         [1@10,sign]\n"
			"#heuristic c : not b. [-1@20,sign]\n");
		Var a = 1, b = 2, c = 3;
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(s.decideNextBranch());
		CPPUNIT_ASSERT(s.isTrue(lp.getLiteral(a)));
		s.propagate();
		CPPUNIT_ASSERT(s.isFalse(lp.getLiteral(b)));

		CPPUNIT_ASSERT(s.decideNextBranch());
		CPPUNIT_ASSERT(s.isTrue(~lp.getLiteral(c)));
	}
	void testDomPrio2() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);
		Solver& s = *ctx.master();
		lpAdd(lp.start(ctx), "{a;b;c}.\n"
			"d :- a, b.\n"
			":- d.\n"
			"#heuristic b.         [1@1,sign]\n"
			"#heuristic a.         [10@10,true]\n"
			"#heuristic c.         [1@30,sign]\n"
			"#heuristic c : not b. [-1@20,sign]\n");
		Var a = 1, b = 2, c = 3;
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(s.decideNextBranch());
		CPPUNIT_ASSERT(s.isTrue(lp.getLiteral(a)));
		s.propagate();
		CPPUNIT_ASSERT(s.isFalse(lp.getLiteral(b)));
		CPPUNIT_ASSERT(s.decideNextBranch());
		CPPUNIT_ASSERT(s.isTrue(lp.getLiteral(c)));
	}
	void testDomPrio3() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);
		Solver& s = *ctx.master();
		Var b = 2, c = 3;
		lpAdd(lp.start(ctx), "{a;c}.\n"
			"b :- a.\n"
			"#heuristic a.     [1@30,true]\n"
			"#heuristic a.     [1@20,false]\n"
			"#heuristic b.     [2@10,true]\n"
			"#heuristic b : c. [2@25,false]\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		s.assume(lp.getLiteral(c)) && s.propagate();
		CPPUNIT_ASSERT(s.decideNextBranch());
		CPPUNIT_ASSERT(s.isTrue(~lp.getDomLiteral(b)));
		s.undoUntil(0);
	}
	void testDomInit() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);
		Solver& s = *ctx.master();
		Var a = 1, b = 2;
		lpAdd(lp.start(ctx), "{a;b}.\n"
			"#heuristic a. [10@20,init]\n"
			"#heuristic a. [50@10,init]\n"
			"#heuristic b. [10@10,init]\n"
			"#heuristic b. [30@20,init]\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		ctx.heuristic.add(lp.getLiteral(a).var(), DomModType::Init, 21, 20, lit_true());
		ctx.endInit();
		CPPUNIT_ASSERT(s.decideNextBranch());
		CPPUNIT_ASSERT(s.value(lp.getLiteral(b).var()) != value_free);
	}
	void testDomInc() {
		SharedContext ctx;
		Solver& s = *ctx.master();

		Var a = 1, b = 2, c = 3, d = 4, e = 5;
		lp.start(ctx).updateProgram();
		lpAdd(lp, "{a;b;c;d}.\n");
		lp.addDomHeuristic(a, DomModType::Level, 1, 1, c);
		lp.addDomHeuristic(b, DomModType::Level, 1, 1, d);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		uint32 n = s.numWatches(posLit(c));
		DomainHeuristic dom;
		dom.startInit(s);
		dom.endInit(s);
		s.setHeuristic(&dom, Ownership_t::Retain);
		CPPUNIT_ASSERT(s.numWatches(posLit(c)) > n);
		CPPUNIT_ASSERT(lp.updateProgram());
		lpAdd(lp, "{e}.");
		lp.addDomHeuristic(e, DomModType::Level, 1, 1, c);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		s.setHeuristic(new SelectFirst(), Ownership_t::Acquire);
		CPPUNIT_ASSERT_MESSAGE("Heuristic not detached", s.numWatches(posLit(c)) == n);
	}
	void testDomIncPrio() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);
		Solver& s = *ctx.master();
		lp.start(ctx).updateProgram();
		lpAdd(lp, "{a}.");
		Var a = 1, b = 2;
		lp.addDomHeuristic(a, DomModType::False,3, 3);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(s.decideNextBranch() && s.isFalse(lp.getLiteral(a)));
		s.undoUntil(0);
		CPPUNIT_ASSERT(lp.updateProgram());
		lpAdd(lp, "{b}.\n");
		lp.addDomHeuristic(a, DomModType::False, 1, 1);
		lp.addDomHeuristic(b, DomModType::False, 2, 2);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(s.decideNextBranch() && s.isFalse(lp.getLiteral(a)));
	}
	void testDomIncDynPrio() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);
		Solver& s = *ctx.master();
		lp.start(ctx).updateProgram();
		Var a = 1, b = 2;
		lpAdd(lp, "{a;b}.");
		lp.addDomHeuristic(a, DomModType::True, 1, 10);
		lp.addDomHeuristic(a, DomModType::False, 1, 20, b);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(s.decideNextBranch() && s.isTrue(lp.getLiteral(a)));
		s.undoUntil(0);

		CPPUNIT_ASSERT(lp.updateProgram());
		lp.addDomHeuristic(a, DomModType::True, 1, 30);
		lp.addDomHeuristic(b, DomModType::True, 2, 2);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(s.decideNextBranch() && s.isTrue(lp.getLiteral(b)));
		CPPUNIT_ASSERT(s.propagate());
		CPPUNIT_ASSERT(s.decideNextBranch() && s.isTrue(lp.getLiteral(a)));
	}

	void testDomReinit() {
		SharedContext ctx;
		Solver& s = *ctx.master();
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);
		Var b = 2;
		lp.start(ctx).updateProgram();
		lpAdd(lp, "{a;b}.");
		lp.addDomHeuristic(b, DomModType::Level, 1, 1);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(s.decideNextBranch() && s.value(lp.getLiteral(b).var()) != value_free);
		CPPUNIT_ASSERT(lp.updateProgram());
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);
		lpAdd(lp, "{c}.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());

		CPPUNIT_ASSERT(s.decideNextBranch() && s.value(lp.getLiteral(b).var()) != value_free);
	}

	void testDomMinBug() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);

		Var a = 1, b = 2;
		lpAdd(lp.start(ctx), "a :- not b. b :- not a.");
		lp.addDomHeuristic(a, DomModType::False, 1, 1);
		lp.addDomHeuristic(b, DomModType::False, 1, 1);
		LitVec min;
		ctx.heuristic.domRec = &min;
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());

		CPPUNIT_ASSERT(min.size() == 2);
	}

	void testDomSameVar() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);
		Solver& s = *ctx.master();
		Var a = 1, b = 2;
		lpAdd(lp.start(ctx), "a :- not b. b :- not a.");
		lp.addDomHeuristic(a, DomModType::True, 2, 2);
		lp.addDomHeuristic(b, DomModType::True, 1, 1);
		LitVec min;
		ctx.heuristic.domRec = &min;
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(s.decideNextBranch() && s.isTrue(lp.getLiteral(a)));
		CPPUNIT_ASSERT(min.size() == 2);
	}

	void testDomEqAtomLevel() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);
		Solver& s = *ctx.master();
		Var a = 1, b = 2, c = 3;
		lpAdd(lp.start(ctx),
			"{a;c}.\n"
			"b :- a.\n");
		lp.addDomHeuristic(a, DomModType::Level, 1, 3);
		lp.addDomHeuristic(b, DomModType::Level, 3, 2);
		lp.addDomHeuristic(c, DomModType::Level, 2, 1);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(s.decideNextBranch() && s.value(lp.getDomLiteral(b).var()) != value_free);
	}
	void testDomEqAtomSign() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);
		Var a = 1, b = 2;
		lpAdd(lp.start(ctx), "{a}. b :- a.");
		lp.addDomHeuristic(a, DomModType::Sign, 1, 1);
		lp.addDomHeuristic(b, DomModType::Sign,-1, 1);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());

		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->pref(lp.getDomLiteral(a).var()).has(ValueSet::user_value));
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->pref(lp.getDomLiteral(b).var()).has(ValueSet::user_value));
	}
	void testDomCompAtomLevel() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);
		Solver& s = *ctx.master();
		Var a = 1, b = 2, c = 3;
		lpAdd(lp.start(ctx), "{a;c}. b :- not a.");
		lp.addDomHeuristic(a, DomModType::Level, 1, 3);
		lp.addDomHeuristic(b, DomModType::Level, 3, 2);
		lp.addDomHeuristic(c, DomModType::Level, 2, 1);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());

		CPPUNIT_ASSERT(s.decideNextBranch() && s.value(lp.getDomLiteral(b).var()) != value_free);
	}
	void testDomCompAtomSign() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);
		Var a = 1, b = 2;
		lpAdd(lp.start(ctx), "{a}. b :- not a.");
		lp.addDomHeuristic(a, DomModType::Sign, 1, 1);
		lp.addDomHeuristic(b, DomModType::Sign, 1, 1);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());

		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->pref(lp.getDomLiteral(a).var()).has(ValueSet::user_value));
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->pref(lp.getDomLiteral(b).var()).has(ValueSet::user_value));
	}
	void testDomCompAtomTF() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);
		Solver& s = *ctx.master();
		Var a = 1, b = 2;
		lpAdd(lp.start(ctx), "a :- not b. b :- not a. {c}.");
		lp.addDomHeuristic(a, DomModType::True, 10, 10);
		lp.addDomHeuristic(b, DomModType::True, 20, 20);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(s.decideNextBranch() && s.isTrue(lp.getDomLiteral(b)));
	}
	void testDomDefault() {
		SharedContext ctx;
		DomainHeuristic dom;
		dom.setDefaultMod(HeuParams::mod_level, 0);
		ctx.master()->setHeuristic(&dom, Ownership_t::Retain);
		Var v1 = ctx.addVar(Var_t::Atom);
		Var v2 = ctx.addVar(Var_t::Body);
		ctx.startAddConstraints();
		ctx.endInit();
		CPPUNIT_ASSERT(dom.score(v1).level == 1);
		CPPUNIT_ASSERT(dom.score(v2).level == 0);
		ctx.unfreeze();
		dom.setDefaultMod(HeuParams::mod_level, HeuParams::pref_show);
		Var v3 = ctx.addVar(Var_t::Atom);
		ctx.output.add("v1", posLit(v1));
		ctx.output.add("v3", posLit(v3));
		ctx.startAddConstraints();
		ctx.endInit();
		CPPUNIT_ASSERT(dom.score(v1).level == dom.score(v3).level);
		CPPUNIT_ASSERT(dom.score(v2).level == 0);
	}

	// UNSUPPORTED

	void testDomAtomicPrio() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);
		Solver& s = *ctx.master();
		lp.start(ctx).updateProgram();
		Var a = 1, b = 2;
		lpAdd(lp, "{a}. b :- a.");
		lp.addDomHeuristic(a, DomModType::False, 2, 3);
		lp.addDomHeuristic(b, DomModType::False, 1, 1);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(s.decideNextBranch() && s.isFalse(lp.getDomLiteral(a)));
		s.undoUntil(0);
		CPPUNIT_ASSERT(lp.updateProgram());
		lp.addDomHeuristic(b, DomModType::True, 3, 2);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(s.decideNextBranch() && s.isTrue(lp.getDomLiteral(b)));
	}
	void testDomEqVarDiffLevel() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);
		Solver& s = *ctx.master();
		Var a = 1, b = 2, c = 3;
		lp.start(ctx);
		lpAdd(lp, "{a;c}. b :- a.");
		lp.addDomHeuristic(a, DomModType::Level, 2, 1);
		lp.addDomHeuristic(c, DomModType::Level, 2, 1);
		lp.addDomHeuristic(c, DomModType::Init, 10, 1);
		lp.addDomHeuristic(b, DomModType::Init, 20, 1);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(s.value(lp.getLiteral(c).var()) == value_free);
		CPPUNIT_ASSERT(s.decideNextBranch() && s.value(lp.getLiteral(c).var()) != value_free);
	}
	void testDomEqVarDiffLevelInc() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);
		Solver& s = *ctx.master();
		Var a = 1, b = 2, c = 3;
		lp.start(ctx);
		lp.updateProgram();
		lpAdd(lp, "{a;c}. b :- a.");
		lp.addDomHeuristic(a, DomModType::Level, 2, 1);
		lp.addDomHeuristic(c, DomModType::Level, 2, 1);
		lp.addDomHeuristic(c, DomModType::Init, 10, 1);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(s.decideNextBranch() && s.value(lp.getLiteral(c).var()) != value_free);

		s.undoUntil(0);
		CPPUNIT_ASSERT(lp.updateProgram());
		lp.addDomHeuristic(b, DomModType::Init, 20, 1);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(s.decideNextBranch() && s.value(lp.getLiteral(c).var()) != value_free);
	}
	void testDomEqVarDiffLevelCond() {
		SharedContext ctx;
		ctx.master()->setHeuristic(new DomainHeuristic, Ownership_t::Acquire);
		Solver& s = *ctx.master();
		Var a = 1, b = 2, c = 3, d = 4;
		lp.start(ctx);
		lpAdd(lp, "{a;b;c;d}. b :- a.");
		lp.addDomHeuristic(b, DomModType::Init, 40, 1);
		lp.addDomHeuristic(d, DomModType::Init, 50, 1);
		lp.addDomHeuristic(d, DomModType::Sign, 1, 1);
		lp.addDomHeuristic(a, DomModType::True, 2, 1, d);
		lp.addDomHeuristic(c, DomModType::True, 2, 1, d);
		lp.addDomHeuristic(c, DomModType::Init, 30, 1);

		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(s.decideNextBranch() && s.isTrue(lp.getLiteral(d)));
		s.propagate();
		CPPUNIT_ASSERT(s.decideNextBranch() && s.value(lp.getLiteral(c).var()) != value_free);
	}
};

CPPUNIT_TEST_SUITE_REGISTRATION(DecisionHeuristicTest);

} }
