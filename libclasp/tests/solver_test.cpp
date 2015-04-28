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
#include <clasp/clause.h>

namespace Clasp { namespace Test {
using namespace Clasp::mt;
struct TestingConstraint : public LearntConstraint {
	TestingConstraint(bool* del = 0, ConstraintType t = Constraint_t::static_constraint) 
		: type_(t), propagates(0), undos(0), sat(false), keepWatch(true), setConflict(false), deleted(del) {}
	Constraint* cloneAttach(Solver&) { 
		return new TestingConstraint(0, type_);
	}
	PropResult propagate(Solver&, Literal, uint32&) {
		++propagates;
		return PropResult(!setConflict, keepWatch);
	}
	void undoLevel(Solver&) {
		++undos;
	}
	bool simplify(Solver&, bool) { return sat; }
	void reason(Solver&, Literal, LitVec& out) { out = ante; }
	void destroy(Solver* s, bool b) {
		if (deleted) *deleted = true;
		LearntConstraint::destroy(s, b);
	}
	bool locked(const Solver&) const { return false; }
	uint32 isOpen(const Solver&, const TypeSet&, LitVec&) { return 0; }
	static uint32 size() { return uint32(10); }
	ConstraintType type() const { return type_; }
	LitVec ante;
	ConstraintType type_;
	int propagates;
	int undos;
	bool sat;
	bool keepWatch;
	bool setConflict;
	bool* deleted;
};
struct TestingPostProp : public PostPropagator {
	explicit TestingPostProp(bool cfl, uint32 p = PostPropagator::priority_class_simple) : props(0), resets(0), inits(0), prio(p), conflict(cfl), deleteOnProp(false) {}
	bool propagateFixpoint(Solver& s, PostPropagator*) {
		++props;
		bool ok = !conflict;
		if (deleteOnProp) {
			s.removePost(this);
			this->destroy();
		}
		return ok;
	}
	void reset() {
		++resets;
	}
	bool init(Solver&) { ++inits; return true; }
	uint32 priority() const { return prio; }
	int props;
	int resets;
	int inits;
	uint32 prio;
	bool conflict;
	bool deleteOnProp;
};

class SolverTest : public CppUnit::TestFixture {
	CPPUNIT_TEST_SUITE(SolverTest);
	CPPUNIT_TEST(testReasonStore);
	CPPUNIT_TEST(testSingleOwnerPtr);
	CPPUNIT_TEST(testDefaults);
	CPPUNIT_TEST(testVarNullIsSentinel);
	CPPUNIT_TEST(testSolverAlwaysContainsSentinelVar);
	CPPUNIT_TEST(testSolverOwnsConstraints);
	CPPUNIT_TEST(testAddVar);
	CPPUNIT_TEST(testEliminateVar);
	CPPUNIT_TEST(testResurrectVar);
	CPPUNIT_TEST(testCmpScores);
	
	CPPUNIT_TEST(testValueSet);
	CPPUNIT_TEST(testPreferredLitByType);
	CPPUNIT_TEST(testInitSavedValue);
	CPPUNIT_TEST(testReset);
	CPPUNIT_TEST(testForce);
	CPPUNIT_TEST(testNoUpdateOnConsistentAssign);
	CPPUNIT_TEST(testAssume);
	CPPUNIT_TEST(testGetDecision);
	CPPUNIT_TEST(testAddWatch);
	CPPUNIT_TEST(testRemoveWatch);
	CPPUNIT_TEST(testNotifyWatch);
	CPPUNIT_TEST(testKeepWatchOnPropagate);
	CPPUNIT_TEST(testRemoveWatchOnPropagate);
	CPPUNIT_TEST(testWatchOrder);
	CPPUNIT_TEST(testUndoUntil);
	CPPUNIT_TEST(testUndoWatches);
	CPPUNIT_TEST(testPropBinary);
	CPPUNIT_TEST(testPropTernary);
	CPPUNIT_TEST(testRestartAfterUnitLitResolvedBug);
	CPPUNIT_TEST(testEstimateBCP);
	CPPUNIT_TEST(testEstimateBCPLoop);
	CPPUNIT_TEST(testAssertImmediate);
	CPPUNIT_TEST(testPreferShortBfs);

	CPPUNIT_TEST(testPostPropInit);
	CPPUNIT_TEST(testPropagateCallsPostProp);
	CPPUNIT_TEST(testPropagateCallsResetOnConflict);
	CPPUNIT_TEST(testPostpropPriority);
	CPPUNIT_TEST(testPostpropPriorityExt);
	CPPUNIT_TEST(testPostpropRemove);
	CPPUNIT_TEST(testPostpropRemoveOnProp);
	CPPUNIT_TEST(testPostpropBug);
	CPPUNIT_TEST(testPostpropAddAfterInitBug);
	
	CPPUNIT_TEST(testSimplifyRemovesSatBinClauses);
	CPPUNIT_TEST(testSimplifyRemovesSatTernClauses);
	CPPUNIT_TEST(testSimplifyRemovesSatConstraints);
	CPPUNIT_TEST(testRemoveConditional);
	CPPUNIT_TEST(testStrengthenConditional);
	CPPUNIT_TEST(testLearnConditional);


	CPPUNIT_TEST(testResolveUnary);
	CPPUNIT_TEST(testResolveConflict);
	CPPUNIT_TEST(testResolveConflictBounded);

	CPPUNIT_TEST(testClearAssumptions);
	CPPUNIT_TEST(testStopConflict);
	CPPUNIT_TEST(testClearStopConflictResetsBtLevel);

	CPPUNIT_TEST(testSearchKeepsAssumptions);
	CPPUNIT_TEST(testSearchAddsLearntFacts);
	CPPUNIT_TEST(testSearchMaxConflicts);

	CPPUNIT_TEST(testStats);
#if WITH_THREADS
	CPPUNIT_TEST(testLearntShort);
	CPPUNIT_TEST(testLearntShortAreDistributed);
	CPPUNIT_TEST(testAuxAreNotDistributed);
	CPPUNIT_TEST(testAttachToDB);
	CPPUNIT_TEST(testAttachDeferred);
#endif

	CPPUNIT_TEST(testUnfortunateSplitSeq);
	CPPUNIT_TEST(testSplitInc);
	CPPUNIT_TEST(testSplitFlipped);
	CPPUNIT_TEST(testSplitFlipToNewRoot);
	CPPUNIT_TEST(testSplitImplied);

	CPPUNIT_TEST(testAddShortIncremental);
	CPPUNIT_TEST(testSwitchToMtIncremental);
#if TEST_ONCE
	CPPUNIT_TEST(testScheduleAdvance);
	CPPUNIT_TEST(testLubyAdvance);
#endif

	CPPUNIT_TEST(testPushAux);
	CPPUNIT_TEST(testPushAuxFact);
	CPPUNIT_TEST(testPopAuxRemovesConstraints);
	CPPUNIT_TEST(testPopAuxMaintainsQueue);
	CPPUNIT_TEST(testIncrementalAux);

	CPPUNIT_TEST(testUnfreezeStepBug);
	CPPUNIT_TEST(testRemoveConstraint);
	CPPUNIT_TEST_SUITE_END(); 
public:
	void setUp() {
	}
	template <class ST>
	void testReasonStore() {
		ST store;
		store.resize(1);
		store.dataResize(1);
		Constraint* x = new TestingConstraint(0, Constraint_t::learnt_conflict);
		store[0] = x;
		store.setData(0, 22);
		CPPUNIT_ASSERT(store[0]      == x);
		CPPUNIT_ASSERT(store.data(0) == 22);
		Literal p(10,0), q(22, 0);
		store[0]   = Antecedent(p, q);
		uint32 old = store.data(0);
		store.setData(0, 74);
		CPPUNIT_ASSERT(store.data(0) == 74);
		store.setData(0, old);
		CPPUNIT_ASSERT(store[0].firstLiteral() == p && store[0].secondLiteral() == q);

		typedef typename ST::value_type ReasonWithData;
		ReasonWithData rwd(x, 169);
		store[0]    = rwd.ante();
		if (rwd.data() != UINT32_MAX) {
			store.setData(0, rwd.data());
		}
		CPPUNIT_ASSERT(store[0] == x);
		CPPUNIT_ASSERT(store.data(0) == 169);

		rwd = ReasonWithData(p, UINT32_MAX);
		store[0] = rwd.ante();
		if (rwd.data() != UINT32_MAX) {
			store.setData(0, rwd.data());
		}
		CPPUNIT_ASSERT(store[0].firstLiteral() == p);
		x->destroy();
	}
	void testReasonStore() {
		if (sizeof(void*) == sizeof(uint32)) {
			testReasonStore<ReasonStore32>();
		}
		testReasonStore<ReasonStore64>();
	}

	void testSingleOwnerPtr() {
		bool conDel1 = false, conDel2 = false;
		TestingConstraint* f = new TestingConstraint(&conDel2);
		{
			SingleOwnerPtr<Constraint, DestroyObject> x(new TestingConstraint(&conDel1));
			SingleOwnerPtr<Constraint, DestroyObject> y(f);
			y.release();
		}
		CPPUNIT_ASSERT_EQUAL(true, conDel1);
		CPPUNIT_ASSERT_EQUAL(false, conDel2);
		{
			SingleOwnerPtr<Constraint, DestroyObject> y(f);
			y = f;
			CPPUNIT_ASSERT_EQUAL(true, y.is_owner());
			y.release();
			CPPUNIT_ASSERT_EQUAL(false, conDel2);
			y = f;
			CPPUNIT_ASSERT_EQUAL(true, !conDel2 && y.is_owner());
		}
		CPPUNIT_ASSERT_EQUAL(true, conDel2);
	}
	void testDefaults() {
		Solver& s = *ctx.master();
		const SolverParams& x = ctx.configuration()->solver(s.id());
		CPPUNIT_ASSERT(x.heuId == 0);
		CPPUNIT_ASSERT(x.ccMinRec == false);
		CPPUNIT_ASSERT(x.ccMinAntes == SolverStrategies::all_antes);
		CPPUNIT_ASSERT(x.search == SolverStrategies::use_learning);
		CPPUNIT_ASSERT(x.compress == 0);
		CPPUNIT_ASSERT(x.initWatches == SolverStrategies::watch_rand);

		CPPUNIT_ASSERT_EQUAL(0u, s.numVars());
		CPPUNIT_ASSERT_EQUAL(0u, s.numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(0u, s.numConstraints());
		CPPUNIT_ASSERT_EQUAL(0u, s.numLearntConstraints());
		CPPUNIT_ASSERT_EQUAL(0u, s.decisionLevel());
		CPPUNIT_ASSERT_EQUAL(0u, s.queueSize());
		ctx.setFrozen(0, true);
		CPPUNIT_ASSERT(ctx.stats().vars_frozen == 0);
	}
	void testVarNullIsSentinel() {
		Literal p = posLit(0);
		CPPUNIT_ASSERT_EQUAL(true, isSentinel(p));
		CPPUNIT_ASSERT_EQUAL(true, isSentinel(~p));
	}
	void testSolverAlwaysContainsSentinelVar() {
		Solver& s = *ctx.master();
		CPPUNIT_ASSERT_EQUAL(value_true, s.value(sentVar));
		CPPUNIT_ASSERT(s.isTrue(posLit(sentVar)));
		CPPUNIT_ASSERT(s.isFalse(negLit(sentVar)));
		CPPUNIT_ASSERT(s.seen(sentVar) == true);
	}
	void testSolverOwnsConstraints() {
		bool conDel = false;
		bool lconDel = false;
		{
			SharedContext ctx;
			Solver& s = ctx.startAddConstraints();
			ctx.add( new TestingConstraint(&conDel) );
			ctx.endInit();
			s.addLearnt( new TestingConstraint(&lconDel, Constraint_t::learnt_conflict), TestingConstraint::size());
			CPPUNIT_ASSERT_EQUAL(1u, s.numConstraints());
			CPPUNIT_ASSERT_EQUAL(1u, s.numLearntConstraints());
		}
		CPPUNIT_ASSERT_EQUAL(true, conDel);
		CPPUNIT_ASSERT_EQUAL(true, lconDel);
	}

	void testAddVar() {
		Var v1 = ctx.addVar(Var_t::atom_var);
		Var v2 = ctx.addVar(Var_t::body_var);
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		CPPUNIT_ASSERT_EQUAL(2u, s.numVars());
		CPPUNIT_ASSERT_EQUAL(0u, s.numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(2u, s.numFreeVars());
		CPPUNIT_ASSERT_EQUAL(Var_t::atom_var, ctx.varInfo(v1).type());
		CPPUNIT_ASSERT_EQUAL(Var_t::body_var, ctx.varInfo(v2).type());

		CPPUNIT_ASSERT_EQUAL( true, ctx.varInfo(v1).preferredSign() );   
		CPPUNIT_ASSERT_EQUAL( false, ctx.varInfo(v2).preferredSign() );
	}

	void testEliminateVar() {
		Var v1 = ctx.addVar(Var_t::atom_var);
		ctx.addVar(Var_t::body_var);
		Solver& s = ctx.startAddConstraints();
		ctx.eliminate(v1);
		CPPUNIT_ASSERT_EQUAL(uint32(2), s.numVars());
		CPPUNIT_ASSERT_EQUAL(uint32(1), ctx.numEliminatedVars());
		CPPUNIT_ASSERT_EQUAL(uint32(1), s.numFreeVars());
		CPPUNIT_ASSERT_EQUAL(uint32(0), s.numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, ctx.eliminated(v1));
		// so v1 is ignored by heuristics!
		CPPUNIT_ASSERT(s.value(v1) != value_free);

		// ignore subsequent calls 
		ctx.eliminate(v1);
		CPPUNIT_ASSERT_EQUAL(uint32(1), ctx.numEliminatedVars());
		ctx.endInit();
	}
	void testResurrectVar() {
		/*
		Var v1 = ctx.addVar(Var_t::atom_var);
		Var v2 = ctx.addVar(Var_t::body_var);
		struct Dummy : public SelectFirst {
			Dummy() : res(0) {}
			void resurrect(const Solver&, Var v) { res = v; }

			Var res;
		}*h = new Dummy();
		s.strategy.heuristic.reset(h);
		// noop if v2 is not eliminated
		s.eliminate(v2, false);
		CPPUNIT_ASSERT_EQUAL(Var(0), h->res);
		
		s.eliminate(v2, true);
		CPPUNIT_ASSERT_EQUAL(1u, s.numEliminatedVars());
		CPPUNIT_ASSERT_EQUAL(1u, s.numFreeVars());
		
		s.eliminate(v2, false);
		CPPUNIT_ASSERT_EQUAL(v2, h->res);
		CPPUNIT_ASSERT_EQUAL(0u, s.numEliminatedVars());
		CPPUNIT_ASSERT_EQUAL(2u, s.numFreeVars());
		*/
		CPPUNIT_FAIL("TODO - Resurrection of vars not yet supported\n");
	}

	void testCmpScores() {
		ReduceStrategy rs;
		Activity a1(100, 5);
		Activity a2(90, 3);
		CPPUNIT_ASSERT(rs.compare(ReduceStrategy::score_act, a1, a2) > 0);
		CPPUNIT_ASSERT(rs.compare(ReduceStrategy::score_lbd, a1, a2) < 0);
		CPPUNIT_ASSERT(rs.compare(ReduceStrategy::score_both, a1, a2) > 0);
	}
	
	void testValueSet() {
		ValueSet vs;
		CPPUNIT_ASSERT_EQUAL(vs.empty(), true);
		vs.set(ValueSet::pref_value, value_true);
		CPPUNIT_ASSERT_EQUAL(vs.empty(), false);
		CPPUNIT_ASSERT_EQUAL(vs.has(ValueSet::pref_value), true);
		CPPUNIT_ASSERT_EQUAL(vs.sign(), false);
		vs.set(ValueSet::saved_value, value_false);
		CPPUNIT_ASSERT_EQUAL(vs.has(ValueSet::saved_value), true);
		CPPUNIT_ASSERT_EQUAL(vs.sign(), true);

		vs.set(ValueSet::user_value, value_true);
		CPPUNIT_ASSERT_EQUAL(vs.has(ValueSet::user_value), true);
		CPPUNIT_ASSERT_EQUAL(vs.sign(), false);

		vs.set(ValueSet::user_value, value_free);
		CPPUNIT_ASSERT_EQUAL(vs.has(ValueSet::user_value), false);
		CPPUNIT_ASSERT_EQUAL(vs.sign(), true);
	}
	void testPreferredLitByType() {
		Var v1 = ctx.addVar(Var_t::atom_var);
		Var v2 = ctx.addVar(Var_t::body_var);
		Var v3 = ctx.addVar(Var_t::atom_var, true);
		Var v4 = ctx.addVar(Var_t::body_var, true);
		CPPUNIT_ASSERT_EQUAL( true, ctx.varInfo(v1).preferredSign() );
		CPPUNIT_ASSERT_EQUAL( false, ctx.varInfo(v2).preferredSign() );
		CPPUNIT_ASSERT_EQUAL( true, ctx.varInfo(v3).preferredSign() );   
		CPPUNIT_ASSERT_EQUAL( false, ctx.varInfo(v4).preferredSign() );
		BasicSatConfig config;
		config.addSolver(0).signDef = SolverStrategies::sign_disj;
		ctx.setConfiguration(&config, false);
		Solver& s = ctx.startAddConstraints();
		CPPUNIT_ASSERT_EQUAL( negLit(v1), DecisionHeuristic::selectLiteral(s, v1, 0) );
		CPPUNIT_ASSERT_EQUAL( posLit(v2), DecisionHeuristic::selectLiteral(s, v2, 0) );
		ctx.setInDisj(v1, true);
		CPPUNIT_ASSERT_EQUAL( posLit(v1), DecisionHeuristic::selectLiteral(s, v1, 0) );
	}

	void testInitSavedValue() {
		Var v1 = ctx.addVar(Var_t::atom_var);
		Var v2 = ctx.addVar(Var_t::body_var);
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		CPPUNIT_ASSERT_EQUAL( value_free, s.pref(v1).get(ValueSet::saved_value) ); 
		CPPUNIT_ASSERT_EQUAL( value_free, s.pref(v2).get(ValueSet::saved_value) );

		s.setPref(v1, ValueSet::saved_value, value_true);
		s.setPref(v2, ValueSet::saved_value, value_false);

		CPPUNIT_ASSERT_EQUAL( value_true, s.pref(v1).get(ValueSet::saved_value) ); 
		CPPUNIT_ASSERT_EQUAL( value_false, s.pref(v2).get(ValueSet::saved_value));
	}

	void testReset() {
		ctx.addVar(Var_t::atom_var); ctx.addVar(Var_t::body_var);
		Solver& s = ctx.startAddConstraints();
		s.add( new TestingConstraint(0) );
		ctx.endInit();
		s.addLearnt( new TestingConstraint(0, Constraint_t::learnt_conflict), TestingConstraint::size());
		s.assume( posLit(1) );
		ctx.reset();
		testDefaults();
		Var n = ctx.addVar(Var_t::body_var);
		ctx.startAddConstraints();
		ctx.endInit();
		CPPUNIT_ASSERT_EQUAL(Var_t::body_var, ctx.varInfo(n).type());
	}

	void testForce() {
		Var v1 = ctx.addVar(Var_t::atom_var);
		Var v2 = ctx.addVar(Var_t::atom_var);
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		CPPUNIT_ASSERT_EQUAL(true, s.force(posLit(v1), 0));
		CPPUNIT_ASSERT_EQUAL(true, s.force(negLit(v2), posLit(v1)));
		CPPUNIT_ASSERT_EQUAL(true, s.isTrue(posLit(v1)));
		CPPUNIT_ASSERT_EQUAL(true, s.isTrue(negLit(v2)));
		CPPUNIT_ASSERT(s.reason(negLit(v2)).type() == Antecedent::binary_constraint);

		CPPUNIT_ASSERT_EQUAL(2u, s.queueSize());
	}

	void testNoUpdateOnConsistentAssign() {
		Var v1 = ctx.addVar(Var_t::atom_var);
		Var v2 = ctx.addVar(Var_t::atom_var);
		Solver& s = ctx.startAddConstraints();
		s.force( posLit(v2), 0 );
		s.force( posLit(v1), 0 );
		uint32 oldA = s.numAssignedVars();
		CPPUNIT_ASSERT_EQUAL(true, s.force( posLit(v1), posLit(v2) ));
		CPPUNIT_ASSERT_EQUAL(oldA, s.numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(2u, s.queueSize());
	}

	void testAssume() {
		Literal p = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		CPPUNIT_ASSERT_EQUAL(true, s.assume(p));
		CPPUNIT_ASSERT_EQUAL(value_true, s.value(p.var()));
		CPPUNIT_ASSERT_EQUAL(1u, s.decisionLevel());
		CPPUNIT_ASSERT_EQUAL(1u, s.queueSize());
	}

	void testGetDecision() {
		Literal p = posLit(ctx.addVar(Var_t::atom_var));
		Literal q = posLit(ctx.addVar(Var_t::atom_var));
		Literal r = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		s.assume(p);
		s.assume(q);
		s.assume(~r);
		CPPUNIT_ASSERT_EQUAL(p, s.decision(1));
		CPPUNIT_ASSERT_EQUAL(q, s.decision(2));
		CPPUNIT_ASSERT_EQUAL(~r, s.decision(3));
		CPPUNIT_ASSERT_EQUAL(~r, s.decision(s.decisionLevel()));
	}
	void testAddWatch() {
		Literal p = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		TestingConstraint c;
		CPPUNIT_ASSERT_EQUAL(false, s.hasWatch(p, &c));
		s.addWatch(p, &c);
		CPPUNIT_ASSERT_EQUAL(true, s.hasWatch(p, &c));
		CPPUNIT_ASSERT_EQUAL(1u, s.numWatches(p));
	}

	void testRemoveWatch() {
		Literal p = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		TestingConstraint c;
		s.addWatch(p, &c);
		s.removeWatch(p, &c);
		CPPUNIT_ASSERT_EQUAL(false, s.hasWatch(p, &c));
	}

	void testNotifyWatch() {
		Literal p = posLit(ctx.addVar(Var_t::atom_var)), q = posLit(ctx.addVar(Var_t::atom_var));
		TestingConstraint c;
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		s.addWatch(p, &c);
		s.addWatch(q, &c);
		s.assume(p);
		s.propagate();
		CPPUNIT_ASSERT_EQUAL(1, c.propagates);
		s.assume(~q);
		s.propagate();
		CPPUNIT_ASSERT_EQUAL(1, c.propagates);
	}

	void testKeepWatchOnPropagate() {
		Literal p = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		TestingConstraint c;
		s.addWatch(p, &c);
		s.assume(p);
		s.propagate();
		CPPUNIT_ASSERT_EQUAL(true, s.hasWatch(p, &c));
	}

	void testRemoveWatchOnPropagate() {
		Literal p = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		TestingConstraint c;
		c.keepWatch = false;
		s.addWatch(p, &c);
		s.assume(p);
		s.propagate();
		CPPUNIT_ASSERT_EQUAL(false, s.hasWatch(p, &c));
	}

	void testWatchOrder() {
		Literal p = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		TestingConstraint c1, c2, c3;
		c1.keepWatch = false;
		c2.setConflict = true;
		s.addWatch(p, &c1);
		s.addWatch(p, &c2);
		s.addWatch(p, &c3);
		s.assume(p);
		CPPUNIT_ASSERT_EQUAL(false, s.propagate());
		CPPUNIT_ASSERT_EQUAL(false, s.hasWatch(p, &c1));
		CPPUNIT_ASSERT_EQUAL(true, s.hasWatch(p, &c2));
		CPPUNIT_ASSERT_EQUAL(true, s.hasWatch(p, &c3));
		CPPUNIT_ASSERT_EQUAL(1, c1.propagates);
		CPPUNIT_ASSERT_EQUAL(1, c2.propagates);
		CPPUNIT_ASSERT_EQUAL(0, c3.propagates);
	}

	void testUndoUntil() {
		Literal a = posLit(ctx.addVar(Var_t::atom_var)), b = posLit(ctx.addVar(Var_t::atom_var))
			, c = posLit(ctx.addVar(Var_t::atom_var)), d = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		s.assume(a);
		s.force(~b, a);
		s.force(~c, a);
		s.force(d, a);
		CPPUNIT_ASSERT_EQUAL(4u, s.queueSize());
		CPPUNIT_ASSERT_EQUAL(4u, s.numAssignedVars());
		s.undoUntil(0u);
		CPPUNIT_ASSERT_EQUAL(0u, s.numAssignedVars());
		for (Var i = a.var(); i != d.var()+1; ++i) {
			CPPUNIT_ASSERT_EQUAL(value_free, s.value(i));
		}
	}

	void testUndoWatches() {
		Literal a = posLit(ctx.addVar(Var_t::atom_var)), b = posLit(ctx.addVar(Var_t::atom_var));
		TestingConstraint c;
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		s.assume(a);
		s.addUndoWatch(1, &c);
		s.assume(b);
		s.undoUntil(1);
		CPPUNIT_ASSERT_EQUAL(0, c.undos);
		s.undoUntil(0);
		CPPUNIT_ASSERT_EQUAL(1, c.undos);
	}

	void testPropBinary() {
		LitVec bin = addBinary();
		Solver& s  = *ctx.master();
		for (int i = 0; i < 2; ++i) {
			s.assume(~bin[i]);
			CPPUNIT_ASSERT(s.propagate());
			int o = (i+1)%2;
			CPPUNIT_ASSERT_EQUAL(true, s.isTrue(bin[o]));
			CPPUNIT_ASSERT_EQUAL(Antecedent::binary_constraint, s.reason(bin[o]).type());
			LitVec r;
			s.reason(bin[o], r);
			CPPUNIT_ASSERT_EQUAL(1u, (uint32)r.size());
			CPPUNIT_ASSERT(~bin[i] == r[0]);
			s.undoUntil(0);
		}
		s.assume(~bin[0]);
		s.force(~bin[1], 0);
		CPPUNIT_ASSERT_EQUAL(false, s.propagate());
		const LitVec& r = s.conflict();
		CPPUNIT_ASSERT_EQUAL(2u, (uint32)r.size());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~bin[0]) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~bin[1]) != r.end());
	}

	void testPropTernary() {
		LitVec tern = addTernary();
		Solver& s   = *ctx.master();
		for (int i = 0; i < 3; ++i) {
			s.assume(~tern[i]);
			s.assume(~tern[(i+1)%3]);
			CPPUNIT_ASSERT(s.propagate());
			int o = (i+2)%3;
			CPPUNIT_ASSERT_EQUAL(true, s.isTrue(tern[o]));
			CPPUNIT_ASSERT_EQUAL(Antecedent::ternary_constraint, s.reason(tern[o]).type());
			LitVec r;
			s.reason(tern[o], r);
			CPPUNIT_ASSERT_EQUAL(2u, (uint32)r.size());
			CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~tern[i]) != r.end());
			CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~tern[(i+1)%3]) != r.end());
			s.undoUntil(0);
		}
		s.assume(~tern[0]);
		s.force(~tern[1], 0);
		s.force(~tern[2], 0);
		CPPUNIT_ASSERT_EQUAL(false, s.propagate());
		const LitVec& r = s.conflict();
		CPPUNIT_ASSERT_EQUAL(3u, (uint32)r.size());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~tern[0]) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~tern[1]) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~tern[2]) != r.end());
	}

	void testRestartAfterUnitLitResolvedBug() {
		LitVec bin = addBinary();
		Solver& s  = *ctx.master();
		s.force(~bin[0], 0);
		s.undoUntil(0);
		s.propagate();
		CPPUNIT_ASSERT_EQUAL(true, s.isTrue(~bin[0]));
		CPPUNIT_ASSERT_EQUAL(true, s.isTrue(bin[1]));
	}

	void testEstimateBCP() {
		Literal a = posLit(ctx.addVar(Var_t::atom_var));
		Literal b = posLit(ctx.addVar(Var_t::atom_var));
		Literal c = posLit(ctx.addVar(Var_t::atom_var));
		Literal d = posLit(ctx.addVar(Var_t::atom_var));
		Literal e = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		ctx.addBinary(a, b);
		ctx.addBinary(~b, c);
		ctx.addBinary(~c, d);
		ctx.addBinary(~d, e);
		ctx.endInit();
		for (int i = 0; i < 4; ++i) {
			uint32 est = s.estimateBCP(~a, i);
			CPPUNIT_ASSERT_EQUAL(uint32(i + 2), est);
		}
	}

	void testEstimateBCPLoop() {
		Literal a = posLit(ctx.addVar(Var_t::atom_var));
		Literal b = posLit(ctx.addVar(Var_t::atom_var));
		Literal c = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		ctx.addBinary(a, b);
		ctx.addBinary(~b, c);
		ctx.addBinary(~c, ~a);
		ctx.endInit();
		CPPUNIT_ASSERT_EQUAL(uint32(3), s.estimateBCP(~a, -1));
	}

	void testAssertImmediate() {
		Literal a = posLit(ctx.addVar(Var_t::atom_var));
		Literal b = posLit(ctx.addVar(Var_t::atom_var));
		Literal d = posLit(ctx.addVar(Var_t::atom_var));
		Literal q = posLit(ctx.addVar(Var_t::atom_var));
		Literal f = posLit(ctx.addVar(Var_t::atom_var));
		Literal x = posLit(ctx.addVar(Var_t::atom_var));
		Literal z = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		
		ClauseCreator cl(&s);
		cl.addDefaultFlags(ClauseCreator::clause_watch_first);
		cl.start().add(~z).add(d).end();
		cl.start().add(a).add(b).end();
		cl.start().add(a).add(~b).add(z).end();
		cl.start().add(a).add(~b).add(~z).add(d).end();
		cl.start().add(~b).add(~z).add(~d).add(q).end();
		cl.start().add(~q).add(f).end();
		cl.start().add(~f).add(~z).add(x).end();
		s.assume( ~a );
		CPPUNIT_ASSERT_EQUAL( true, s.propagate() );

		CPPUNIT_ASSERT_EQUAL( 7u, s.numAssignedVars());

		Antecedent whyB = s.reason(b);
		Antecedent whyZ = s.reason(z);
		Antecedent whyD = s.reason(d);
		Antecedent whyQ = s.reason(q);
		Antecedent whyF = s.reason(f);
		Antecedent whyX = s.reason(x);

		CPPUNIT_ASSERT(whyB.type() == Antecedent::binary_constraint && whyB.firstLiteral() == ~a);
		CPPUNIT_ASSERT(whyZ.type() == Antecedent::ternary_constraint && whyZ.firstLiteral() == ~a && whyZ.secondLiteral() == b);
		CPPUNIT_ASSERT(whyD.type() == Antecedent::generic_constraint);
		CPPUNIT_ASSERT(whyQ.type() == Antecedent::generic_constraint);
		
		CPPUNIT_ASSERT(whyF.type() == Antecedent::binary_constraint && whyF.firstLiteral() == q);
		CPPUNIT_ASSERT(whyX.type() == Antecedent::ternary_constraint && whyX.firstLiteral() == f && whyX.secondLiteral() == z);
	}

	void testPreferShortBfs() {
		Literal a = posLit(ctx.addVar(Var_t::atom_var));
		Literal b = posLit(ctx.addVar(Var_t::atom_var));
		Literal p = posLit(ctx.addVar(Var_t::atom_var));
		Literal q = posLit(ctx.addVar(Var_t::atom_var));
		Literal x = posLit(ctx.addVar(Var_t::atom_var));
		Literal y = posLit(ctx.addVar(Var_t::atom_var));
		Literal z = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		ClauseCreator cl(&s);
		cl.addDefaultFlags(ClauseCreator::clause_watch_least);
		cl.start().add(a).add(x).add(y).add(p).end();   // c1
		cl.start().add(a).add(x).add(y).add(z).end();   // c2
		cl.start().add(a).add(p).end();                 // c3
		cl.start().add(a).add(~p).add(z).end();         // c4
		cl.start().add(~z).add(b).end();                // c5
		cl.start().add(a).add(x).add(q).add(~b).end();  // c6
		cl.start().add(a).add(~b).add(~p).add(~q).end();// c7
		
		CPPUNIT_ASSERT_EQUAL(7u, s.numConstraints());
		CPPUNIT_ASSERT_EQUAL(2u, ctx.numBinary());
		CPPUNIT_ASSERT_EQUAL(1u, ctx.numTernary());
		
		s.assume( ~x );
		s.propagate();
		s.assume( ~y );
		s.propagate();
		CPPUNIT_ASSERT_EQUAL(2u, s.numAssignedVars());
		s.assume( ~a );
		
		CPPUNIT_ASSERT_EQUAL(false, s.propagate());

		CPPUNIT_ASSERT_EQUAL( 7u, s.numAssignedVars());

		CPPUNIT_ASSERT( s.reason(b).type() == Antecedent::binary_constraint );
		CPPUNIT_ASSERT( s.reason(p).type() == Antecedent::binary_constraint );
		CPPUNIT_ASSERT( s.reason(z).type() == Antecedent::ternary_constraint );
		CPPUNIT_ASSERT( s.reason(q).type() == Antecedent::generic_constraint );
	}
	void testPostPropInit() {
		TestingPostProp* p = new TestingPostProp(false);
		Solver& s = ctx.startAddConstraints();
		s.addPost(p);
		CPPUNIT_ASSERT_EQUAL(0, p->inits); // init is called *after* setup
		ctx.endInit();
		CPPUNIT_ASSERT_EQUAL(1, p->inits);
		ctx.startAddConstraints();
		ctx.endInit();
		CPPUNIT_ASSERT_EQUAL(2, p->inits);
	}
	void testPropagateCallsPostProp() {
		TestingPostProp* p = new TestingPostProp(false);
		Solver& s = ctx.startAddConstraints();
		s.addPost(p);
		s.propagate();
		CPPUNIT_ASSERT_EQUAL(0, p->props); // not yet enabled
		ctx.endInit();
		CPPUNIT_ASSERT_EQUAL(1, p->props);
		CPPUNIT_ASSERT_EQUAL(0, p->resets);
	}
	void testPropagateCallsResetOnConflict() {
		TestingPostProp* p = new TestingPostProp(true);
		Solver& s = ctx.startAddConstraints();
		s.addPost(p);
		ctx.endInit();
		CPPUNIT_ASSERT_EQUAL(1, p->props);
		CPPUNIT_ASSERT_EQUAL(1, p->resets);
	}

	void testPostpropPriority() {
		TestingPostProp* p1 = new TestingPostProp(false);
		p1->prio += 10;
		TestingPostProp* p2 = new TestingPostProp(false);
		p2->prio += 30;
		TestingPostProp* p3 = new TestingPostProp(false);
		p3->prio += 20;
		Solver& s = ctx.startAddConstraints();
		s.addPost(p2);
		s.addPost(p1);
		s.addPost(p3);
		CPPUNIT_ASSERT(p1->next == p3 && p3->next == p2);
	}

	void testPostpropPriorityExt() {
		TestingPostProp* p1 = new TestingPostProp(false);
		TestingPostProp* p2 = new TestingPostProp(false);
		TestingPostProp* p3 = new TestingPostProp(false);
		TestingPostProp* p4 = new TestingPostProp(false);
		p1->prio = 10;
		p2->prio = 20;
		p3->prio = PostPropagator::priority_class_general;
		p4->prio = PostPropagator::priority_class_general;
		Solver& s = ctx.startAddConstraints();
		s.addPost(p3);
		s.addPost(p2);
		CPPUNIT_ASSERT(s.getPost(PostPropagator::priority_class_general));
		CPPUNIT_ASSERT(s.getPost(20));
		CPPUNIT_ASSERT(p2->next == p3);
		s.addPost(p4);
		CPPUNIT_ASSERT(p2->next == p4);
		CPPUNIT_ASSERT(p4->next == p3);
		ctx.endInit();
		CPPUNIT_ASSERT(p3->inits == 1);
		p3->props = 0;
		p2->props = 0;
		p4->props = 0;
		s.removePost(p2);
		s.removePost(p4);
		s.addPost(p4);
		s.propagate();
		CPPUNIT_ASSERT(p3->props == 1 && p4->props == 1);
		s.addPost(p1);
		CPPUNIT_ASSERT(p1->next == p4);
		s.addPost(p2);
		CPPUNIT_ASSERT(p1->next == p2 && p2->next == p4);
		s.removePost(p3);
		s.removePost(p4);
		s.propagate();
		CPPUNIT_ASSERT(p3->props == 1 && p4->props == 1 && p1->props == 1 && p2->props == 1);
		s.addPost(p4);
		s.addPost(p3);
		p3->conflict = true;
		s.propagate();
		CPPUNIT_ASSERT(p3->props == 2 && p1->props == 2 && p2->props == 2 && p4->props == 1);
	}
	
	void testPostpropRemove() {
		SingleOwnerPtr<TestingPostProp> p1(new TestingPostProp(false, 1));
		SingleOwnerPtr<TestingPostProp> p2(new TestingPostProp(false, 2));
		SingleOwnerPtr<TestingPostProp> p3(new TestingPostProp(false, 3));
		Solver& s = ctx.startAddConstraints();
		s.addPost(p1.release());
		s.addPost(p2.release());
		s.addPost(p3.release());
		CPPUNIT_ASSERT(p1->next == p2.get() && p2->next == p3.get());
		s.removePost(p2.acquire());
		CPPUNIT_ASSERT(p1->next == p3.get() && p3->next == 0 && p2->next == 0);
		s.removePost(p2.acquire());
		s.removePost(p3.acquire());
		CPPUNIT_ASSERT(p1->next == 0);
		ctx.endInit();
		CPPUNIT_ASSERT(p1->props == 1);
	}

	void testPostpropRemoveOnProp() {
		TestingPostProp* p1 = new TestingPostProp(false);
		TestingPostProp* p2 = new TestingPostProp(false);
		TestingPostProp* p3 = new TestingPostProp(false);
		Solver& s = ctx.startAddConstraints();
		s.addPost(p1);
		s.addPost(p2);
		s.addPost(p3);
		ctx.endInit();
		p2->deleteOnProp = true;
		s.propagate();
		CPPUNIT_ASSERT(p1->props == 2 && p3->props == 2);
	}

	void testPostpropBug() {
		Solver& s = ctx.startAddConstraints();
		SingleOwnerPtr<TestingPostProp> p1(new TestingPostProp(false));
		s.addPost(p1.release());
		ctx.endInit();
		// later
		ctx.startAddConstraints();
		s.removePost(p1.get());
		p1.acquire();
		ctx.endInit();
		s.removePost(p1.get());
		CPPUNIT_ASSERT(p1->inits == 1);
	}

	void testPostpropAddAfterInitBug() {
		Solver& s = ctx.startAddConstraints();
		SingleOwnerPtr<TestingPostProp> p1(new TestingPostProp(false));
		ctx.endInit();
		s.addPost(p1.release());
		CPPUNIT_ASSERT(p1->inits == 1);
		s.propagate();
		CPPUNIT_ASSERT(p1->props == 1);
	}

	void testSimplifyRemovesSatBinClauses() {
		Literal a = posLit(ctx.addVar(Var_t::atom_var));
		Literal b = posLit(ctx.addVar(Var_t::atom_var));
		Literal c = posLit(ctx.addVar(Var_t::atom_var));
		Literal d = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		ctx.addBinary(a, b);
		ctx.addBinary(a, c);
		ctx.addBinary(~a, d);
		s.force(a, 0);
		s.simplify();
		CPPUNIT_ASSERT_EQUAL(0u, ctx.numBinary());
	}

	void testSimplifyRemovesSatTernClauses() {
		Literal a = posLit(ctx.addVar(Var_t::atom_var));
		Literal b = posLit(ctx.addVar(Var_t::atom_var));
		Literal c = posLit(ctx.addVar(Var_t::atom_var));
		Literal d = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		ctx.addTernary(a, b, d);
		ctx.addTernary(~a, b, c);
		s.force(a, 0);
		s.simplify(); 
		s.assume(~b);
		CPPUNIT_ASSERT_EQUAL(0u, ctx.numTernary());
		
		// simplify transformed the tern-clause ~a b c to the bin clause b c
		// because ~a is false on level 0
		CPPUNIT_ASSERT_EQUAL(1u, ctx.numBinary());
		s.propagate();
		CPPUNIT_ASSERT_EQUAL(true, s.isTrue(c));
	}
	
	void testSimplifyRemovesSatConstraints() {
		Literal a = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		TestingConstraint* t1;
		TestingConstraint* t2;
		TestingConstraint* t3;
		TestingConstraint* t4;
		bool t2Del = false, t3Del = false;
		s.add( t1 = new TestingConstraint );
		s.add( t2 = new TestingConstraint(&t2Del) );
		ctx.endInit();
		s.addLearnt( t3 = new TestingConstraint(&t3Del, Constraint_t::learnt_conflict), TestingConstraint::size() );
		s.addLearnt( t4 = new TestingConstraint(0, Constraint_t::learnt_conflict), TestingConstraint::size() );
		t1->sat = false;
		t2->sat = true;
		t3->sat = true;
		t4->sat = false;
		CPPUNIT_ASSERT_EQUAL(2u, s.numLearntConstraints());
		CPPUNIT_ASSERT_EQUAL(2u, s.numLearntConstraints());
		s.force( a, 0 );
		s.simplify();
		CPPUNIT_ASSERT_EQUAL(1u, s.numLearntConstraints());
		CPPUNIT_ASSERT_EQUAL(1u, s.numLearntConstraints());
		CPPUNIT_ASSERT_EQUAL(true, t2Del);
		CPPUNIT_ASSERT_EQUAL(true, t3Del);
	}

	void testRemoveConditional() {
		Var a = ctx.addVar( Var_t::atom_var );
		Var b = ctx.addVar( Var_t::atom_var );
		Var c = ctx.addVar( Var_t::atom_var );
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		Literal tag = posLit(s.pushTagVar(false));
		ClauseCreator cc(&s);
		cc.start(Constraint_t::learnt_conflict).add(posLit(a)).add(posLit(b)).add(posLit(c)).add(~tag).end();
		CPPUNIT_ASSERT(s.numLearntConstraints() == 1);
		s.removeConditional();
		CPPUNIT_ASSERT(s.numLearntConstraints() == 0);
	}

	void testStrengthenConditional() {
		Var a = ctx.addVar( Var_t::atom_var );
		Var b = ctx.addVar( Var_t::atom_var );
		Var c = ctx.addVar( Var_t::atom_var );
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		ClauseCreator cc(&s);
		Literal tag = posLit(s.pushTagVar(false));
		cc.start(Constraint_t::learnt_conflict).add(posLit(a)).add(posLit(b)).add(posLit(c)).add(~tag).end();
		CPPUNIT_ASSERT(s.numLearntConstraints() == 1);
		s.strengthenConditional();
		CPPUNIT_ASSERT(ctx.numLearntShort() == 1 || ctx.numTernary() == 1);
	}

	void testLearnConditional() {
		Var b = ctx.addVar( Var_t::atom_var );
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		Literal tag = posLit(s.pushTagVar(true));
		s.assume(posLit(b));
		s.propagate();
		TestingConstraint* cfl = new TestingConstraint;
		cfl->ante.push_back(tag);
		cfl->ante.push_back(posLit(b));
		s.force(negLit(0), cfl);
		cfl->destroy(&s, true);
		s.resolveConflict();
		CPPUNIT_ASSERT(ctx.numLearntShort() == 0 && ctx.numBinary() == 0);
		CPPUNIT_ASSERT(s.numLearntConstraints() == 1 && s.decisionLevel() == 1);
		s.strengthenConditional();
		s.clearAssumptions();
		CPPUNIT_ASSERT(s.isTrue(negLit(b)));
	}

	void testResolveUnary() {
		ctx.enableStats(1);
		Var a = ctx.addVar( Var_t::atom_var );
		Var b = ctx.addVar( Var_t::atom_var );
		Var c = ctx.addVar( Var_t::atom_var );
		Solver& s = ctx.startAddConstraints();
		ctx.addBinary(posLit(a), posLit(b));
		ctx.addBinary(negLit(b), posLit(c));
		ctx.addBinary(negLit(a), posLit(c));
		s.assume( negLit(c) );
		CPPUNIT_ASSERT_EQUAL(false, s.propagate());
		CPPUNIT_ASSERT_EQUAL(true, s.resolveConflict());
		CPPUNIT_ASSERT_EQUAL(false, s.hasConflict());
		CPPUNIT_ASSERT_EQUAL(true, s.isTrue(posLit(c)));
		CPPUNIT_ASSERT_EQUAL(0u, s.decisionLevel());
		CPPUNIT_ASSERT(s.stats.extra->learnts[Constraint_t::learnt_conflict-1] == 1);
	}

	void testResolveConflict() {
		Literal x1 = posLit(ctx.addVar( Var_t::atom_var )); Literal x2 = posLit(ctx.addVar( Var_t::atom_var ));
		Literal x3 = posLit(ctx.addVar( Var_t::atom_var )); Literal x4 = posLit(ctx.addVar( Var_t::atom_var ));
		Literal x5 = posLit(ctx.addVar( Var_t::atom_var )); Literal x6 = posLit(ctx.addVar( Var_t::atom_var ));
		Literal x7 = posLit(ctx.addVar( Var_t::atom_var )); Literal x8 = posLit(ctx.addVar( Var_t::atom_var ));
		Literal x9 = posLit(ctx.addVar( Var_t::atom_var )); Literal x10 = posLit(ctx.addVar( Var_t::atom_var ));
		Literal x11 = posLit(ctx.addVar( Var_t::atom_var )); Literal x12 = posLit(ctx.addVar( Var_t::atom_var ));
		Literal x13 = posLit(ctx.addVar( Var_t::atom_var )); Literal x14 = posLit(ctx.addVar( Var_t::atom_var ));
		Literal x15 = posLit(ctx.addVar( Var_t::atom_var )); Literal x16 = posLit(ctx.addVar( Var_t::atom_var ));
		Literal x17 = posLit(ctx.addVar( Var_t::atom_var ));
		Solver& s   = ctx.startAddConstraints();
		ClauseCreator cl(&s);
		cl.start().add(~x11).add(x12).end();
		cl.start().add(x1).add(~x12).add(~x13).end();
		cl.start().add(~x4).add(~x12).add(x14).end();
		cl.start().add(x13).add(~x14).add(~x15).end();
		cl.start().add(~x2).add(x15).add(x16).end();
		cl.start().add(x3).add(x15).add(~x17).end();
		cl.start().add(~x6).add(~x16).add(x17).end();
		cl.start().add(~x2).add(x9).add(x10).end();
		cl.start().add(~x4).add(~x7).add(~x8).end();
		cl.start().add(x5).add(x6).end();
		CPPUNIT_ASSERT_EQUAL(true, ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(0u, s.queueSize());
		
		CPPUNIT_ASSERT_EQUAL(true, s.assume(~x1) && s.propagate());
		CPPUNIT_ASSERT_EQUAL(true, s.assume(x2) && s.propagate());
		CPPUNIT_ASSERT_EQUAL(true, s.assume(~x3) && s.propagate());
		CPPUNIT_ASSERT_EQUAL(true, s.assume(x4) && s.propagate());
		CPPUNIT_ASSERT_EQUAL(true, s.assume(~x5) && s.propagate());
		CPPUNIT_ASSERT_EQUAL(true, s.assume(x7) && s.propagate());
		CPPUNIT_ASSERT_EQUAL(true, s.assume(~x9) && s.propagate());

		CPPUNIT_ASSERT_EQUAL(false, s.assume(x11) && s.propagate());
		
		CPPUNIT_ASSERT_EQUAL(true, s.resolveConflict());
		CPPUNIT_ASSERT_EQUAL(s.trail().back(), x15); // UIP
		CPPUNIT_ASSERT_EQUAL(5u, s.decisionLevel());
		CPPUNIT_ASSERT_EQUAL(Antecedent::generic_constraint, s.reason(s.trail().back()).type());
		
		LitVec cflClause;
		s.reason(s.trail().back(), cflClause);
		cflClause.push_back(s.trail().back());
		CPPUNIT_ASSERT(LitVec::size_type(4) == cflClause.size());
		CPPUNIT_ASSERT(std::find(cflClause.begin(), cflClause.end(), x2) != cflClause.end());
		CPPUNIT_ASSERT(std::find(cflClause.begin(), cflClause.end(), ~x3) != cflClause.end());
		CPPUNIT_ASSERT(std::find(cflClause.begin(), cflClause.end(), x6) != cflClause.end());
		CPPUNIT_ASSERT(std::find(cflClause.begin(), cflClause.end(), x15) != cflClause.end());
	}

	void testResolveConflictBounded() {
		Literal x1 = posLit(ctx.addVar( Var_t::atom_var )); Literal x2 = posLit(ctx.addVar( Var_t::atom_var ));
		Literal x3 = posLit(ctx.addVar( Var_t::atom_var )); Literal x4 = posLit(ctx.addVar( Var_t::atom_var ));
		Literal x5 = posLit(ctx.addVar( Var_t::atom_var )); Literal x6 = posLit(ctx.addVar( Var_t::atom_var ));
		Literal x7 = posLit(ctx.addVar( Var_t::atom_var )); Literal x8 = posLit(ctx.addVar( Var_t::atom_var ));
		Literal x9 = posLit(ctx.addVar( Var_t::atom_var )); Literal x10 = posLit(ctx.addVar( Var_t::atom_var ));
		Literal x11 = posLit(ctx.addVar( Var_t::atom_var )); Literal x12 = posLit(ctx.addVar( Var_t::atom_var ));
		Literal x13 = posLit(ctx.addVar( Var_t::atom_var )); Literal x14 = posLit(ctx.addVar( Var_t::atom_var ));
		Literal x15 = posLit(ctx.addVar( Var_t::atom_var )); Literal x16 = posLit(ctx.addVar( Var_t::atom_var ));
		Literal x17 = posLit(ctx.addVar( Var_t::atom_var )); Literal x18 = posLit(ctx.addVar( Var_t::atom_var ));
		Solver& s = ctx.startAddConstraints();
		ClauseCreator cl(&s);
		cl.start().add(~x11).add(x12).end();
		cl.start().add(x1).add(~x12).add(~x13).end();
		cl.start().add(~x4).add(~x12).add(x14).end();
		cl.start().add(x13).add(~x14).add(~x15).end();
		cl.start().add(~x2).add(x15).add(x16).end();
		cl.start().add(x3).add(x15).add(~x17).end();
		cl.start().add(~x6).add(~x16).add(x17).end();
		cl.start().add(~x2).add(x9).add(x10).end();
		cl.start().add(~x4).add(~x7).add(~x8).end();
		cl.start().add(x5).add(x6).end();
		CPPUNIT_ASSERT_EQUAL(true, ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(0u, s.queueSize());
		
		CPPUNIT_ASSERT_EQUAL(true, s.assume(~x1) && s.propagate());
		CPPUNIT_ASSERT_EQUAL(true, s.assume(x2) && s.propagate());
		CPPUNIT_ASSERT_EQUAL(true, s.assume(~x3) && s.propagate());
		CPPUNIT_ASSERT_EQUAL(true, s.assume(x4) && s.propagate());
		CPPUNIT_ASSERT_EQUAL(true, s.assume(~x5) && s.propagate());
		CPPUNIT_ASSERT_EQUAL(true, s.assume(x7) && s.propagate());

		// force backtrack-level to 6
		CPPUNIT_ASSERT_EQUAL(true, s.assume(x18) && s.propagate());
		CPPUNIT_ASSERT_EQUAL(true, s.backtrack());
		
		CPPUNIT_ASSERT_EQUAL(true, s.assume(~x9) && s.propagate());
		CPPUNIT_ASSERT_EQUAL(false, s.assume(x11) && s.propagate());
		
		CPPUNIT_ASSERT_EQUAL(true, s.resolveConflict());
		CPPUNIT_ASSERT_EQUAL(s.trail().back(), x15); // UIP
		CPPUNIT_ASSERT_EQUAL(6u, s.decisionLevel());  // Jump was bounded!
		Antecedent ante = s.reason(s.trail().back());
		CPPUNIT_ASSERT_EQUAL(Antecedent::generic_constraint, ante.type());
		ClauseHead* cflClause = (ClauseHead*)ante.constraint();
		LitVec r;
		cflClause->reason(s, s.trail().back(), r);
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), x2) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~x3) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), x6) != r.end());
		
		CPPUNIT_ASSERT_EQUAL(true, s.hasWatch(x6, cflClause));

		CPPUNIT_ASSERT_EQUAL(true, s.backtrack());
		CPPUNIT_ASSERT_EQUAL(true, s.isTrue(x15));  // still true, because logically implied on level 5
		CPPUNIT_ASSERT_EQUAL(true, s.backtrack());
		CPPUNIT_ASSERT_EQUAL(value_free, s.value(x15.var()));
	}
	
	void testSearchKeepsAssumptions() {
		Var a = ctx.addVar( Var_t::atom_var );
		Var b = ctx.addVar( Var_t::atom_var );
		Var c = ctx.addVar( Var_t::atom_var );
		Var d = ctx.addVar( Var_t::atom_var );
		Solver& s = ctx.startAddConstraints();
		ClauseCreator cl(&s);
		ctx.addBinary(posLit(a), posLit(b));
		ctx.addBinary(negLit(b), posLit(c));
		ctx.addBinary(negLit(a), posLit(c));
		ctx.addBinary(negLit(c), negLit(d));
		ctx.endInit();
		s.simplify();
		s.assume( posLit(d) );
		s.pushRootLevel();
		CPPUNIT_ASSERT_EQUAL(value_false, s.search(-1, -1, 0));
		CPPUNIT_ASSERT_EQUAL(1u, s.decisionLevel());
	}
	void testSearchAddsLearntFacts() {
		Var a = ctx.addVar( Var_t::atom_var );
		Var b = ctx.addVar( Var_t::atom_var );
		Var c = ctx.addVar( Var_t::atom_var );
		Var d = ctx.addVar( Var_t::atom_var );
		struct Dummy : public DecisionHeuristic {
			Dummy(Literal first, Literal second) {lit_[0] = first; lit_[1] = second;}
			void updateVar(const Solver&, Var, uint32) {}
			Literal doSelect(Solver& s) {
				for (uint32 i = 0; i < 2; ++i) {
					if (s.value(lit_[i].var()) == value_free) {
						return lit_[i];
					}
				}
				return Literal();
			}
			Literal lit_[2];
		}*h = new Dummy(negLit(c),negLit(a));
		ctx.master()->setHeuristic(h);
		Solver& s = ctx.startAddConstraints();
		ClauseCreator cl(&s);
		ctx.addBinary(posLit(a), posLit(b));
		ctx.addBinary(negLit(b), posLit(c));
		ctx.addBinary(negLit(a), posLit(c));
		ctx.endInit();
		s.assume( posLit(d) );
		s.pushRootLevel();
		CPPUNIT_ASSERT_EQUAL(value_true, s.search(-1, -1, 0));
		s.clearAssumptions();
		CPPUNIT_ASSERT_EQUAL(0u, s.decisionLevel());
		CPPUNIT_ASSERT(s.isTrue(posLit(c)));
	}

	void testSearchMaxConflicts() {
		Var a = ctx.addVar( Var_t::atom_var );
		Var b = ctx.addVar( Var_t::atom_var );
		Var c = ctx.addVar( Var_t::atom_var );
		ctx.addVar( Var_t::atom_var );
		Solver& s = ctx.startAddConstraints();
		ctx.addBinary(posLit(a), negLit(b));
		ctx.addBinary(negLit(a), posLit(b));
		ctx.addBinary(negLit(a), negLit(b));
		ctx.endInit();
		s.simplify();
		s.assume(posLit(c));
		s.pushRootLevel();
		s.assume(posLit(a));
		CPPUNIT_ASSERT_EQUAL(value_free, s.search(1, -1, 0));
		CPPUNIT_ASSERT_EQUAL(1u, s.decisionLevel());
	} 

	void testClearAssumptions() {
		Var a = ctx.addVar( Var_t::atom_var );
		Var b = ctx.addVar( Var_t::atom_var );
		ctx.addVar( Var_t::atom_var );
		Solver& s = ctx.startAddConstraints();
		ctx.addBinary(negLit(a), negLit(b));
		ctx.addBinary(negLit(a), posLit(b));
		ctx.endInit();
		s.assume(posLit(a));
		s.pushRootLevel();
		CPPUNIT_ASSERT_EQUAL(false, s.propagate());
		CPPUNIT_ASSERT_EQUAL(true, s.clearAssumptions());		
		CPPUNIT_ASSERT_EQUAL(0u, s.decisionLevel());		
		
		s.force(posLit(a), 0);
		CPPUNIT_ASSERT_EQUAL(false, s.propagate());
		CPPUNIT_ASSERT_EQUAL(false, s.clearAssumptions());		
	}

	void testStopConflict() {
		Var a = ctx.addVar( Var_t::atom_var );
		Var b = ctx.addVar( Var_t::atom_var );
		Var c = ctx.addVar( Var_t::atom_var );
		Var d = ctx.addVar( Var_t::atom_var );
		Solver& s = ctx.startAddConstraints();
		ctx.addBinary(negLit(a), negLit(b));
		ctx.addBinary(negLit(a), posLit(b));
		ctx.endInit();
		s.assume(posLit(a)) && !s.propagate() && s.resolveConflict();
		CPPUNIT_ASSERT(s.decisionLevel() == 0 && s.queueSize() == 1 && !s.hasConflict());
		s.setStopConflict();
		CPPUNIT_ASSERT(s.hasConflict() && !s.resolveConflict());
		s.clearStopConflict();
		CPPUNIT_ASSERT(s.decisionLevel() == 0 && s.queueSize() == 1 && !s.hasConflict());
		s.propagate();
		s.assume(posLit(c)) && s.propagate();
		s.pushRootLevel(1);
		CPPUNIT_ASSERT(s.rootLevel() == 1);
		s.assume(posLit(d));
		s.setStopConflict();
		CPPUNIT_ASSERT(s.rootLevel() == 2);
		s.clearStopConflict();
		CPPUNIT_ASSERT(s.rootLevel() == 1 && s.queueSize() == 1);
	}
	
	void testClearStopConflictResetsBtLevel() {
		Var a = ctx.addVar( Var_t::atom_var );
		Var b = ctx.addVar( Var_t::atom_var );
		Var c = ctx.addVar( Var_t::atom_var );
		Var d = ctx.addVar( Var_t::atom_var );
		Solver& s = ctx.startAddConstraints();
		ctx.addBinary(negLit(c), posLit(d));
		ctx.endInit();
		s.assume(posLit(a)) && s.propagate();
		s.assume(posLit(b)) && s.propagate();
		s.assume(posLit(c)) && s.propagate();
		CPPUNIT_ASSERT(s.numFreeVars() == 0);
		s.setBacktrackLevel(s.decisionLevel());
		s.backtrack();
		uint32 bt = s.backtrackLevel();
		s.assume(posLit(d)) && s.propagate();
		CPPUNIT_ASSERT(bt != s.decisionLevel());
		s.setStopConflict();
		CPPUNIT_ASSERT(s.backtrackLevel() == s.decisionLevel());
		s.clearStopConflict();
		CPPUNIT_ASSERT(s.backtrackLevel() == bt);
	}

	void testStats() {
		ProblemStats p1, p2;
		CPPUNIT_ASSERT_EQUAL(uint32(0), p1.vars);
		CPPUNIT_ASSERT_EQUAL(uint32(0), p2.vars_eliminated);
		CPPUNIT_ASSERT_EQUAL(uint32(0), p1.constraints);
		CPPUNIT_ASSERT_EQUAL(uint32(0), p2.constraints_binary);
		CPPUNIT_ASSERT_EQUAL(uint32(0), p2.constraints_ternary);

		p1.vars               = 100; p2.vars               = 150;
		p1.vars_eliminated    =  20; p2.vars_eliminated    =  30;
		p1.constraints        = 150; p2.constraints        = 150;
		p1.constraints_binary =   0; p2.constraints_binary = 100;
		p1.constraints_ternary= 100; p2.constraints_ternary=   0;
		p1.diff(p2);

		CPPUNIT_ASSERT_EQUAL(uint32(50), p1.vars);
		CPPUNIT_ASSERT_EQUAL(uint32(10), p1.vars_eliminated);
		CPPUNIT_ASSERT_EQUAL(uint32(0),  p1.constraints);
		CPPUNIT_ASSERT_EQUAL(uint32(100),p1.constraints_binary);
		CPPUNIT_ASSERT_EQUAL(uint32(100),p1.constraints_ternary);

		SolverStats st, st2;
		st.enableExtended();
		st2.enableExtended();
		
		st.conflicts  = 12; st2.conflicts = 3;
		st.choices    = 100;st2.choices   = 99;	
		st.restarts   = 7;  st2.restarts  = 8;
		
		st.extra->models     = 10; st2.extra->models     = 2;
		st.extra->learnts[0] = 6;  st2.extra->learnts[0] = 4;
		st.extra->learnts[1] = 5;  st2.extra->learnts[1] = 4;
		st.extra->lits[0]    = 15; st2.extra->lits[0]    = 14;
		st.extra->lits[1]    = 5;  st2.extra->lits[1]    = 4;
		st.extra->binary     = 6;  st2.extra->ternary    = 5;
		st.extra->deleted    = 10;
		
		st.accu(st2);

		CPPUNIT_ASSERT_EQUAL(uint64(15), st.conflicts);
		CPPUNIT_ASSERT_EQUAL(uint64(199),st.choices);
		CPPUNIT_ASSERT_EQUAL(uint64(15),st.restarts);
		CPPUNIT_ASSERT_EQUAL(uint64(12), st.extra->models);
		CPPUNIT_ASSERT_EQUAL(uint64(29),st.extra->lits[0]);
		CPPUNIT_ASSERT_EQUAL(uint64(9),st.extra->lits[1]);
		CPPUNIT_ASSERT_EQUAL(uint64(10),st.extra->learnts[0]);
		CPPUNIT_ASSERT_EQUAL(uint64(9),st.extra->learnts[1]);
		CPPUNIT_ASSERT_EQUAL(uint32(6),st.extra->binary);
		CPPUNIT_ASSERT_EQUAL(uint32(5),st.extra->ternary);
		CPPUNIT_ASSERT_EQUAL(uint64(10),st.extra->deleted);
	}


	void testLearntShort() {
		Literal a = posLit(ctx.addVar( Var_t::atom_var ));
		Literal b = posLit(ctx.addVar( Var_t::atom_var ));
		Literal c = posLit(ctx.addVar( Var_t::atom_var ));
		Literal d = posLit(ctx.addVar( Var_t::atom_var ));
		ctx.setShareMode(ContextParams::share_problem);
		ctx.setConcurrency(2);
		Solver& s = ctx.startAddConstraints();
		ctx.addBinary(c, d);
		ctx.endInit();
		ClauseCreator cc(&s);
		CPPUNIT_ASSERT(cc.start(Constraint_t::learnt_conflict).add(a).add(b).end());
		CPPUNIT_ASSERT(cc.start(Constraint_t::learnt_conflict).add(~a).add(~b).add(c).end());
		CPPUNIT_ASSERT(ctx.numLearntShort() == 2);
		CPPUNIT_ASSERT(ctx.numBinary()  == 1);
		CPPUNIT_ASSERT(ctx.numTernary() == 0);

		cc.start(Constraint_t::learnt_conflict).add(a).add(b).add(c).end();
		// ignore subsumed/duplicate clauses
		CPPUNIT_ASSERT(ctx.numLearntShort() == 2);

		s.assume(~b);
		s.propagate();
		CPPUNIT_ASSERT(s.isTrue(a) && s.reason(a).firstLiteral() == ~b);
		s.undoUntil(0);
		s.assume(a);
		s.propagate();
		s.assume(b);
		s.propagate();
		CPPUNIT_ASSERT(s.isTrue(c));
		LitVec res;
		s.reason(c, res);
		CPPUNIT_ASSERT(std::find(res.begin(), res.end(), a) != res.end());
		CPPUNIT_ASSERT(std::find(res.begin(), res.end(), b) != res.end());
	}
	
	void testLearntShortAreDistributed() {
		Literal a = posLit(ctx.addVar( Var_t::atom_var ));
		Literal b = posLit(ctx.addVar( Var_t::atom_var ));
		Literal c = posLit(ctx.addVar( Var_t::atom_var ));
		Literal d = posLit(ctx.addVar( Var_t::atom_var ));
		struct Dummy : public Distributor {		
			Dummy() : Distributor(Policy(UINT32_MAX, UINT32_MAX, UINT32_MAX)), unary(0), binary(0), ternary(0) {}
			void publish(const Solver&, SharedLiterals* lits) {
				uint32 size = lits->size();
				unary   += size == 1;
				binary  += size == 2;
				ternary += size == 3;
				shared.push_back(lits);
			}
			uint32 receive(const Solver&, SharedLiterals** out, uint32 num) { 
				uint32 r = 0;
				while (!shared.empty() && num--) {
					out[r++] = shared.back();
					shared.pop_back();
				}
				return r;
			}
			uint32 unary;
			uint32 binary;
			uint32 ternary;
			PodVector<SharedLiterals*>::type shared;
		}* dummy;
		ctx.distributor.reset(dummy = new Dummy());
		ctx.setConcurrency(2);
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		LitVec lits; lits.resize(2);
		lits[0] = a; lits[1] = b;
		ClauseCreator::create(s, lits, 0, ClauseInfo(Constraint_t::learnt_conflict));
		lits.resize(3);
		lits[0] = ~a; lits[1] = ~b; lits[2] = ~c;
		ClauseCreator::create(s, lits, 0, ClauseInfo(Constraint_t::learnt_loop));
		lits.resize(1);
		lits[0] = d;
		ClauseCreator::create(s, lits, 0, ClauseInfo(Constraint_t::learnt_conflict));
		CPPUNIT_ASSERT(dummy->unary  == 1);
		CPPUNIT_ASSERT(dummy->binary == 1);
		CPPUNIT_ASSERT(dummy->ternary == 1);
		SharedLiterals* rec[3];
		CPPUNIT_ASSERT(dummy->receive(s, rec, 3) == 3);
		CPPUNIT_ASSERT(ClauseCreator::integrate(s, rec[0], 0).ok() == true);
		CPPUNIT_ASSERT(ClauseCreator::integrate(s, rec[1], 0).ok() == true);
		CPPUNIT_ASSERT(ClauseCreator::integrate(s, rec[2], 0).ok() == true);
	}

	void testAuxAreNotDistributed() {
		Literal a = posLit(ctx.addVar( Var_t::atom_var ));
		Literal b = posLit(ctx.addVar( Var_t::atom_var ));
		Literal c = posLit(ctx.addVar( Var_t::atom_var ));
		struct Dummy : public Distributor {		
			Dummy() : Distributor(Policy(UINT32_MAX, UINT32_MAX, UINT32_MAX)) {}
			void publish(const Solver&, SharedLiterals* lits) {
				shared.push_back(lits);
			}
			uint32 receive(const Solver&, SharedLiterals**, uint32) { return 0; }
			PodVector<SharedLiterals*>::type shared;
		}* dummy;
		ctx.distributor.reset(dummy = new Dummy());
		ctx.setConcurrency(2);
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		Var aux = s.pushAuxVar();
		
		LitVec lits; lits.resize(2);
		lits[0] = a; lits[1] = posLit(aux);
		ClauseCreator::create(s, lits, 0, ClauseInfo(Constraint_t::learnt_conflict));
		lits.resize(4);
		lits[0] = ~a; lits[1] = posLit(aux); lits[2] = b; lits[3] = c;
		ClauseCreator::create(s, lits, 0, ClauseInfo(Constraint_t::learnt_conflict));
		CPPUNIT_ASSERT(s.numLearntConstraints() == 2);
		CPPUNIT_ASSERT(dummy->shared.empty());
		CPPUNIT_ASSERT(s.getLearnt(0).simplify(s, false) == false);
		s.pushRoot(posLit(aux));
		s.pushRoot(a);
		lits.clear();
		s.copyGuidingPath(lits);
		CPPUNIT_ASSERT(lits.size() == 1 && lits[0] == a);
		s.clearAssumptions();
		lits.resize(4);
		lits[0] = ~a; lits[1] = posLit(aux); lits[2] = ~b; lits[3] = c;
		ClauseCreator::create(s, lits, 0, ClauseInfo(Constraint_t::learnt_conflict));
		s.assume(a) && s.propagate();
		s.assume(negLit(aux)) && s.propagate();
		s.assume(~c) && s.propagate();
		CPPUNIT_ASSERT(s.hasConflict());
		s.resolveConflict();
		CPPUNIT_ASSERT(s.numLearntConstraints() == 4);
		CPPUNIT_ASSERT(dummy->shared.empty());
		CPPUNIT_ASSERT(s.sharedContext()->numTernary() + s.sharedContext()->numBinary() == 0);
	}

	void testAttachToDB() {
		Literal a = posLit(ctx.addVar( Var_t::atom_var ));
		Literal b = posLit(ctx.addVar( Var_t::atom_var ));
		Literal c = posLit(ctx.addVar( Var_t::atom_var ));
		Literal d = posLit(ctx.addVar( Var_t::atom_var ));
		ctx.setConcurrency(2);
		Solver& s = ctx.startAddConstraints();
		ClauseCreator cc(&s);
		cc.start().add(a).add(b).add(c).add(d).end();
		Solver& s2 = ctx.addSolver();
		ctx.endInit();
		ctx.attach(s2);
		CPPUNIT_ASSERT(s2.numConstraints() == 1);
		ctx.unfreeze();
		Literal e = posLit(ctx.addVar( Var_t::atom_var ));
		Literal f = posLit(ctx.addVar( Var_t::atom_var ));
		Literal g = posLit(ctx.addVar( Var_t::atom_var ));
		Literal h = posLit(ctx.addVar( Var_t::atom_var ));
		ctx.startAddConstraints();
		cc.start().add(e).add(f).add(g).add(h).end();
		cc.start().add(a).end();
		ctx.endInit();
		CPPUNIT_ASSERT(s.numConstraints() == 1);
		ctx.attach(s2);
		CPPUNIT_ASSERT(s2.numConstraints() == 1);
		s2.assume(~e) && s2.propagate();
		s2.assume(~f) && s2.propagate();
		s2.assume(~g) && s2.propagate();
		CPPUNIT_ASSERT(s2.isTrue(h));
	}

	void testAttachDeferred() {
		Literal a = posLit(ctx.addVar( Var_t::atom_var ));
		Literal b = posLit(ctx.addVar( Var_t::atom_var ));
		Literal c = posLit(ctx.addVar( Var_t::atom_var ));
		Literal d = posLit(ctx.addVar( Var_t::atom_var ));
		ctx.setConcurrency(2);
		Solver& s = ctx.startAddConstraints();
		ClauseCreator cc(&s);
		cc.start().add(a).add(b).add(c).add(d).end();
		Solver& s2= ctx.addSolver();
		ctx.endInit(true);
		CPPUNIT_ASSERT(s2.numConstraints() == 1);
		ctx.unfreeze();
		ctx.startAddConstraints();
		cc.start().add(~a).add(~b).add(c).add(d).end();
		ctx.endInit(false);
		CPPUNIT_ASSERT(s.numConstraints() == 2);
		CPPUNIT_ASSERT(s2.numConstraints() == 1);
		ctx.unfreeze();
		ctx.startAddConstraints();
		cc.start().add(a).add(b).add(~c).add(~d).end();
		ctx.endInit(true);
		CPPUNIT_ASSERT(s.numConstraints() == 3);
		CPPUNIT_ASSERT(s2.numConstraints() == 3);
	}

	void testUnfortunateSplitSeq() {
		Literal a = posLit(ctx.addVar( Var_t::atom_var ));
		Literal b = posLit(ctx.addVar( Var_t::atom_var ));
		Literal c = posLit(ctx.addVar( Var_t::atom_var ));
		Literal d = posLit(ctx.addVar( Var_t::atom_var ));
		ctx.setConcurrency(2);
		Solver& s = ctx.startAddConstraints();
		Solver& s2= ctx.addSolver();
		ctx.endInit(true);
		
		s.assume(a)   && s.propagate();
		// new fact
		s.backtrack() && s.propagate();

		s.assume(b) && s.propagate();

		LitVec sGp;
		s.copyGuidingPath(sGp);

		sGp.push_back(~b);
		s.pushRootLevel();
		integrateGp(s2, sGp);
		sGp.pop_back();
		s.clearAssumptions();
	
		LitVec s2Gp;
		
		s2.assume(c)&& s.propagate();
		s2.copyGuidingPath(s2Gp);
		s.pushRootLevel();
		s2Gp.push_back(~c);
		integrateGp(s, s2Gp);
		s2.clearAssumptions();
		s2Gp.clear();
	
		s.assume(d)&& s.propagate();
		sGp.clear();
		s.copyGuidingPath(sGp);

		integrateGp(s2, sGp);
		CPPUNIT_ASSERT(s2.isTrue(~a));
	}

	void testSplitInc() {
		Literal a = posLit(ctx.addVar( Var_t::atom_var ));
		Literal b = posLit(ctx.addVar( Var_t::atom_var ));
		Literal c = posLit(ctx.addVar( Var_t::atom_var ));
		Literal d = posLit(ctx.addVar( Var_t::atom_var ));
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		s.assume(a) && s.propagate();
		s.assume(b) && s.propagate();
		s.assume(c) && s.propagate();
		s.assume(d) && s.propagate();
		LitVec gp;
		s.copyGuidingPath(gp);
		s.pushRootLevel();
		gp.push_back(~a);
		CPPUNIT_ASSERT(gp.size() == 1 && gp[0] == ~a && s.rootLevel() == 1);
		gp.pop_back();
		
		s.copyGuidingPath(gp);
		s.pushRootLevel();
		gp.push_back(~b);
		CPPUNIT_ASSERT(gp.size() == 2 && gp[1] == ~b && s.rootLevel() == 2);
		gp.pop_back();
		
		s.copyGuidingPath(gp);
		s.pushRootLevel();
		gp.push_back(~c);
		CPPUNIT_ASSERT(gp.size() == 3 && gp[2] == ~c && s.rootLevel() == 3);
		gp.pop_back();
	}

	void testSplitFlipped() {
		Literal a = posLit(ctx.addVar( Var_t::atom_var ));
		Literal b = posLit(ctx.addVar( Var_t::atom_var ));
		Literal c = posLit(ctx.addVar( Var_t::atom_var ));
		Literal d = posLit(ctx.addVar( Var_t::atom_var ));
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		
		LitVec gp;
		
		s.assume(a) && s.propagate();
		s.pushRootLevel();
		s.assume(b) && s.propagate();
		s.backtrack();
		
		s.assume(c) && s.propagate();
		s.backtrack();

		s.assume(d) && s.propagate();
		s.copyGuidingPath(gp);
		CPPUNIT_ASSERT(std::find(gp.begin(), gp.end(), ~b) != gp.end());
		CPPUNIT_ASSERT(std::find(gp.begin(), gp.end(), ~c) != gp.end());
	}

	void testSplitFlipToNewRoot() {
		Literal a = posLit(ctx.addVar( Var_t::atom_var ));
		Literal b = posLit(ctx.addVar( Var_t::atom_var ));
		Literal c = posLit(ctx.addVar( Var_t::atom_var ));
		Literal d = posLit(ctx.addVar( Var_t::atom_var ));
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		
		LitVec gp;
		s.assume(a) && s.propagate();
		s.copyGuidingPath(gp);
		s.pushRootLevel();
		
		s.assume(b) && s.propagate();
		s.assume(c) && s.propagate();
		
		s.backtrack(); // bt-level now 2, rootLevel = 1

		s.copyGuidingPath(gp);
		s.pushRootLevel();
		CPPUNIT_ASSERT(s.rootLevel() == s.backtrackLevel());
		s.assume(d) && s.propagate();	
		s.copyGuidingPath(gp);
		s.pushRootLevel();
		CPPUNIT_ASSERT(std::find(gp.begin(), gp.end(), ~c) != gp.end());
	}

	void testSplitImplied() {
		Literal a = posLit(ctx.addVar( Var_t::atom_var ));
		Literal b = posLit(ctx.addVar( Var_t::atom_var ));
		Literal c = posLit(ctx.addVar( Var_t::atom_var ));
		Literal d = posLit(ctx.addVar( Var_t::atom_var ));
		Literal e = posLit(ctx.addVar( Var_t::atom_var ));
		Literal f = posLit(ctx.addVar( Var_t::atom_var ));
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();

		s.assume(a) && s.propagate();
		s.assume(b) && s.propagate();
		s.pushRootLevel(2);
		
		s.assume(c);
		s.setBacktrackLevel(s.decisionLevel());
		SingleOwnerPtr<TestingConstraint> x( new TestingConstraint );
		s.force(~d, 2, x.get());

		LitVec gp;
		s.copyGuidingPath(gp);
		
		CPPUNIT_ASSERT(std::find(gp.begin(), gp.end(), ~d) != gp.end());
		s.pushRootLevel();
		s.assume(e);
		s.setBacktrackLevel(s.decisionLevel());
		s.force(~f, 2, x.get());
		
		s.copyGuidingPath(gp);
		CPPUNIT_ASSERT(std::find(gp.begin(), gp.end(), ~f) != gp.end());
	}

	void testAddShortIncremental() {
		Literal a = posLit(ctx.addVar( Var_t::atom_var ));
		Literal b = posLit(ctx.addVar( Var_t::atom_var ));
		ctx.setConcurrency(2);
		ctx.startAddConstraints();
		ctx.addBinary(a, b);
		ctx.endInit();
		CPPUNIT_ASSERT(ctx.numBinary()  == 1);
		ctx.startAddConstraints();
		ctx.addBinary(~a, ~b);
		ctx.endInit();
		CPPUNIT_ASSERT(ctx.numBinary()  == 2);
	}

	void testSwitchToMtIncremental() {
		Literal a = posLit(ctx.addVar( Var_t::atom_var ));
		Literal b = posLit(ctx.addVar( Var_t::atom_var ));
		Literal c = posLit(ctx.addVar( Var_t::atom_var ));
		Literal d = posLit(ctx.addVar( Var_t::atom_var ));
		Solver& s = ctx.startAddConstraints();
		ClauseCreator cl(&s);
		cl.start().add(a).add(b).add(c).add(d).end();
		ctx.endInit(true);
		CPPUNIT_ASSERT(s.numVars() == 4 && s.numConstraints() == 1);
		ctx.unfreeze();
		Solver& s2 = ctx.addSolver();
		CPPUNIT_ASSERT(ctx.concurrency() == 2);
		ctx.startAddConstraints();
		cl.start().add(~a).add(~b).add(~c).add(~d).end();
		ctx.endInit(true);
		CPPUNIT_ASSERT(s.numVars() == 4 && s.numConstraints() == 2);
		CPPUNIT_ASSERT(s2.numVars() == 4 && s2.numConstraints() == 2);
	}

	void testScheduleAdvance() {
		ScheduleStrategy r1 = ScheduleStrategy::geom(100,1.5,13);
		for (uint32 i = 0, m = (1u << 15)-1; i != m; ++i, r1.next()) {
			ScheduleStrategy r2 = ScheduleStrategy::geom(100,1.5,13);
			r2.advanceTo(i);
			CPPUNIT_ASSERT(r1.idx == r2.idx && r1.len == r2.len);
		}
	}
	void testLubyAdvance() {
		ScheduleStrategy r1 = ScheduleStrategy::luby(64,10);
		for (uint32 i = 0, m = (1u << 15)-1; i != m; ++i, r1.next()) {
			ScheduleStrategy r2 = ScheduleStrategy::luby(64,10);
			r2.advanceTo(i);
			CPPUNIT_ASSERT(r1.idx == r2.idx && r1.len == r2.len);
		}
	}
	void testPushAux() {
		Literal a = posLit(ctx.addVar(Var_t::atom_var));
		Literal b = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		CPPUNIT_ASSERT(s.numVars() == s.sharedContext()->numVars());

		Var aux = s.pushAuxVar();
		CPPUNIT_ASSERT(s.numVars() > s.sharedContext()->numVars());
		CPPUNIT_ASSERT(s.validVar(aux) && !s.sharedContext()->validVar(aux));
		LitVec clause;
		clause.push_back(posLit(aux));
		clause.push_back(a);
		clause.push_back(b);
		ClauseCreator::create(s, clause, 0, Constraint_t::learnt_conflict);
		CPPUNIT_ASSERT(s.sharedContext()->numTernary() == 0);
		CPPUNIT_ASSERT(s.numLearntConstraints() == 1);
		s.assume(~a) && s.propagate();
		s.assume(~b) && s.propagate();
		CPPUNIT_ASSERT(s.isTrue(posLit(aux)));
		s.popAuxVar();
		CPPUNIT_ASSERT(s.decisionLevel() < 2u);
		CPPUNIT_ASSERT(s.numVars() == s.sharedContext()->numVars());
	}
	void testPushAuxFact() {
		Literal a = posLit(ctx.addVar(Var_t::atom_var));
		Literal b = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		Var aux = s.pushAuxVar();
		LitVec clause;
		clause.push_back(posLit(aux));
		clause.push_back(a);
		ClauseCreator::create(s, clause, 0, Constraint_t::learnt_conflict);
		s.force(~a) && s.propagate();
		s.force(b)  && s.simplify();
		CPPUNIT_ASSERT(s.numFreeVars() == 0);
		s.popAuxVar();
		CPPUNIT_ASSERT(s.numFreeVars() == 0 && s.validVar(aux) == false);
	}
	void testPopAuxRemovesConstraints() {
		Literal a = posLit(ctx.addVar(Var_t::atom_var));
		Literal b = posLit(ctx.addVar(Var_t::atom_var));
		Literal c = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		Var aux = s.pushAuxVar();
		LitVec clause;
		clause.push_back(a);
		clause.push_back(b);
		clause.push_back(c);
		clause.push_back(posLit(aux));
		ClauseCreator::create(s, clause, 0, Constraint_t::learnt_conflict);
		clause.clear();
		clause.push_back(a);
		clause.push_back(b);
		clause.push_back(~c);
		clause.push_back(negLit(aux));
		ClauseCreator::create(s, clause, 0, Constraint_t::learnt_conflict);
		CPPUNIT_ASSERT(s.numLearntConstraints() == 2);
		s.popAuxVar();
		CPPUNIT_ASSERT(s.numLearntConstraints() == 0);
	}
	void testPopAuxMaintainsQueue() {
		Literal a = posLit(ctx.addVar(Var_t::atom_var));
		Literal b = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		ctx.endInit();
		Var aux = s.pushAuxVar();
		s.force(a, 0); s.propagate();
		s.force(posLit(aux), 0);
		s.force(b, 0);
		s.popAuxVar();
		CPPUNIT_ASSERT(s.isTrue(a) && s.isTrue(b) && s.queueSize() == 1 && s.assignment().units() == 1);
	}

	void testIncrementalAux() {
		Literal a = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		Solver& s2= ctx.addSolver();
		ctx.endInit(true);
		Var aux   = s2.pushAuxVar();
		CPPUNIT_ASSERT(!ctx.validVar(aux) && !s.validVar(aux));
		LitVec clause;
		clause.push_back(a);
		clause.push_back(posLit(aux));
		ClauseCreator::create(s2, clause, 0, Constraint_t::learnt_conflict);
		ctx.unfreeze();
		Var n     = ctx.addVar(Var_t::atom_var);
		ctx.startAddConstraints();
		ctx.endInit(true);
		s2.assume(negLit(n)) && s2.propagate();
		CPPUNIT_ASSERT(s2.value(a.var()) == value_free);
	}

	void testUnfreezeStepBug() {
		Literal a = posLit(ctx.addVar(Var_t::atom_var));
		Literal b = posLit(ctx.addVar(Var_t::atom_var));
		ctx.requestStepVar();
		Solver& s = ctx.startAddConstraints();
		Solver& s2= ctx.addSolver();
		ctx.addBinary(~a, b);
		ctx.endInit(true);
		s2.force(b);
		ctx.unfreeze();
		ctx.endInit(true);
		CPPUNIT_ASSERT(s.force(a) && s.propagate());
		CPPUNIT_ASSERT(s.isTrue(b));
	}
	void testRemoveConstraint() {
		ctx.requestStepVar();
		Solver& s = ctx.startAddConstraints();
		Solver& s2= ctx.addSolver();
		ctx.add(new TestingConstraint());
		ctx.endInit(true);
		CPPUNIT_ASSERT(s2.numConstraints() == 1);
		ctx.removeConstraint(0, true);
		CPPUNIT_ASSERT(s.numConstraints() == 0);
		CPPUNIT_ASSERT(s2.numConstraints() == 1);
		ctx.unfreeze();
		ctx.startAddConstraints();
		ctx.add(new TestingConstraint());
		ctx.add(new TestingConstraint());
		ctx.endInit(true);
		CPPUNIT_ASSERT(s.numConstraints() == 2);
		CPPUNIT_ASSERT(s2.numConstraints() == 3);
	}
private:
	SharedContext ctx;
	void integrateGp(Solver& s, LitVec& gp) {
		s.clearAssumptions();
		for (LitVec::size_type i = 0; i != gp.size(); ++i) {
			if (s.value(gp[i].var()) == value_free) {
				s.assume(gp[i]) && s.propagate();
				s.pushRootLevel();
			}
		}
	}
	LitVec addBinary() {
		LitVec r;
		r.push_back( posLit(ctx.addVar(Var_t::atom_var)) );
		r.push_back( posLit(ctx.addVar(Var_t::atom_var)) );
		ctx.startAddConstraints();
		ctx.addBinary(r[0], r[1]);
		ctx.endInit();
		return r;
	}
	LitVec addTernary() {
		LitVec r;
		r.push_back( posLit(ctx.addVar(Var_t::atom_var)) );
		r.push_back( posLit(ctx.addVar(Var_t::atom_var)) );
		r.push_back( posLit(ctx.addVar(Var_t::atom_var)) );
		ctx.startAddConstraints();
		ctx.addTernary(r[0], r[1],r[2]);
		ctx.endInit();
		return r;
	}
};
CPPUNIT_TEST_SUITE_REGISTRATION(SolverTest);
} } 

