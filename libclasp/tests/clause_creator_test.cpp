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
#include <algorithm>
#include <clasp/clause.h>
#include <clasp/solver.h>
namespace Clasp { namespace Test {
using namespace Clasp::mt;
class ClauseCreatorTest : public CppUnit::TestFixture {

  CPPUNIT_TEST_SUITE(ClauseCreatorTest);
	CPPUNIT_TEST(testEmptyClauseIsFalse);	
	CPPUNIT_TEST(testFactsAreAsserted);
	CPPUNIT_TEST(testTopLevelSATClausesAreNotAdded);
	CPPUNIT_TEST(testTopLevelFalseLitsAreRemoved);
	CPPUNIT_TEST(testAddBinaryClause);
	CPPUNIT_TEST(testAddTernaryClause);
	CPPUNIT_TEST(testAddGenericClause);
	CPPUNIT_TEST(testCreatorAssertsFirstLit);
	CPPUNIT_TEST(testCreatorInitsWatches);
	CPPUNIT_TEST(testCreatorNotifiesHeuristic);
	CPPUNIT_TEST(testCreatorAddLitBug);

	CPPUNIT_TEST(testCreatorSimplifyRemovesDuplicates);
	CPPUNIT_TEST(testCreatorSimplifyFindsTauts);
	CPPUNIT_TEST(testCreatorSimplifyMovesWatch);
	CPPUNIT_TEST(testCreatorSimplifyBug);

	CPPUNIT_TEST(testCreateNonAssertingLearntClause);
	CPPUNIT_TEST(testCreateLearntClauseConflict);
	CPPUNIT_TEST(testCreateNonAssertingLearntClauseAsserting);
	CPPUNIT_TEST(testCreateBogusUnit);
	
	CPPUNIT_TEST(testInitWatches);
	CPPUNIT_TEST(testIntegrateEmpty);
	CPPUNIT_TEST(testIntegrateUnit);
	CPPUNIT_TEST(testIntegrateUnitSAT);
	CPPUNIT_TEST(testIntegrateConflict);
	CPPUNIT_TEST(testIntegrateAssertingConflict);
	CPPUNIT_TEST(testIntegrateAssertingConflictBelowRoot);
	CPPUNIT_TEST(testIntegrateConflictBelowRoot);
	CPPUNIT_TEST(testIntegrateSATBug1);
	CPPUNIT_TEST(testIntegrateSATBug2);
	CPPUNIT_TEST(testIntegrateSATBug3);
	CPPUNIT_TEST(testIntegrateSATBug4);
	CPPUNIT_TEST(testIntegrateKnownOrderBug);
	CPPUNIT_TEST(testIntegrateNotConflictingBug);
	CPPUNIT_TEST(testIntegrateSimplify);
	CPPUNIT_TEST(testIntegrateSAT);
	CPPUNIT_TEST(testIntegrateUnsat);
	CPPUNIT_TEST(testIntegrateAssertingBelowBT);
	CPPUNIT_TEST(testIntegrateConflictBelowBT);
	
	CPPUNIT_TEST(testFactsAreRemovedFromLearnt);
	CPPUNIT_TEST_SUITE_END();	
public:
	ClauseCreatorTest() {
		a = posLit(ctx.addVar(Var_t::atom_var));
		b = posLit(ctx.addVar(Var_t::atom_var));
		c = posLit(ctx.addVar(Var_t::atom_var));
		d = posLit(ctx.addVar(Var_t::atom_var));
		e = posLit(ctx.addVar(Var_t::atom_var));
		f = posLit(ctx.addVar(Var_t::atom_var));
		creator.setSolver(*ctx.master());
		ctx.startAddConstraints(1);
	}
	void testEmptyClauseIsFalse() {
		CPPUNIT_ASSERT_EQUAL(false, (bool)creator.start().end());
	}
	
	void testFactsAreAsserted() {
		CPPUNIT_ASSERT_EQUAL(true, (bool)creator.start().add(a).end());
		CPPUNIT_ASSERT_EQUAL(true, solver().isTrue(a));
	}
	void testTopLevelSATClausesAreNotAdded() {
		solver().force(a, 0);
		CPPUNIT_ASSERT_EQUAL(true, (bool)creator.start().add(a).add(b).end());
		CPPUNIT_ASSERT_EQUAL(0u, ctx.numConstraints());
	}
	void testTopLevelFalseLitsAreRemoved() {
		solver().force(~a, 0);
		CPPUNIT_ASSERT_EQUAL(true, (bool)creator.start().add(a).add(b).end());
		CPPUNIT_ASSERT_EQUAL(0u, ctx.numConstraints());
		CPPUNIT_ASSERT_EQUAL(true, solver().isTrue(b));
	}
	void testAddBinaryClause() {
		CPPUNIT_ASSERT_EQUAL(true, (bool)creator.start().add(a).add(b).end());
		CPPUNIT_ASSERT_EQUAL(1u, ctx.numConstraints());
		CPPUNIT_ASSERT_EQUAL(1u, ctx.numBinary());
	}
	void testAddTernaryClause() {
		CPPUNIT_ASSERT_EQUAL(true, (bool)creator.start().add(a).add(b).add(c).end());
		CPPUNIT_ASSERT_EQUAL(1u, ctx.numConstraints());
		CPPUNIT_ASSERT_EQUAL(1u, ctx.numTernary());
	}
	void testAddGenericClause() {
		CPPUNIT_ASSERT_EQUAL(true, (bool)creator.start().add(a).add(b).add(c).add(d).end());		
		CPPUNIT_ASSERT_EQUAL(1u, ctx.numConstraints());
	}

	void testCreatorAssertsFirstLit() {
		ctx.endInit();
		solver().assume(~b);
		solver().assume(~c);
		solver().assume(~d);
		solver().propagate();
		CPPUNIT_ASSERT_EQUAL(true, (bool)creator.start(Constraint_t::learnt_conflict).add(a)
			.add(b).add(c).add(d).end());

		CPPUNIT_ASSERT_EQUAL(true, solver().isTrue(a));
		CPPUNIT_ASSERT_EQUAL(false, solver().hasConflict());
		CPPUNIT_ASSERT_EQUAL(1u, solver().numLearntConstraints());
	}

	void testCreatorInitsWatches() {
		ctx.endInit();
		solver().assume(~b);
		solver().assume(~c);
		solver().assume(~d);
		
		creator.start(Constraint_t::learnt_conflict).add(a).add(b).add(d).add(c);
		CPPUNIT_ASSERT_EQUAL(true, (bool)creator.end());	// asserts a
		solver().undoUntil(2);	// clear a and d
		solver().assume(~d);		// hopefully d was watched.
		solver().propagate();
		CPPUNIT_ASSERT_EQUAL( value_true, solver().value(a.var()) );
	}
	void testCreatorNotifiesHeuristic() {
		struct FakeHeu : public SelectFirst {
			void newConstraint(const Solver&, const Literal*, LitVec::size_type size, ConstraintType t) {
				clSizes_.push_back(size);
				clTypes_.push_back(t);
			}
			std::vector<LitVec::size_type> clSizes_;
			std::vector<ConstraintType> clTypes_;
		}*heu = new FakeHeu;
		solver().setHeuristic(heu);
		CPPUNIT_ASSERT_EQUAL(true, (bool)creator.start().add(a).add(b).add(c).add(d).end());
		ctx.endInit();
		solver().assume(a);
		solver().assume(b);
		solver().propagate();

		CPPUNIT_ASSERT_EQUAL(true, (bool)creator.start(Constraint_t::learnt_conflict).add(c)
			.add(~a).add(~b).end());

		CPPUNIT_ASSERT_EQUAL(true, (bool)creator.start(Constraint_t::learnt_loop).add(c)
			.add(~a).add(~b).end(0));

		CPPUNIT_ASSERT_EQUAL(uint32(3), (uint32)heu->clSizes_.size());
		CPPUNIT_ASSERT_EQUAL(uint32(4), (uint32)heu->clSizes_[0]);
		CPPUNIT_ASSERT_EQUAL(uint32(3), (uint32)heu->clSizes_[1]);
		CPPUNIT_ASSERT_EQUAL(uint32(3), (uint32)heu->clSizes_[2]);

		CPPUNIT_ASSERT_EQUAL(Constraint_t::static_constraint, heu->clTypes_[0]);
		CPPUNIT_ASSERT_EQUAL(Constraint_t::learnt_conflict, heu->clTypes_[1]);
		CPPUNIT_ASSERT_EQUAL(Constraint_t::learnt_loop, heu->clTypes_[2]);
	}

	void testCreatorAddLitBug() {
		creator.start(Constraint_t::learnt_conflict).add(a);
		solver().assume(b) && solver().propagate();
		creator.add(~b);
		solver().assume(c) && solver().propagate();
		creator.add(~c);
		solver().assume(d) && solver().propagate();
		creator.add(~d);
		creator.end();
		CPPUNIT_ASSERT_MESSAGE("TODO: Fix me!", creator[0] == a);
	}

	void testCreatorSimplifyRemovesDuplicates() {
		creator.start().add(a).add(b).add(c).add(a).add(b).add(d).prepare(true);
		CPPUNIT_ASSERT(creator.size() == 4);
		CPPUNIT_ASSERT(creator[0] == a);
		CPPUNIT_ASSERT(creator[1] == b);
		CPPUNIT_ASSERT(creator[2] == c);
		CPPUNIT_ASSERT(creator[3] == d);
	}
	void testCreatorSimplifyFindsTauts() {
		creator.start().add(a).add(b).add(c).add(a).add(b).add(~a).end(ClauseCreator::clause_force_simplify);
		CPPUNIT_ASSERT(0 == ctx.numConstraints());
	}
	void testCreatorSimplifyMovesWatch() {
		ctx.endInit();
		solver().assume(a); solver().propagate();
		solver().assume(b); solver().propagate();
		creator.start(Constraint_t::learnt_loop);
		creator.add(~a).add(~b).add(~b).add(~a).add(c).add(d).prepare(true);
		CPPUNIT_ASSERT(creator.size() == 4);
		CPPUNIT_ASSERT_EQUAL(c, creator[0]);
		CPPUNIT_ASSERT_EQUAL(d, creator[1]);
	}

	void testCreatorSimplifyBug() {
		LitVec clause;
		clause.push_back(negLit(0));
		clause.push_back(a);
		clause.push_back(b);
		ClauseCreator::prepare(*ctx.master(), clause, ClauseCreator::clause_force_simplify);
		CPPUNIT_ASSERT(clause.size() == 2);
	}

	void testCreateNonAssertingLearntClause() {
		ctx.endInit();
		solver().assume(a); solver().propagate();
		solver().assume(b); solver().propagate();
		creator.start(Constraint_t::learnt_loop);
		creator.add(~a).add(~b).add(c).add(d);
		CPPUNIT_ASSERT(creator.end());
		CPPUNIT_ASSERT_EQUAL(c, creator[0]);
		CPPUNIT_ASSERT_EQUAL(d, creator[1]);
		CPPUNIT_ASSERT(solver().numLearntConstraints() == 1);

		solver().undoUntil(0);
		// test with a short clause
		solver().assume(a); solver().propagate();
		creator.start(Constraint_t::learnt_loop);
		creator.add(~a).add(b).add(c);
		CPPUNIT_ASSERT(creator.end());
		CPPUNIT_ASSERT_EQUAL(b, creator[0]);
		CPPUNIT_ASSERT_EQUAL(c, creator[1]);
		CPPUNIT_ASSERT(ctx.numLearntShort() == 1);
	}
	void testCreateLearntClauseConflict() {
		ctx.endInit();
		solver().assume(a); solver().force(b,0); solver().propagate();// level 1
		solver().assume(c); solver().propagate();                     // level 2
		solver().assume(d); solver().propagate();                     // level 3
		solver().assume(f); solver().propagate();                     // level 4

		creator.start(Constraint_t::learnt_loop);
		creator.add(~c).add(~a).add(~d).add(~b); // 2 1 3 1
		CPPUNIT_ASSERT_EQUAL(false, (bool)creator.end());
		// make sure we watch highest levels, i.e. 3 and 2
		CPPUNIT_ASSERT_EQUAL(~d, creator[0]);
		CPPUNIT_ASSERT_EQUAL(~c, creator[1]);
		CPPUNIT_ASSERT(solver().numLearntConstraints() == 0);

		
		solver().undoUntil(0);
		// test with a short clause
		solver().assume(a); solver().propagate();// level 1
		solver().assume(c); solver().propagate();// level 2
		creator.start(Constraint_t::learnt_loop);
		creator.add(~a).add(~c);
		CPPUNIT_ASSERT_EQUAL(false, (bool)creator.end());
		CPPUNIT_ASSERT_EQUAL(~c, creator[0]);
		CPPUNIT_ASSERT_EQUAL(~a, creator[1]);
		CPPUNIT_ASSERT(ctx.numBinary() == 0);
	}

	void testCreateNonAssertingLearntClauseAsserting() {
		ctx.endInit();
		solver().assume(a); solver().force(b,0); solver().propagate();// level 1
		solver().assume(c); solver().propagate();                     // level 2
		creator.start(Constraint_t::learnt_loop);
		creator.add(~c).add(~a).add(d).add(~b);                       // 2 1 Free 1
		CPPUNIT_ASSERT_EQUAL(true, (bool)creator.end());
		// make sure we watch the right lits, i.e. d (free) and ~c (highest DL)
		CPPUNIT_ASSERT_EQUAL(d, creator[0]);
		CPPUNIT_ASSERT_EQUAL(~c, creator[1]);
		CPPUNIT_ASSERT_EQUAL(true, solver().isTrue(d));
		CPPUNIT_ASSERT(solver().numLearntConstraints() == 1);
		// test with a short clause
		solver().undoUntil(0);
		solver().reduceLearnts(1.0f);
		solver().assume(a); solver().force(b,0); solver().propagate();// level 1
		solver().assume(c); solver().propagate();                     // level 2
		creator.start(Constraint_t::learnt_loop);
		creator.add(~c).add(~a).add(d);                               // 2 1 Free
		CPPUNIT_ASSERT_EQUAL(true, (bool)creator.end());
		// make sure we watch the right lits, i.e. d (free) and ~c (highest DL)
		CPPUNIT_ASSERT_EQUAL(d, creator[0]);
		CPPUNIT_ASSERT_EQUAL(~c, creator[1]);
		CPPUNIT_ASSERT_EQUAL(true, solver().isTrue(d));
	}

	void testCreateBogusUnit() {
		solver().assume(a) && solver().propagate();
		solver().assume(~b) && solver().propagate();
		solver().force(~d,0) && solver().propagate();
		solver().assume(~c) && solver().propagate();
		CPPUNIT_ASSERT(solver().decisionLevel() == 3);
		
		creator.start(Constraint_t::learnt_other).add(d).add(b).add(c).add(a);
		CPPUNIT_ASSERT(ClauseCreator::status(solver(), &creator.lits()[0], &creator.lits()[0] + creator.size()) == ClauseCreator::status_sat);

		ClauseCreator::Result r = creator.end();
		CPPUNIT_ASSERT_EQUAL(true, r.ok());
		CPPUNIT_ASSERT(solver().decisionLevel() == 3);
	}

	void testInitWatches() {
		LitVec cl;
		cl.push_back(a);
		cl.push_back(b);
		cl.push_back(c);
		cl.push_back(d);
		solver().assume(~b)   && solver().propagate();
		solver().force(~c, 0) && solver().propagate();
		solver().assume(~a)   && solver().propagate();
		solver().assume(d)    && solver().propagate();
		// aF@2 bF@1 cF@1 dT@3 -> dT@3 aF@2 cF@1 bF@1
		LitVec temp = cl;
		ClauseCreator::prepare(solver(), temp, 0);
		CPPUNIT_ASSERT(temp[0] == d);
		CPPUNIT_ASSERT(temp[1] == a);
		
		SharedLiterals* p(SharedLiterals::newShareable(cl, Constraint_t::learnt_other));
		ClauseCreator::Result r = ClauseCreator::integrate(solver(), p, ClauseCreator::clause_no_add);
		temp.clear();
		r.local->clause()->toLits(temp);
		CPPUNIT_ASSERT(temp[0] == d);
		CPPUNIT_ASSERT(temp[1] == a);
		r.local->destroy(&solver(), true);
	}

	void testIntegrateEmpty() {
		LitVec cl;
		solver().assume(~a) && solver().propagate();
		solver().pushRootLevel(solver().decisionLevel());
		SharedLiterals* p(SharedLiterals::newShareable(cl, Constraint_t::learnt_other));
		ClauseCreator::Result r = ClauseCreator::integrate(solver(), p, 0);
		CPPUNIT_ASSERT_EQUAL(false, r.ok());
		CPPUNIT_ASSERT_EQUAL(true, solver().hasConflict());
		CPPUNIT_ASSERT_EQUAL(false, solver().clearAssumptions());
	}
	void testIntegrateUnit() {
		solver().assume(a) && solver().propagate();
		solver().assume(b) && solver().propagate();
		solver().assume(c) && solver().propagate();
		solver().assume(d) && solver().propagate();
		solver().pushRootLevel(solver().decisionLevel());
		solver().assume(e) && solver().propagate();

		LitVec cl; 
		// ~a ~b ~c f -> Unit: f@3
		cl.push_back(~a); cl.push_back(f);
		cl.push_back(~c); cl.push_back(~b);
		SharedLiterals* p(SharedLiterals::newShareable(cl, Constraint_t::learnt_other));
		ClauseCreator::integrate(solver(), p, 0);
		CPPUNIT_ASSERT(solver().isTrue(f));
		CPPUNIT_ASSERT(solver().decisionLevel() == solver().rootLevel());
		solver().popRootLevel();
		solver().backtrack() && solver().propagate();
		CPPUNIT_ASSERT(solver().isTrue(f));
		CPPUNIT_ASSERT(solver().decisionLevel() == solver().rootLevel());
		solver().popRootLevel();
		solver().backtrack() && solver().propagate();
		CPPUNIT_ASSERT_EQUAL(false, solver().isTrue(f));
		CPPUNIT_ASSERT(solver().value(c.var()) == value_free);
	}

	void testIntegrateUnitSAT() {
		solver().assume(a) && solver().propagate();
		LitVec cl; 
		cl.push_back(a);
		SharedLiterals* p(SharedLiterals::newShareable(cl, Constraint_t::learnt_other));
		ClauseCreator::integrate(solver(), p, 0);
		CPPUNIT_ASSERT(solver().isTrue(a));
		CPPUNIT_ASSERT(solver().decisionLevel() == 0);
	}

	void testIntegrateConflict() {
		solver().assume(a) && solver().propagate();
		solver().assume(b) && solver().propagate();
		solver().assume(c) && solver().propagate();
		solver().force(d, 0) && solver().propagate();
		
		// ~a ~b ~c ~d -> conflicting@3
		LitVec cl;
		cl.push_back(~a); cl.push_back(~c); cl.push_back(~b); cl.push_back(~d);
		SharedLiterals* p(SharedLiterals::newShareable(cl, Constraint_t::learnt_other));
		ClauseCreator::Result r = ClauseCreator::integrate(solver(), p, 0);
		CPPUNIT_ASSERT(!r.ok());
		CPPUNIT_ASSERT(r.local != 0);
		CPPUNIT_ASSERT(solver().hasConflict());
	}

	void testIntegrateAssertingConflict() {
		solver().assume(a) && solver().propagate();
		solver().assume(b) && solver().propagate();
		solver().assume(c) && solver().propagate();
		solver().assume(d) && solver().propagate();
		
		// ~a ~b ~c -> Conflict @3
		LitVec cl;
		cl.push_back(~a); cl.push_back(~c); cl.push_back(~b);
		SharedLiterals* p(SharedLiterals::newShareable(cl, Constraint_t::learnt_other));
		ClauseCreator::integrate(solver(), p, 0);
		CPPUNIT_ASSERT(solver().decisionLevel() == uint32(2));
	}

	void testIntegrateAssertingConflictBelowRoot() {
		solver().assume(a) && solver().propagate();
		solver().assume(b) && solver().propagate();
		solver().assume(d) && solver().propagate();
		solver().pushRootLevel(solver().decisionLevel());
		solver().assume(c) && solver().propagate();
		// ~a ~b ~c -> Conflict @3, Asserting @2
		LitVec cl;
		cl.push_back(~a); cl.push_back(~c); cl.push_back(~b);
		SharedLiterals* p(SharedLiterals::newShareable(cl, Constraint_t::learnt_other));
		ClauseCreator::integrate(solver(), p, 0);
		CPPUNIT_ASSERT(solver().decisionLevel() == uint32(3));
		solver().popRootLevel();
		solver().backtrack() && solver().propagate();
		CPPUNIT_ASSERT(solver().isTrue(~c));
	}
	void testIntegrateConflictBelowRoot() {
		LitVec cl;
		cl.push_back(a); cl.push_back(b); cl.push_back(c);
		solver().assume(~a) && solver().propagate();
		solver().assume(~b) && solver().propagate();
		solver().assume(~c) && solver().propagate();
		solver().assume(~d) && solver().propagate();
		solver().pushRootLevel(solver().decisionLevel());
		SharedLiterals* p(SharedLiterals::newShareable(cl, Constraint_t::learnt_other));
		ClauseCreator::Result r = ClauseCreator::integrate(solver(), p, ClauseCreator::clause_explicit);
		CPPUNIT_ASSERT_EQUAL(false, r.ok());
		CPPUNIT_ASSERT_EQUAL(uint32(1), solver().numLearntConstraints());
	}
	
	void testIntegrateSATBug1() {
		LitVec cl;
		cl.push_back(d); cl.push_back(b); cl.push_back(a); cl.push_back(c);
		solver().assume(~a) && solver().propagate();
		solver().assume(b) && solver().propagate();
		solver().assume(~d) && solver().propagate();
		SharedLiterals* p(SharedLiterals::newShareable(cl, Constraint_t::learnt_other));
		ClauseCreator::Result r = ClauseCreator::integrate(solver(), p, 0);
		CPPUNIT_ASSERT_EQUAL(true, r.ok());
		CPPUNIT_ASSERT(3u == solver().numAssignedVars());
	}
	void testIntegrateSATBug2() {
		LitVec cl;
		cl.push_back(d); cl.push_back(b); cl.push_back(c); cl.push_back(a);
		solver().assume(~a) && solver().propagate();
		solver().assume(b) && solver().propagate();
		solver().assume(~d) && solver().propagate();
		solver().force(c,0) && solver().propagate();
		SharedLiterals* p(SharedLiterals::newShareable(cl, Constraint_t::learnt_other));
		ClauseCreator::Result r = ClauseCreator::integrate(solver(), p, 0);
		CPPUNIT_ASSERT_EQUAL(true, r.ok());
	}

	void testIntegrateSATBug3() {
		LitVec cl;
		cl.push_back(d); cl.push_back(b); cl.push_back(c); cl.push_back(a);
		solver().assume(~a) && solver().propagate();
		solver().assume(~b) && solver().propagate();
		solver().force(~d,0) && solver().propagate();
		solver().assume(c) && solver().propagate();
		CPPUNIT_ASSERT(solver().decisionLevel() == 3);
		SharedLiterals* p(SharedLiterals::newShareable(cl, Constraint_t::learnt_other));
		ClauseCreator::Result r = ClauseCreator::integrate(solver(), p, ClauseCreator::clause_not_sat);
		
		CPPUNIT_ASSERT_EQUAL(true, r.ok());
		CPPUNIT_ASSERT(solver().decisionLevel() == 2);
		CPPUNIT_ASSERT(solver().isTrue(c));
	}

	void testIntegrateSATBug4() {
		LitVec cl;
		cl.push_back(a); cl.push_back(b);
		solver().force(~a, 0);
		solver().assume(b);
		SharedLiterals* p(SharedLiterals::newShareable(cl,Constraint_t::learnt_other));
		CPPUNIT_ASSERT((ClauseCreator::status(solver(), p->begin(), p->end()) & ClauseCreator::status_unit) != 0);
		ClauseCreator::integrate(solver(), p, ClauseCreator::clause_explicit);
	}

	void testIntegrateKnownOrderBug() {
		LitVec cl;
		cl.push_back(a);
		SharedLiterals* p(SharedLiterals::newShareable(cl,Constraint_t::learnt_other));
		CPPUNIT_ASSERT((ClauseCreator::status(solver(), p->begin(), p->end()) & ClauseCreator::status_unit) != 0);
		ClauseCreator::integrate(solver(), p, ClauseCreator::clause_no_prepare);
		CPPUNIT_ASSERT(solver().isTrue(a));
	}

	void testIntegrateNotConflictingBug() {
		LitVec cl;
		cl.push_back(a); cl.push_back(b);
		SharedLiterals* p(SharedLiterals::newShareable(cl,Constraint_t::learnt_other));
		solver().assume(~a) && solver().propagate();
		solver().force(~b,0)&& solver().propagate();
		CPPUNIT_ASSERT((ClauseCreator::status(solver(), p->begin(), p->end()) & ClauseCreator::status_unsat) != 0);
		ClauseCreator::Result r = ClauseCreator::integrate(solver(), p, ClauseCreator::clause_not_conflict);
		CPPUNIT_ASSERT(r.ok() == false);
		CPPUNIT_ASSERT(r.local == 0);
	}
	void testIntegrateSimplify() {
		LitVec cl;
		cl.push_back(a); cl.push_back(b); cl.push_back(c);
		cl.push_back(d); cl.push_back(e); cl.push_back(f);
		SharedLiterals* p(SharedLiterals::newShareable(cl,Constraint_t::learnt_other));
		solver().force(~d, 0) && solver().propagate();
		solver().assume(~a)   && solver().propagate();
		ClauseCreator::Result r = ClauseCreator::integrate(solver(), p, ClauseCreator::clause_no_add);
		CPPUNIT_ASSERT(r.ok());
		CPPUNIT_ASSERT(r.local != 0);
		cl.clear();
		r.local->toLits(cl);
		CPPUNIT_ASSERT(cl.size() == 5 && std::find(cl.begin(), cl.end(), d) == cl.end());
	}
	void testIntegrateSAT() {
		LitVec cl;
		cl.push_back(a); cl.push_back(b); cl.push_back(c); cl.push_back(d);
		solver().assume(~a) && solver().propagate();
		solver().assume(b) && solver().propagate();
		solver().assume(~d) && solver().propagate();
		do {
			SharedLiterals* p(SharedLiterals::newShareable(cl, Constraint_t::learnt_other));
			ClauseCreator::Result r = ClauseCreator::integrate(solver(), p, ClauseCreator::clause_not_sat);
			CPPUNIT_ASSERT_EQUAL(true, r.ok());
			CPPUNIT_ASSERT(solver().numAssignedVars() == 3);
		} while (std::next_permutation(cl.begin(), cl.end()));
		CPPUNIT_ASSERT(solver().numLearntConstraints() == 0);
	}

	void testIntegrateUnsat() {
		solver().force(~a,0) && solver().propagate();
		solver().assume(b);
		LitVec cl;
		cl.push_back(a);
		SharedLiterals* p(SharedLiterals::newShareable(cl, Constraint_t::learnt_other));
		ClauseCreator::Result r = ClauseCreator::integrate(solver(), p, 0);
		CPPUNIT_ASSERT_EQUAL(false, r.ok());
		CPPUNIT_ASSERT(0 == r.local);
		CPPUNIT_ASSERT_EQUAL(uint32(0), solver().decisionLevel());
	}

	void testIntegrateAssertingBelowBT() {
		solver().assume(a) && solver().propagate();
		solver().assume(b) && solver().propagate();
		solver().assume(c) && solver().propagate();
		solver().assume(d) && solver().propagate();
		solver().setBacktrackLevel(solver().decisionLevel());
		// ~a ~b ~c -> Conflict @3, Asserting @2
		LitVec cl;
		cl.push_back(~a); cl.push_back(~c); cl.push_back(~b);
		SharedLiterals* p(SharedLiterals::newShareable(cl, Constraint_t::learnt_other));
		ClauseCreator::Result r = ClauseCreator::integrate(solver(), p, 0);
		CPPUNIT_ASSERT_EQUAL(false, r.ok());
		solver().backtrack();
		CPPUNIT_ASSERT(solver().isTrue(~c));
		CPPUNIT_ASSERT_EQUAL(uint32(2), solver().decisionLevel());
		solver().backtrack();
		CPPUNIT_ASSERT(!solver().isTrue(~c));
	}

	void testIntegrateConflictBelowBT() {
		solver().assume(a) && solver().propagate();
		solver().assume(b) && solver().force(c, 0) && solver().propagate();
		solver().assume(d) && solver().propagate();
		solver().assume(e) && solver().propagate();
		solver().setBacktrackLevel(solver().decisionLevel());
		// ~a ~b ~c -> Conflict @2
		LitVec cl;
		cl.push_back(~a); cl.push_back(~c); cl.push_back(~b);
		SharedLiterals* p(SharedLiterals::newShareable(cl, Constraint_t::learnt_other));
		ClauseCreator::Result r = ClauseCreator::integrate(solver(), p, 0);
		CPPUNIT_ASSERT_EQUAL(false, r.ok());
		CPPUNIT_ASSERT_EQUAL(true, solver().resolveConflict());
		CPPUNIT_ASSERT_EQUAL(uint32(1), solver().decisionLevel());
	}


	void testFactsAreRemovedFromLearnt() {
		ctx.enableStats(1);
		ctx.addUnary(a);
		ctx.endInit();
		solver().assume(~b) && solver().propagate();
		creator.start(Constraint_t::learnt_conflict);
		creator.add(b).add(c).add(~a).end();

		CPPUNIT_ASSERT(1u == ctx.numLearntShort());
		CPPUNIT_ASSERT(ctx.master()->stats.extra->lits[0] == 2);
	}
private:
	const Solver& solver() const { return *ctx.master(); }
	Solver&       solver()       { return *ctx.master(); }
	SharedContext ctx;
	ClauseCreator creator;
	Literal a,b,c,d,e,f;
};
CPPUNIT_TEST_SUITE_REGISTRATION(ClauseCreatorTest);
} } 
