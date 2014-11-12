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

#ifdef _MSC_VER
#pragma warning (disable : 4267) //  conversion from 'size_t' to unsigned int
#pragma once
#endif


namespace Clasp { namespace Test {

class ClauseTest : public CppUnit::TestFixture {
	CPPUNIT_TEST_SUITE(ClauseTest);
	CPPUNIT_TEST(testClauseCtorAddsWatches);
	CPPUNIT_TEST(testClauseTypes);
	CPPUNIT_TEST(testClauseActivity);

	CPPUNIT_TEST(testPropGenericClause);
	CPPUNIT_TEST(testPropGenericClauseConflict);
	CPPUNIT_TEST(testPropAlreadySatisfied);
	CPPUNIT_TEST(testPropRandomClauses);

	CPPUNIT_TEST(testReasonBumpsActivityIfLearnt);

	CPPUNIT_TEST(testSimplifySAT);

	CPPUNIT_TEST(testSimplifyUnitButNotLocked);
	CPPUNIT_TEST(testSimplifyRemovesFalseLitsBeg);
	CPPUNIT_TEST(testSimplifyRemovesFalseLitsMid);
	CPPUNIT_TEST(testSimplifyRemovesFalseLitsEnd);
	CPPUNIT_TEST(testSimplifyShortRemovesFalseLitsBeg);
	CPPUNIT_TEST(testSimplifyShortRemovesFalseLitsMid);
	CPPUNIT_TEST(testSimplifyShortRemovesFalseLitsEnd);

	CPPUNIT_TEST(testStrengthen);
	CPPUNIT_TEST(testStrengthenToUnary);
	CPPUNIT_TEST(testStrengthenContracted);
	CPPUNIT_TEST(testStrengthenBug);
	CPPUNIT_TEST(testStrengthenContractedNoExtend);
	CPPUNIT_TEST(testStrengthenLocked);
	CPPUNIT_TEST(testStrengthenLockedEarly);
	CPPUNIT_TEST(testSimplifyTagged);

	CPPUNIT_TEST(testClauseSatisfied);
	CPPUNIT_TEST(testContraction);
	CPPUNIT_TEST(testNewContractedClause);

	CPPUNIT_TEST(testClone);

	CPPUNIT_TEST(testBug);

	CPPUNIT_TEST(testLoopFormulaInitialWatches);
	CPPUNIT_TEST(testSimplifyLFIfOneBodyTrue);
	CPPUNIT_TEST(testSimplifyLFIfAllAtomsFalse);
	CPPUNIT_TEST(testSimplifyLFRemovesFalseBodies);
	CPPUNIT_TEST(testSimplifyLFRemovesFalseAtoms);
	CPPUNIT_TEST(testSimplifyLFRemovesTrueAtoms);

	CPPUNIT_TEST(testLoopFormulaPropagateBody);
	CPPUNIT_TEST(testLoopFormulaPropagateBody2);
	CPPUNIT_TEST(testLoopFormulaPropagateAtoms);
	CPPUNIT_TEST(testLoopFormulaPropagateAtoms2);
	CPPUNIT_TEST(testLoopFormulaBodyConflict);
	CPPUNIT_TEST(testLoopFormulaAtomConflict);
	CPPUNIT_TEST(testLoopFormulaDontChangeSat);
	CPPUNIT_TEST(testLoopFormulaPropTrueAtomInSatClause);

	CPPUNIT_TEST(testLoopFormulaSatisfied);

	CPPUNIT_TEST(testLoopFormulaBugEq);

	CPPUNIT_TEST_SUITE_END(); 
public:
	ClauseTest() {
		a1 = posLit(ctx.addVar(Var_t::atom_var));
		a2 = posLit(ctx.addVar(Var_t::atom_var));
		a3 = posLit(ctx.addVar(Var_t::atom_var));
		b1 = posLit(ctx.addVar(Var_t::body_var));
		b2 = posLit(ctx.addVar(Var_t::body_var));
		b3 = posLit(ctx.addVar(Var_t::body_var));

		for (int i = 6; i < 15; ++i) {
			ctx.addVar(Var_t::atom_var);
		}
		ctx.startAddConstraints(10);
		solver = ctx.master();
	}
	void testClauseCtorAddsWatches() {
		ClauseHead* cl1;
		solver->add(cl1 = createClause(2,2));
		CPPUNIT_ASSERT_EQUAL(2, countWatches(*solver, cl1, clLits) );
		ClauseHead* cl2 = createClause(clLits, Constraint_t::learnt_conflict);
		solver->add(cl2);
		CPPUNIT_ASSERT_EQUAL(2,  countWatches(*solver, cl2, clLits));
	}

	void testClauseTypes() {
		Clause* cl1 = createClause(2, 2);
		LearntConstraint* cl2 = createClause(clLits, ClauseInfo(Constraint_t::learnt_conflict));
		LearntConstraint* cl3 = createClause(clLits, ClauseInfo(Constraint_t::learnt_loop));
		CPPUNIT_ASSERT_EQUAL(Constraint_t::static_constraint, cl1->type());
		CPPUNIT_ASSERT_EQUAL(Constraint_t::learnt_conflict, cl2->type());
		CPPUNIT_ASSERT_EQUAL(Constraint_t::learnt_loop, cl3->type());
		cl1->destroy();
		cl2->destroy();
		cl3->destroy();
	}

	void testClauseActivity() {
		LitVec lit;
		lit.push_back(posLit(1));
		lit.push_back(posLit(2));
		lit.push_back(posLit(3));
		lit.push_back(posLit(4));
		uint32 exp = 258;
		ClauseHead* cl1 = createClause(lit, ClauseInfo(Constraint_t::learnt_conflict).setActivity(exp));
		ClauseHead* cl2 = createClause(lit, ClauseInfo(Constraint_t::learnt_loop).setActivity(exp));
		solver->add(cl1);
		solver->add(cl2);
		while ( exp != 0 ) {
			CPPUNIT_ASSERT(cl1->activity().activity() == cl2->activity().activity() && cl1->activity().activity() == exp);
			exp >>= 1;
			cl1->decreaseActivity();
			cl2->decreaseActivity();
		}
		CPPUNIT_ASSERT(cl1->activity().activity() == cl2->activity().activity() && cl1->activity().activity() == exp);
	}

	void testPropGenericClause() {
		Clause* c;
		solver->add(c = createClause(2, 2));
		solver->assume(~clLits[0]);
		solver->propagate();
		solver->assume( ~clLits.back() );
		solver->propagate();
		
		solver->assume(~clLits[1]);
		solver->propagate();

		CPPUNIT_ASSERT_EQUAL(true, solver->isTrue( clLits[2] ) );
		CPPUNIT_ASSERT_EQUAL(true, c->locked(*solver));
		Antecedent reason = solver->reason(clLits[2]);
		CPPUNIT_ASSERT(reason == c);
		
		LitVec r;
		reason.reason(*solver, clLits[2], r);
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~clLits[0]) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~clLits[1]) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~clLits[3]) != r.end());
	}

	void testPropGenericClauseConflict() {
		Clause* c;
		solver->add(c = createClause(2, 2));
		solver->assume( ~clLits[0] );
		solver->force( ~clLits[1], 0 );
		solver->force( ~clLits[2], 0 );
		solver->force( ~clLits[3], 0 );
		
		CPPUNIT_ASSERT_EQUAL(false, solver->propagate());
		const LitVec& r = solver->conflict();
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~clLits[0]) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~clLits[1]) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~clLits[2]) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~clLits[3]) != r.end());
	}

	void testPropAlreadySatisfied() {
		Clause* c;
		solver->add(c = createClause(2, 2));

		// satisfy the clause...
		solver->force(clLits[2], 0);
		solver->propagate();

		// ...make all but one literal false
		solver->force(~clLits[0], 0);
		solver->force(~clLits[1], 0);
		solver->propagate();

		// ...and assert that the last literal is still unassigned
		CPPUNIT_ASSERT(value_free == solver->value(clLits[3].var()));
	}
	void testPropRandomClauses() {
		for (int i = 0; i != 100; ++i) {
			SharedContext cc;
			solver = cc.master();
			for (int j = 0; j < 12; ++j) { cc.addVar(Var_t::atom_var); }
			cc.startAddConstraints(1);
			Clause* c;
			solver->add( c = createRandomClause( (rand() % 10) + 2 ) );
			check(*c);
		}
	}
	
	void testReasonBumpsActivityIfLearnt() {
		clLits.push_back(posLit(1));
		clLits.push_back(posLit(2));
		clLits.push_back(posLit(3));
		clLits.push_back(posLit(4));
		ctx.endInit();
		ClauseHead* cl1 = createClause(clLits, ClauseInfo(Constraint_t::learnt_conflict));
		solver->addLearnt(cl1, (uint32)clLits.size());
		solver->assume(~clLits[0]);
		solver->propagate();
		solver->assume(~clLits[1]);
		solver->propagate();
		solver->assume(~clLits[2]);
		solver->propagate();
		
		CPPUNIT_ASSERT_EQUAL(true, solver->isTrue( clLits[3] ) );
		uint32 a = cl1->activity().activity();
		LitVec r;
		solver->reason(clLits[3], r);
		CPPUNIT_ASSERT_EQUAL(a+1, cl1->activity().activity());
	}

	void testSimplifySAT() {
		Clause* c;
		solver->add(c = createClause(3, 2));
		solver->force( ~clLits[1], 0);
		solver->force( clLits[2], 0 );
		solver->propagate();

		CPPUNIT_ASSERT_EQUAL(true, c->simplify(*solver, false));
	}
	void testSimplifyUnitButNotLocked() {
		Clause* c;
		solver->add(c = createClause(2, 2));
		solver->force( clLits[0], 0);  // SAT clause
		solver->force( ~clLits[1], 0 );
		solver->force( ~clLits[2], 0 );
		solver->force( ~clLits[3], 0 );
		solver->propagate();
		CPPUNIT_ASSERT_EQUAL(true, c->simplify(*solver, false));
	}

	void testSimplifyRemovesFalseLitsBeg() {
		Clause* c;
		
		solver->add(c = createClause(3, 3));
		CPPUNIT_ASSERT(6 == c->size());
		
		solver->force(~clLits[0], 0);
		solver->force(~clLits[1], 0);
		solver->propagate();

		CPPUNIT_ASSERT_EQUAL(false, c->simplify(*solver));
		CPPUNIT_ASSERT(4 == c->size());

		CPPUNIT_ASSERT_EQUAL(2, countWatches(*solver, c, clLits));
	}

	void testSimplifyRemovesFalseLitsMid() {
		Clause* c;
		
		solver->add(c = createClause(3, 3));
		CPPUNIT_ASSERT(6 == c->size());
		
		solver->force(~clLits[1], 0);
		solver->force(~clLits[2], 0);
		solver->propagate();

		CPPUNIT_ASSERT_EQUAL(false, c->simplify(*solver));
		CPPUNIT_ASSERT(4 == c->size());

		CPPUNIT_ASSERT_EQUAL(2, countWatches(*solver, c, clLits));
	}

	void testSimplifyShortRemovesFalseLitsBeg() {
		ClauseHead* c = createClause(2, 3);
		solver->add(c);
		
		solver->force(~clLits[0], 0);
		solver->propagate();

		CPPUNIT_ASSERT_EQUAL(false, c->simplify(*solver));
		CPPUNIT_ASSERT(4 == c->size());

		CPPUNIT_ASSERT_EQUAL(2, countWatches(*solver, c, clLits));
	}

	void testSimplifyShortRemovesFalseLitsMid() {
		ClauseHead* c = createClause(2, 3);
		solver->add(c);
		
		solver->force(~clLits[2], 0);
		solver->propagate();

		CPPUNIT_ASSERT_EQUAL(false, c->simplify(*solver));
		CPPUNIT_ASSERT(4 == c->size());

		CPPUNIT_ASSERT_EQUAL(2, countWatches(*solver, c, clLits));
	}

	void testSimplifyShortRemovesFalseLitsEnd() {
		ClauseHead* c = createClause(2, 3);
		solver->add(c);
		
		solver->force(~clLits[4], 0);
		solver->propagate();

		CPPUNIT_ASSERT_EQUAL(false, c->simplify(*solver));
		CPPUNIT_ASSERT(4 == c->size());

		CPPUNIT_ASSERT_EQUAL(2, countWatches(*solver, c, clLits));
	}

	void testStrengthen() {
		ClauseHead* c;
		clLits.push_back(a1);
		clLits.push_back(a2);
		clLits.push_back(a3);
		clLits.push_back(b1);
		clLits.push_back(b2);
		clLits.push_back(b3);
		c = createClause(clLits, ClauseInfo());
		CPPUNIT_ASSERT_EQUAL(false, c->strengthen(*solver, b2).second);
		CPPUNIT_ASSERT(c->size() == 5);
		CPPUNIT_ASSERT_EQUAL(false, c->strengthen(*solver, a3).second);
		CPPUNIT_ASSERT(c->size() == 4);
		
		CPPUNIT_ASSERT_EQUAL(true, c->strengthen(*solver, a1).second);
		CPPUNIT_ASSERT(c->size() == 3);
		c->destroy(solver, true);
	}

	void testStrengthenToUnary() {
		Literal b = posLit(ctx.addVar( Var_t::atom_var ));
		Literal x = posLit(ctx.addVar( Var_t::atom_var ));
		Literal y = posLit(ctx.addVar( Var_t::atom_var ));
		ctx.startAddConstraints();
		ctx.endInit();
		Literal a = posLit(solver->pushTagVar(true));
		solver->assume(x) && solver->propagate();
		solver->assume(y) && solver->propagate();
		solver->setBacktrackLevel(solver->decisionLevel());
		clLits.clear(); 
		clLits.push_back(b);
		clLits.push_back(~a);
		ClauseInfo extra(Constraint_t::learnt_conflict); extra.setTagged(true);
		ClauseHead* c = ClauseCreator::create(*solver, clLits, 0, extra).local;
		CPPUNIT_ASSERT(c->size() == 2);
		CPPUNIT_ASSERT(solver->isTrue(b) && solver->reason(b).constraint() == c);
		solver->backtrack() && solver->propagate();
		CPPUNIT_ASSERT(solver->isTrue(b) && solver->reason(b).constraint() == c);
		c->strengthen(*solver, ~a);
		solver->backtrack();
		CPPUNIT_ASSERT(solver->isTrue(b));
		LitVec out;
		solver->reason(b, out);
		CPPUNIT_ASSERT(out.size() == 1 && out[0] == posLit(0));
		solver->clearAssumptions();
		CPPUNIT_ASSERT(solver->isTrue(b));
	}

	void testStrengthenContracted() {
		ctx.endInit();
		LitVec lits;
		lits.push_back(a1);
		for (uint32 i = 2; i <= 12; ++i) {
			solver->assume(negLit(i));
			lits.push_back(posLit(i));
		}
		solver->strategies().compress = 4;
		ClauseHead* c = ClauseCreator::create(*solver, lits, 0, Constraint_t::learnt_conflict).local;
		uint32 si = c->size();
		c->strengthen(*solver, posLit(12));
		solver->undoUntil(solver->decisionLevel()-1);
		CPPUNIT_ASSERT(solver->value(posLit(12).var()) == value_free && si == c->size());
		solver->undoUntil(solver->level(posLit(9).var())-1);
		
		CPPUNIT_ASSERT(si+1 <= c->size());
		si = c->size();

		c->strengthen(*solver, posLit(2));
		c->strengthen(*solver, posLit(6));
		CPPUNIT_ASSERT(si == c->size());
		c->strengthen(*solver, posLit(9));
		
		c->strengthen(*solver, posLit(8));
		c->strengthen(*solver, posLit(5));
		c->strengthen(*solver, posLit(4));
		c->strengthen(*solver, posLit(3));

		CPPUNIT_ASSERT_EQUAL(false, c->strengthen(*solver, posLit(7), false).second);
		CPPUNIT_ASSERT_EQUAL(uint32(3), c->size());
		CPPUNIT_ASSERT_EQUAL(true, c->strengthen(*solver, posLit(11)).second);
		CPPUNIT_ASSERT_EQUAL(uint32(sizeof(Clause) + (9*sizeof(Literal))), ((Clause*)c)->computeAllocSize());
	}

	void testStrengthenBug() {
		ctx.endInit();
		LitVec clause;
		clause.push_back(a1);
		for (uint32 i = 2; i <= 6; ++i) {
			solver->assume(negLit(8-i)) && solver->propagate();
			clause.push_back(posLit(i));
		}
		ClauseHead* c = Clause::newContractedClause(*solver, ClauseRep::create(&clause[0], (uint32)clause.size(), ClauseInfo(Constraint_t::learnt_conflict)) , 5, true);
		solver->addLearnt(c, 5);
		uint32 si = c->size();
		CPPUNIT_ASSERT(si == 5);
		c->strengthen(*solver, posLit(4));
		LitVec clause2;
		c->toLits(clause2);
		CPPUNIT_ASSERT(clause2.size() == 5);
		for (uint32 i = 0; i != clause.size(); ++i) {
			CPPUNIT_ASSERT(std::find(clause2.begin(), clause2.end(), clause[i]) != clause2.end() || clause[i] == posLit(4));
		}
	}

	void testStrengthenContractedNoExtend() {
		ctx.endInit();
		LitVec clause;
		clause.push_back(a1);
		for (uint32 i = 2; i <= 6; ++i) {
			solver->assume(negLit(8-i)) && solver->propagate();
			clause.push_back(posLit(i));
		}
		ClauseRep   x = ClauseRep::create(&clause[0], (uint32)clause.size(), ClauseInfo(Constraint_t::learnt_conflict));
		ClauseHead* c = Clause::newContractedClause(*solver, x, 4, false);
		solver->addLearnt(c, 4);
		CPPUNIT_ASSERT(c->size() == 4);
		c->strengthen(*solver, posLit(2));
		CPPUNIT_ASSERT(c->size() == 4);
		solver->undoUntil(0);
		CPPUNIT_ASSERT(c->size() == 4);
	}

	void testStrengthenLocked() {
		Var a = ctx.addVar( Var_t::atom_var );
		Var b = ctx.addVar( Var_t::atom_var );
		Var c = ctx.addVar( Var_t::atom_var );
		ctx.startAddConstraints();
		ctx.endInit();
		Literal tag = posLit(solver->pushTagVar(true));
		solver->assume(posLit(a)) && solver->propagate();
		solver->assume(posLit(b)) && solver->propagate();
		ClauseCreator cc(solver);
		cc.start(Constraint_t::learnt_conflict).add(negLit(a)).add(negLit(b)).add(negLit(c)).add(~tag);
		ClauseHead* clause = cc.end().local;
		CPPUNIT_ASSERT(clause->locked(*solver));
		CPPUNIT_ASSERT(!clause->strengthen(*solver, ~tag).second);
		CPPUNIT_ASSERT(clause->locked(*solver));
		LitVec r;
		solver->reason(negLit(c), r);
		CPPUNIT_ASSERT(r.size() == 2);
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), posLit(a)) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), posLit(b)) != r.end());
	}

	void testStrengthenLockedEarly() {
		Literal b = posLit(ctx.addVar( Var_t::atom_var ));
		Literal c = posLit(ctx.addVar( Var_t::atom_var ));
		Literal d = posLit(ctx.addVar( Var_t::atom_var ));
		Literal x = posLit(ctx.addVar( Var_t::atom_var ));
		ctx.startAddConstraints();
		ctx.endInit();
		Literal a = posLit(solver->pushTagVar(true));
		solver->assume(b) && solver->propagate();
		solver->force(c, 0) && solver->propagate();
		solver->assume(x) && solver->propagate();
		solver->setBacktrackLevel(solver->decisionLevel());
		
		ClauseCreator cc(solver);
		cc.start(Constraint_t::learnt_conflict).add(~a).add(~b).add(~c).add(d);
		ClauseHead* clause = cc.end().local;
		CPPUNIT_ASSERT(clause->locked(*solver));
		bool remove = clause->strengthen(*solver, ~a).second;
		solver->backtrack();
		CPPUNIT_ASSERT(solver->isTrue(d));
		CPPUNIT_ASSERT(!remove || solver->reason(d).type() != Antecedent::generic_constraint || solver->reason(d).constraint() != clause);
	}

	void testSimplifyTagged() {
		Var a = ctx.addVar( Var_t::atom_var );
		Var b = ctx.addVar( Var_t::atom_var );
		Var c = ctx.addVar( Var_t::atom_var );
		ctx.startAddConstraints();
		ctx.endInit();
		Literal tag = posLit(solver->pushTagVar(true));
		ClauseCreator cc(solver);
		// ~a ~b ~c ~tag
		cc.start(Constraint_t::learnt_conflict).add(negLit(a)).add(negLit(b)).add(negLit(c)).add(~tag);
		ClauseHead* clause = cc.end().local;
		
		solver->force(posLit(c));
		CPPUNIT_ASSERT_EQUAL(false, clause->strengthen(*solver, negLit(c)).second);
	}
	
	void testSimplifyRemovesFalseLitsEnd() {
		Clause* c;
		solver->add(c = createClause(3, 3));
		CPPUNIT_ASSERT(6 == c->size());
		
		solver->force(~clLits[4], 0);
		solver->force(~clLits[5], 0);
		solver->propagate();

		CPPUNIT_ASSERT_EQUAL(false, c->simplify(*solver));
		CPPUNIT_ASSERT(4 == c->size());

		CPPUNIT_ASSERT_EQUAL(2, countWatches(*solver, c, clLits));
	}

	void testClauseSatisfied() {
		ConstraintType t = Constraint_t::learnt_conflict;
		TypeSet ts; ts.addSet(t);
		Clause* c;
		solver->addLearnt(c = createClause(2, 2, t), 4);
		LitVec free;
		CPPUNIT_ASSERT_EQUAL(uint32(t), c->isOpen(*solver, ts, free));
		CPPUNIT_ASSERT_EQUAL(LitVec::size_type(4), free.size());

		solver->assume( clLits[2] );
		solver->propagate();
		free.clear();
		CPPUNIT_ASSERT_EQUAL(uint32(0), c->isOpen(*solver, ts, free));
		solver->undoUntil(0);
		solver->assume( ~clLits[1] );
		solver->assume( ~clLits[2] );
		solver->propagate();
		free.clear();
		CPPUNIT_ASSERT_EQUAL(uint32(t), c->isOpen(*solver, ts, free));
		CPPUNIT_ASSERT_EQUAL(LitVec::size_type(2), free.size());
		ts.m = 0; ts.addSet(Constraint_t::learnt_loop);
		CPPUNIT_ASSERT_EQUAL(uint32(0), c->isOpen(*solver, ts, free));
	}
	
	void testContraction() {
		ctx.endInit();
		LitVec lits(1, a1);
		for (uint32 i = 2; i <= 12; ++i) {
			solver->assume(negLit(i));
			lits.push_back(posLit(i));
		}
		solver->strategies().compress = 6;
		ClauseHead* cl = ClauseCreator::create(*solver, lits, 0, Constraint_t::learnt_conflict).local;
		uint32  s1 = cl->size();
		CPPUNIT_ASSERT(s1 < lits.size());
		LitVec r;
		solver->reason(a1, r);
		CPPUNIT_ASSERT( r.size() == lits.size()-1 );

		solver->undoUntil(0);
		CPPUNIT_ASSERT(cl->size() == lits.size());
	}

	void testNewContractedClause() {
		ctx.endInit();
		// head
		clLits.push_back(a1);
		clLits.push_back(a2);
		clLits.push_back(a3);
		for (uint32 i = 4; i <= 12; ++i) {
			solver->assume(negLit(i));
			// (false) tail
			clLits.push_back(posLit(i));
		}
		ClauseRep   x = ClauseRep::create(&clLits[0], (uint32)clLits.size(), ClauseInfo(Constraint_t::learnt_conflict));
		ClauseHead* c = Clause::newContractedClause(*solver, x, 3, false);
		solver->addLearnt(c, static_cast<uint32>(clLits.size()));
		CPPUNIT_ASSERT(c->size() < clLits.size());

		solver->assume(~a1) && solver->propagate();
		solver->assume(~a3) && solver->propagate();
		CPPUNIT_ASSERT(solver->isTrue(a2));
		LitVec r;
		solver->reason(a2, r);
		CPPUNIT_ASSERT(r.size() == clLits.size()-1);
	}
	void testBug() {
		Clause* c;
		solver->add(c = createClause(3, 3));
		solver->assume(~clLits[1]);
		solver->propagate();
		solver->assume(~clLits[2]);
		solver->propagate();
		solver->assume(~clLits[3]);
		solver->propagate();
		solver->assume(~clLits[0]);
		solver->propagate();
		uint32 exp = solver->numAssignedVars();
		solver->undoUntil(0);
		solver->assume(~clLits[1]);
		solver->propagate();
		solver->assume(~clLits[2]);
		solver->propagate();
		solver->assume(~clLits[3]);
		solver->propagate();
		solver->assume(~clLits[4]);
		solver->propagate();
		
		CPPUNIT_ASSERT(exp == solver->numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, solver->hasWatch(~clLits[0], c));
		CPPUNIT_ASSERT_EQUAL(true, solver->hasWatch(~clLits[5], c));
	}

	void testClone() {
		Solver& solver2 = ctx.addSolver();
		ctx.endInit(true);
		ClauseHead* c      = createClause(3, 3);
		ClauseHead* clone  = (ClauseHead*)c->cloneAttach(solver2);
		LitVec lits;
		clone->toLits(lits);
		CPPUNIT_ASSERT(lits == clLits);
		CPPUNIT_ASSERT(countWatches(solver2, clone, lits) == 2);
		clone->destroy(&solver2, true);

		solver->force(~clLits[0], 0);
		solver->force(~clLits[2], 0);
		solver->propagate();
		c->simplify(*solver);
		clone = (ClauseHead*)c->cloneAttach(solver2);
		lits.clear();
		clone->toLits(lits);
		CPPUNIT_ASSERT(lits.size() == 4);
		CPPUNIT_ASSERT(countWatches(solver2, clone, lits) == 2);
		clone->destroy(&solver2, true);
		c->destroy(solver, true);

	}

	void testLoopFormulaInitialWatches() {
		LoopFormula* lf = lfTestInit();
		CPPUNIT_ASSERT_EQUAL(true, solver->hasWatch(a1, lf));
		CPPUNIT_ASSERT_EQUAL(true, solver->hasWatch(a2, lf));
		CPPUNIT_ASSERT_EQUAL(true, solver->hasWatch(a3, lf));
		CPPUNIT_ASSERT_EQUAL(true, solver->hasWatch(~b3, lf));   
	}
	
	void testSimplifyLFIfOneBodyTrue() {
		LoopFormula* lf = lfTestInit();
		solver->undoUntil(0);
		solver->force( b2, 0 );
		solver->propagate();

		CPPUNIT_ASSERT_EQUAL(true, lf->simplify(*solver));
		CPPUNIT_ASSERT_EQUAL(false, solver->hasWatch(a1, lf));
		CPPUNIT_ASSERT_EQUAL(false, solver->hasWatch(~b3, lf));
	}

	void testSimplifyLFIfAllAtomsFalse() {
		LoopFormula* lf = lfTestInit();
		solver->undoUntil(0);
		solver->force( ~a1, 0 );
		solver->force( ~a2, 0 );
		solver->propagate();
		CPPUNIT_ASSERT_EQUAL(false, lf->simplify(*solver));
		solver->assume(a3);
		solver->propagate();
		solver->backtrack();
		solver->propagate();
		CPPUNIT_ASSERT_EQUAL(true, lf->simplify(*solver));
		CPPUNIT_ASSERT_EQUAL(false, solver->hasWatch(~b3, lf));
		CPPUNIT_ASSERT_EQUAL(false, solver->hasWatch(a1, lf));
		CPPUNIT_ASSERT_EQUAL(false, solver->hasWatch(a2, lf));
		CPPUNIT_ASSERT_EQUAL(false, solver->hasWatch(a3, lf));
		solver->reduceLearnts(1.0f);
	}

	void testSimplifyLFRemovesFalseBodies() {
		LoopFormula* lf = lfTestInit();
		solver->undoUntil(0);
		
		solver->force( ~b1, 0 );
		solver->propagate();
		CPPUNIT_ASSERT_EQUAL(true, lf->simplify(*solver));
		CPPUNIT_ASSERT(3u == solver->sharedContext()->numLearntShort());
	}

	void testSimplifyLFRemovesFalseAtoms() {
		LoopFormula* lf = lfTestInit();
		solver->undoUntil(0);
		solver->force( ~a1,0 );
		solver->propagate();
		CPPUNIT_ASSERT_EQUAL(false, lf->simplify(*solver));
		CPPUNIT_ASSERT(5 == lf->size());

		solver->force( ~a3,0 );
		solver->propagate();
		CPPUNIT_ASSERT_EQUAL(false, lf->simplify(*solver));
		CPPUNIT_ASSERT(4 == lf->size());

		solver->force( ~a2,0 );
		solver->propagate();
		CPPUNIT_ASSERT_EQUAL(true, lf->simplify(*solver));
	}

	void testSimplifyLFRemovesTrueAtoms() {
		LoopFormula* lf = lfTestInit();
		solver->undoUntil(0);
		solver->force( a1,0 );
		solver->propagate();
		CPPUNIT_ASSERT_EQUAL(true, lf->simplify(*solver));
		
		CPPUNIT_ASSERT(1u == solver->sharedContext()->numLearntShort());
	}

	void testLoopFormulaPropagateBody() {
		LoopFormula* lf = lfTestInit();
		solver->undoUntil(0);
		solver->assume( ~b1 );
		solver->propagate();
		solver->assume( ~b3 );
		solver->propagate();
		solver->assume( a3 );
		solver->propagate();

		CPPUNIT_ASSERT_EQUAL( true, solver->isTrue(b2) );
		CPPUNIT_ASSERT_EQUAL( Antecedent::generic_constraint, solver->reason(b2).type() );
		LitVec r;
		solver->reason(b2, r);
		CPPUNIT_ASSERT_EQUAL( LitVec::size_type(3), r.size() );
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), a3) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~b3) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~b1) != r.end());

		CPPUNIT_ASSERT_EQUAL(true, lf->locked(*solver));
	}

	void testLoopFormulaPropagateBody2() {
		LoopFormula* lf = lfTestInit();
		solver->undoUntil(0);
		solver->assume( a1 );
		solver->propagate();
		solver->undoUntil(0);
		
		solver->assume( ~b1 );
		solver->propagate();
		solver->assume( a2 );
		solver->propagate();
		solver->assume( ~b2 );
		solver->propagate();

		CPPUNIT_ASSERT_EQUAL( true, solver->isTrue(b3) );
		
		CPPUNIT_ASSERT_EQUAL( Antecedent::generic_constraint, solver->reason(b3).type() );
		LitVec r;
		solver->reason(b3, r);
		CPPUNIT_ASSERT_EQUAL( LitVec::size_type(3), r.size() );
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~b1) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~b2) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), a2) != r.end());

		CPPUNIT_ASSERT_EQUAL(true, lf->locked(*solver));
	}

	void testLoopFormulaPropagateAtoms() {
		LoopFormula* lf = lfTestInit();
		solver->undoUntil(0);
		solver->assume( ~b3 );
		solver->propagate();
		solver->assume( ~b1 );
		solver->propagate();
		
		solver->assume( ~a1 );
		solver->propagate();
		
		solver->assume( ~b2 );
		solver->propagate();

		CPPUNIT_ASSERT_EQUAL( true, solver->isTrue(~a1) );
		CPPUNIT_ASSERT_EQUAL( true, solver->isTrue(~a2) );
		CPPUNIT_ASSERT_EQUAL( true, solver->isTrue(~a3) );
		
		CPPUNIT_ASSERT_EQUAL( Antecedent::generic_constraint, solver->reason(~a2).type() );
		LitVec r;
		solver->reason(~a2, r);
		CPPUNIT_ASSERT_EQUAL( LitVec::size_type(3), r.size() );
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~b1) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~b2) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~b3) != r.end());

		CPPUNIT_ASSERT_EQUAL(true, lf->locked(*solver));
	}

	void testLoopFormulaPropagateAtoms2() {
		LoopFormula* lf = lfTestInit();
		solver->undoUntil(0);
		solver->assume( a1 );
		solver->force( a2, 0 );
		solver->propagate();
		solver->undoUntil(0);
		
		solver->assume( ~b3 );
		solver->propagate();
		solver->assume( ~b1 );
		solver->propagate();
		solver->assume( ~b2 );
		solver->propagate();

		CPPUNIT_ASSERT_EQUAL( true, solver->isTrue(~a1) );
		CPPUNIT_ASSERT_EQUAL( true, solver->isTrue(~a2) );
		CPPUNIT_ASSERT_EQUAL( true, solver->isTrue(~a3) );
		
		
		CPPUNIT_ASSERT_EQUAL( Antecedent::generic_constraint, solver->reason(~a1).type() );
		LitVec r;
		solver->reason(~a1, r);
		CPPUNIT_ASSERT_EQUAL( LitVec::size_type(3), r.size() );
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~b1) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~b2) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~b3) != r.end());

		CPPUNIT_ASSERT_EQUAL(true, lf->locked(*solver));
	}

	void testLoopFormulaBodyConflict() {
		lfTestInit();
		solver->undoUntil(0);
		
		solver->assume( ~b3 );
		solver->propagate();
		solver->assume( ~b2 );
		solver->propagate();
		solver->force(a3, 0);
		solver->force(~b1, 0);
		
		CPPUNIT_ASSERT_EQUAL( false, solver->propagate() );
		const LitVec& r = solver->conflict();
		
		CPPUNIT_ASSERT_EQUAL( LitVec::size_type(4), r.size() );
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), a3) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~b3) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~b1) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~b2) != r.end());
	}
	void testLoopFormulaAtomConflict() {
		lfTestInit();
		solver->undoUntil(0);
		solver->assume( ~b3 );
		solver->propagate();
		solver->assume(~b1);
		solver->propagate();
		solver->force(~b2, 0);
		solver->force(a2, 0);
		CPPUNIT_ASSERT_EQUAL( false, solver->propagate() );
		
		
		LitVec r = solver->conflict();
		
		CPPUNIT_ASSERT_EQUAL( LitVec::size_type(4), r.size() );
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), a2) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~b3) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~b1) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~b2) != r.end());

		CPPUNIT_ASSERT_EQUAL( true, solver->isTrue(~a1));
		solver->reason(~a1, r);
		CPPUNIT_ASSERT_EQUAL( LitVec::size_type(3), r.size() );
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~b3) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~b1) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~b2) != r.end());
	}

	void testLoopFormulaDontChangeSat() {
		lfTestInit();
		solver->undoUntil(0);
		CPPUNIT_ASSERT_EQUAL(true, solver->assume( ~b1 ) && solver->propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver->assume( ~b3 ) && solver->propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver->assume( a2 ) && solver->propagate());

		CPPUNIT_ASSERT_EQUAL(true, solver->isTrue( b2 ));
		LitVec rold;
		solver->reason(b2, rold);
		
		CPPUNIT_ASSERT_EQUAL(true, solver->assume( a1 ) && solver->propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver->isTrue( b2 ));
		LitVec rnew;
		solver->reason(b2, rnew);
		CPPUNIT_ASSERT(rold == rnew);
	}

	void testLoopFormulaSatisfied() {
		LoopFormula* lf = lfTestInit();
		ConstraintType t= Constraint_t::learnt_loop;
		TypeSet ts, other; ts.addSet(t); other.addSet(Constraint_t::learnt_conflict);
		LitVec free;
		CPPUNIT_ASSERT_EQUAL(uint32(0), lf->isOpen(*solver, ts, free));
		solver->undoUntil(0);
		free.clear();
		CPPUNIT_ASSERT_EQUAL(uint32(lf->type()), lf->isOpen(*solver, ts, free));
		CPPUNIT_ASSERT_EQUAL(LitVec::size_type(6), free.size());
		CPPUNIT_ASSERT_EQUAL(uint32(0), lf->isOpen(*solver, other, free));
		solver->assume( a1 );
		solver->assume( ~b2 );
		solver->propagate();
		free.clear();
		CPPUNIT_ASSERT_EQUAL(uint32(lf->type()), lf->isOpen(*solver, ts, free));
		CPPUNIT_ASSERT_EQUAL(LitVec::size_type(4), free.size());
		solver->assume( ~b1 );
		solver->propagate();
		CPPUNIT_ASSERT_EQUAL(uint32(0), lf->isOpen(*solver, ts, free));
	}

	void testLoopFormulaBugEq() {
		ctx.endInit();
		Literal body1 = b1; 
		Literal body2 = b2;
		Literal body3 = ~b3; // assume body3 is equivalent to some literal ~xy
		solver->assume(~body1);
		solver->assume(~body2);
		solver->assume(~body3);
		solver->propagate();
		Literal lits[4] = { ~a1, body3, body2, body1 };
		
		LoopFormula* lf = LoopFormula::newLoopFormula(*solver, ClauseRep::prepared(lits, 4), lits, 1);
		solver->addLearnt(lf, lf->size());
		solver->force(~a1, lf);
		solver->propagate();
		solver->undoUntil(solver->decisionLevel()-2);
		CPPUNIT_ASSERT_EQUAL(true, solver->assume(~body3) && solver->propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver->assume(a1) && solver->propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver->isTrue(body2));
	}

	void testLoopFormulaPropTrueAtomInSatClause() {
		lfTestInit();
		solver->undoUntil(0);
		solver->assume( ~a1 );
		solver->propagate();
		
		solver->assume( a2 );
		solver->force( ~b3, 0 );
		solver->force( ~b2, 0 );
		solver->propagate();   
		
		CPPUNIT_ASSERT_EQUAL( true, solver->isTrue(b1) );
	}
private:
	SharedContext ctx;
	Solver*       solver;
	int countWatches(const Solver& s, ClauseHead* c, const LitVec& lits) {
		int w     = 0;
		for (LitVec::size_type i = 0; i != lits.size(); ++i) {
			w += s.hasWatch(~lits[i], c);
		}
		return w;
	}
	void check(Clause& c) {
		std::string s = toString(clLits);
		std::random_shuffle(clLits.begin(), clLits.end());
		CPPUNIT_ASSERT( value_free == solver->value(clLits.back().var()) );
		for (LitVec::size_type i = 0; i != clLits.size() - 1; ++i) {
			CPPUNIT_ASSERT( value_free == solver->value(clLits[i].var()) );
			solver->force(~clLits[i], 0);
			solver->propagate();
		}
		CPPUNIT_ASSERT_EQUAL_MESSAGE(s.c_str(), true, solver->isTrue(clLits.back()));

		Antecedent reason = solver->reason(clLits.back());
		CPPUNIT_ASSERT(reason == &c);
		LitVec r;
		c.reason(*solver, clLits.back(), r);
		for (LitVec::size_type i = 0; i != clLits.size() - 1; ++i) {
			LitVec::iterator it = std::find(r.begin(), r.end(), ~clLits[i]);
			CPPUNIT_ASSERT_MESSAGE(s.c_str(), it != r.end());
			r.erase(it);
		}
		while (!r.empty() && isSentinel(r.back())) r.pop_back();
		CPPUNIT_ASSERT(r.empty());
	}
	std::string toString(const LitVec& c) {
		std::string res="[";
		for (uint32 i = 0; i != c.size(); ++i) {
			if (c[i].sign()) {
				res += '~';
			}
			res += ('a' + i);
			res += ' ';
		}
		res+="]";
		return res;
	}
	Clause* createClause(LitVec& lits, const ClauseInfo& info) {
		uint32 flags = ClauseCreator::clause_explicit | ClauseCreator::clause_no_add | ClauseCreator::clause_no_prepare;
		return (Clause*)ClauseCreator::create(*solver, lits, flags, info).local;
	}
	Clause* createClause(int pos, int neg, ConstraintType t = Constraint_t::static_constraint) {
		clLits.clear();
		int size = pos + neg;
		LitVec lit(size);
		for (int i = 0; i < pos; ++i) {
			lit[i] = posLit(i+1);
			clLits.push_back(lit[i]);
		}
		for (int i = pos; i < pos + neg; ++i) {
			lit[i] = negLit(i+1);
			clLits.push_back(lit[i]);
		}
		return createClause(clLits, ClauseInfo(t));
	}

	Clause* createRandomClause(int size) {
		int pos = rand() % size + 1;
		return createClause( pos, size - pos );
	}
	
	LoopFormula* lfTestInit() {
		ctx.endInit();
		solver->assume(~b1);
		solver->assume(~b2);
		solver->assume(~b3);
		solver->propagate();
		Literal lits[] = { ~a1, b3, b2, b1, ~a1, ~a2, ~a3 };
		LoopFormula* lf = LoopFormula::newLoopFormula(*solver, ClauseRep::prepared(lits, 4), lits+4, 3);
		solver->addLearnt(lf, lf->size());
		solver->force(~a1, lf);
		solver->force(~a2, lf);
		solver->force(~a3, lf);
		solver->propagate();
		return lf;
	}
	Literal a1, a2, a3, b1, b2, b3;
	LitVec clLits;
};
CPPUNIT_TEST_SUITE_REGISTRATION(ClauseTest);
} } 
