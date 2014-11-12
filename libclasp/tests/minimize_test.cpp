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
#include <clasp/minimize_constraint.h>
#include <clasp/solver.h>
#include <clasp/solve_algorithms.h>
namespace Clasp { namespace Test {
class DefaultMinimizeTest : public CppUnit::TestFixture {
	CPPUNIT_TEST_SUITE(DefaultMinimizeTest);
	CPPUNIT_TEST(testEmpty);
	CPPUNIT_TEST(testOneLevelLits);
	CPPUNIT_TEST(testMultiLevelLits);
	CPPUNIT_TEST(testMultiLevelWeightsAreReused);
	CPPUNIT_TEST(testMergeComplementaryLits);
	CPPUNIT_TEST(testMergeComplementaryLits2);
	CPPUNIT_TEST(testNegativeLowerInit);
	CPPUNIT_TEST(testNegativeLower);

	CPPUNIT_TEST(testOrder);
	CPPUNIT_TEST(testSkipLevel);
	CPPUNIT_TEST(testReassertAfterBacktrack);
	CPPUNIT_TEST(testConflict);
	CPPUNIT_TEST(testOptimize);
	CPPUNIT_TEST(testEnumerate);
	CPPUNIT_TEST(testComputeImplicationLevel);
	CPPUNIT_TEST(testSetModelMayBacktrackMultiLevels);
	CPPUNIT_TEST(testPriorityBug);
	CPPUNIT_TEST(testStrengthenImplication);
	CPPUNIT_TEST(testRootLevelMadness);
	CPPUNIT_TEST(testIntegrateOptimum);
	CPPUNIT_TEST(testIntegrateOptimumConflict);
	CPPUNIT_TEST(testIntegrateBug);

	CPPUNIT_TEST(testReasonBug);
	CPPUNIT_TEST(testSmartBacktrack);
	CPPUNIT_TEST(testBacktrackToTrue);
	CPPUNIT_TEST(testMultiAssignment);
	CPPUNIT_TEST(testBugBacktrackFromFalse);
	CPPUNIT_TEST(testBugBacktrackToTrue);
	CPPUNIT_TEST(testBugInitOptHierarch);
	CPPUNIT_TEST(testBugAdjustSum);
	CPPUNIT_TEST(testWeightNullBug);
	CPPUNIT_TEST(testAdjust);
	CPPUNIT_TEST(testAdjustFact);
	CPPUNIT_TEST(testAssumption);

	CPPUNIT_TEST(testHierarchicalSetModel);
	CPPUNIT_TEST(testHierarchical);
	CPPUNIT_TEST(testInconsistent);
	CPPUNIT_TEST_SUITE_END(); 
public:
	DefaultMinimizeTest() {
		a = posLit(ctx.addVar(Var_t::atom_var));
		b = posLit(ctx.addVar(Var_t::atom_var));
		c = posLit(ctx.addVar(Var_t::atom_var));
		d = posLit(ctx.addVar(Var_t::atom_var));
		e = posLit(ctx.addVar(Var_t::atom_var));
		f = posLit(ctx.addVar(Var_t::atom_var));
		x = posLit(ctx.addVar(Var_t::atom_var));
		y = posLit(ctx.addVar(Var_t::atom_var));
		ctx.startAddConstraints();
	}
	void setUp()    { newMin = 0; data = 0; }
	void tearDown() { 
		if (newMin) { newMin->destroy(ctx.master(), true);  } 
		if (data)   { data->release(); }
	}
	void testEmpty() {
		MinimizeBuilder b;
		newMin = buildAndAttach(b);
		CPPUNIT_ASSERT(countMinLits() == 0);
	}
	
	void testOneLevelLits() {
		WeightLitVec min;
		ctx.addUnary(c);
		ctx.addUnary(~e);
		min.push_back( WeightLiteral(a, 1) );
		min.push_back( WeightLiteral(b, 2) );
		min.push_back( WeightLiteral(c, 1) ); // true lit
		min.push_back( WeightLiteral(a, 2) ); // duplicate lit
		min.push_back( WeightLiteral(d, 1) );
		min.push_back( WeightLiteral(e, 2) ); // false lit
		newMin = buildAndAttach(MinimizeBuilder().addRule(min));
		CPPUNIT_ASSERT(newMin->numRules() == 1);
		CPPUNIT_ASSERT(countMinLits() == 3);
		CPPUNIT_ASSERT(newMin->shared()->adjust(0) == 1);
		const SharedMinimizeData* data = newMin->shared();
		CPPUNIT_ASSERT(data->lits[0].first == a && data->lits[0].second == 3);
		for (const WeightLiteral* it = data->lits; !isSentinel(it->first); ++it) {
			CPPUNIT_ASSERT_MESSAGE("Minimize lits not sorted!", it->second >= (it+1)->second);
			CPPUNIT_ASSERT(ctx.master()->hasWatch(it->first, newMin));
			CPPUNIT_ASSERT(ctx.varInfo(it->first.var()).frozen());
		}
		newMin->destroy(ctx.master(), true);
		newMin = 0;
		CPPUNIT_ASSERT(!ctx.master()->hasWatch(a, newMin));
	}
	
	void testMultiLevelLits() {
		MinimizeBuilder builder;
		WeightLitVec min;
		ctx.addUnary(c);
		ctx.addUnary(~e);
		min.push_back( WeightLiteral(a, 1) );
		min.push_back( WeightLiteral(b, 1) );
		min.push_back( WeightLiteral(c, 1) ); // true lit
		min.push_back( WeightLiteral(b, 2) ); // duplicate lit
		min.push_back( WeightLiteral(d, 1) );
		min.push_back( WeightLiteral(b, 1) ); // duplicate lit
		
		builder.addRule(min);
		min.clear();
		min.push_back( WeightLiteral(e, 2) ); // false lit
		min.push_back( WeightLiteral(f, 1) );
		min.push_back( WeightLiteral(x, 2) );
		min.push_back( WeightLiteral(y, 3) );
		min.push_back( WeightLiteral(b, 1) ); // duplicate lit
		builder.addRule(min);
		min.clear();
		min.push_back( WeightLiteral(b, 2) ); // duplicate lit
		min.push_back( WeightLiteral(a, 1) ); // duplicate lit
		min.push_back( WeightLiteral(a, 2) ); // duplicate lit
		min.push_back( WeightLiteral(c, 2) ); // true lit
		min.push_back( WeightLiteral(d, 1) ); // duplicate lit
		builder.addRule(min);
		
		newMin = buildAndAttach(builder);
		CPPUNIT_ASSERT(newMin->numRules() == 3);
		CPPUNIT_ASSERT(countMinLits() == 6);
		const SharedMinimizeData* data = newMin->shared();
		CPPUNIT_ASSERT(data->adjust(0) == 1 && data->adjust(1) == 0 && data->adjust(2) == 2);
		CPPUNIT_ASSERT(data->lits[0].first == b);
		CPPUNIT_ASSERT(data->weights.size() == 11);
		for (const WeightLiteral* it = data->lits; !isSentinel(it->first); ++it) {
			CPPUNIT_ASSERT(ctx.master()->hasWatch(it->first, newMin));
		}
	}

	void testMultiLevelWeightsAreReused() {
		MinimizeBuilder builder;
		WeightLitVec min;
		min.push_back( WeightLiteral(a, 1) );
		min.push_back( WeightLiteral(b, 1) );
		min.push_back( WeightLiteral(b, 2) );
		min.push_back( WeightLiteral(c, 1) );
		min.push_back( WeightLiteral(d, 3) );
		builder.addRule(min);
		
		min.clear();
		min.push_back( WeightLiteral(b, 1) );
		min.push_back( WeightLiteral(d, 1) );
		builder.addRule(min);
		
		newMin = buildAndAttach(builder);
		// b = 0
		// d = 0
		// a = 2
		// c = 2
		// weights: [(0,3)(1,1)][(0,1)] + [(1,0)] for sentinel
		CPPUNIT_ASSERT(newMin->shared()->weights.size() == 4);
	}

	void testMergeComplementaryLits() {
		MinimizeBuilder builder;
		WeightLitVec min;
		min.push_back( WeightLiteral(a, 1) );
		min.push_back( WeightLiteral(b, 1) );
		min.push_back( WeightLiteral(c, 2) );
		min.push_back( WeightLiteral(d, 1) );
		min.push_back( WeightLiteral(~d, 2) );
		builder.addRule(min);
		min.clear();
		min.push_back( WeightLiteral(~c, 1) );
		min.push_back( WeightLiteral(e, 1) );
		builder.addRule(min);
		newMin = buildAndAttach(builder);
		CPPUNIT_ASSERT(countMinLits() == 5);
		CPPUNIT_ASSERT(newMin->shared()->adjust(0) == 1 && newMin->shared()->adjust(1) == 1);

		ctx.master()->assume(c) && ctx.master()->propagate();
		CPPUNIT_ASSERT(newMin->sum(1, true) == 0);

	}

	void testMergeComplementaryLits2() {
		MinimizeBuilder builder;
		WeightLitVec min;
		min.push_back( WeightLiteral(a, 1) );
		min.push_back( WeightLiteral(~a, 1) );
		builder.addRule(min);
		min.clear();
		min.push_back( WeightLiteral(a, 1) );
		builder.addRule(min);
		newMin = buildAndAttach(builder);
		CPPUNIT_ASSERT(countMinLits() == 1);
		CPPUNIT_ASSERT(newMin->shared()->adjust(0) == 1 && newMin->shared()->adjust(1) == 0);
	}
	void testNegativeLowerInit() {
		WeightLitVec aMin, bMin, cMin;
		aMin.push_back( WeightLiteral(a, 1) );
		aMin.push_back( WeightLiteral(b, 1) );
		bMin.push_back( WeightLiteral(~a, 1) );
		bMin.push_back( WeightLiteral(~b, 1) );
		cMin.push_back( WeightLiteral(a, 1) );
		cMin.push_back( WeightLiteral(b, 1) );
		data = MinimizeBuilder()
			.addRule(aMin)
			.addRule(bMin)
			.addRule(cMin)
			.build(ctx);
		CPPUNIT_ASSERT(data->lower(0) == 0);
		CPPUNIT_ASSERT(data->lower(1) == -2);
		CPPUNIT_ASSERT(data->lower(2) == 0);
	}
	void testNegativeLower() {
		ctx.addBinary(a, b);
		WeightLitVec aMin, bMin, cMin;
		aMin.push_back( WeightLiteral(a, 1) );
		aMin.push_back( WeightLiteral(b, 1) );
		bMin.push_back( WeightLiteral(~a, 1) );
		cMin.push_back( WeightLiteral(a, 1) );
		data = MinimizeBuilder()
			.addRule(aMin)
			.addRule(bMin)
			.addRule(cMin)
			.build(ctx);
		newMin = createMin(ctx, *ctx.master(), data, MinimizeMode_t::bb_step_hier);
		newMin->integrateBound(*ctx.master());
		
		Solver& s = *ctx.master();
		s.assume(b) && s.propagate();
		s.assume(~a) && s.propagate();
		newMin->handleModel(s);
		s.undoUntil(0);
		CPPUNIT_ASSERT(!newMin->integrate(s) || !s.propagate());
		LitVec ignore;
		CPPUNIT_ASSERT(newMin->handleUnsat(s, true, ignore));
		CPPUNIT_ASSERT(newMin->integrate(s) && s.propagate());
		
		CPPUNIT_ASSERT(s.isFalse(b));
		CPPUNIT_ASSERT(s.assume(a) && s.propagate());
		newMin->handleModel(s);
	}
	
	void testOrder() {
		WeightLitVec aMin, bMin;
		aMin.push_back( WeightLiteral(a, 1) );
		bMin.push_back( WeightLiteral(b, 1) );
		newMin = buildAndAttach(MinimizeBuilder()
			.addRule(aMin)
			.addRule(bMin));
		
		Solver& solver = *ctx.master();
		solver.assume(b);
		CPPUNIT_ASSERT_EQUAL(true, solver.propagate());
		solver.assume(~a);
		CPPUNIT_ASSERT_EQUAL(true, solver.propagate());
		CPPUNIT_ASSERT(newMin->sum(0, true) == 0 && newMin->sum(1, true) == 1);
		newMin->commitUpperBound(solver);
		CPPUNIT_ASSERT(newMin->integrateBound(solver));
		CPPUNIT_ASSERT(solver.isFalse(a));
		CPPUNIT_ASSERT(solver.isFalse(b));
		CPPUNIT_ASSERT(solver.decisionLevel() == 0);
	}

	void testSkipLevel() {
		WeightLitVec aMin, bMin;
		aMin.push_back( WeightLiteral(c, 2) );
		aMin.push_back( WeightLiteral(d, 1) );
		aMin.push_back( WeightLiteral(e, 2) );
		
		bMin.push_back( WeightLiteral(a, 1) );
		bMin.push_back( WeightLiteral(b, 1) );

		newMin = buildAndAttach(MinimizeBuilder()
			.addRule(aMin)
			.addRule(bMin));
		Solver& solver = *ctx.master();
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(a) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(b) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(~d) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(c) && solver.propagate());
		solver.force(~e, 0); solver.propagate();
		newMin->commitUpperBound(solver);
		solver.backtrack();
		solver.force(e, 0);
		CPPUNIT_ASSERT_EQUAL(true, newMin->integrateBound(solver));
		CPPUNIT_ASSERT(solver.decisionLevel() == 2 && solver.backtrackLevel() == 2);
		CPPUNIT_ASSERT(solver.isFalse(c) && solver.isFalse(e));
		solver.backtrack();
	} 

	void testReassertAfterBacktrack() {
		WeightLitVec aMin;
		aMin.push_back( WeightLiteral(x, 1) );
		aMin.push_back( WeightLiteral(y, 1) );
		newMin = buildAndAttach(MinimizeBuilder().addRule(aMin));
		// disable backjumping
		ctx.setProject(a.var(), true);
		Solver& solver = *ctx.master();
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(a) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(~x) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(y) && solver.propagate());
		newMin->commitUpperBound(solver);
		solver.undoUntil(1);
		solver.setBacktrackLevel(1);
		CPPUNIT_ASSERT_EQUAL(true, newMin->integrateBound(solver));
		CPPUNIT_ASSERT(solver.decisionLevel() == 1 && solver.isTrue(~x));
		solver.backtrack();
		CPPUNIT_ASSERT(solver.decisionLevel() == 0 && solver.isTrue(~x));
	}

	void testConflict() {
		WeightLitVec aMin, bMin;
		aMin.push_back( WeightLiteral(c, 2) );
		aMin.push_back( WeightLiteral(d, 1) );
		aMin.push_back( WeightLiteral(e, 2) );
		
		bMin.push_back( WeightLiteral(a, 1) );
		bMin.push_back( WeightLiteral(b, 1) );

		newMin = buildAndAttach(MinimizeBuilder()
			.addRule(aMin)
			.addRule(bMin));
		Solver& solver = *ctx.master();
				
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(a) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(b) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(~d) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(c) && solver.propagate());
		solver.force(~e, 0); solver.propagate();
		newMin->commitUpperBound(solver);
		solver.undoUntil(0);
		CPPUNIT_ASSERT_EQUAL(true, newMin->integrateBound(solver));
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(a) && solver.propagate());
		solver.force(c, 0);
		solver.force(d, 0);
		CPPUNIT_ASSERT_EQUAL(false, solver.propagate());
		const LitVec& cfl = solver.conflict();
		CPPUNIT_ASSERT(cfl.size() == 3);
		CPPUNIT_ASSERT(std::find(cfl.begin(), cfl.end(), a) != cfl.end());
		CPPUNIT_ASSERT(std::find(cfl.begin(), cfl.end(), c) != cfl.end());
		CPPUNIT_ASSERT(std::find(cfl.begin(), cfl.end(), d) != cfl.end());
	} 

	void testOptimize() {
		WeightLitVec aMin, bMin;
		aMin.push_back( WeightLiteral(a, 1) );
		aMin.push_back( WeightLiteral(b, 1) );
		bMin.push_back( WeightLiteral(c, 1) );
		bMin.push_back( WeightLiteral(d, 1) );
		newMin = buildAndAttach(MinimizeBuilder()
			.addRule(aMin)
			.addRule(bMin));
		Solver& solver = *ctx.master();
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(a) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(c) && solver.propagate());
		CPPUNIT_ASSERT(newMin->shared()->optimum(0) == SharedMinimizeData::maxBound());
		newMin->commitUpperBound(solver);
		CPPUNIT_ASSERT(newMin->shared()->optimum(0) != SharedMinimizeData::maxBound());
		solver.undoUntil(0);
		CPPUNIT_ASSERT_EQUAL(true, newMin->integrateBound(solver));
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(d) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.isTrue(~a));
		CPPUNIT_ASSERT_EQUAL(true, solver.isTrue(~b));
		CPPUNIT_ASSERT_EQUAL(value_free, solver.value(c.var()));
	}

	void testEnumerate() {
		WeightLitVec aMin, bMin;
		aMin.push_back( WeightLiteral(a, 1) );
		aMin.push_back( WeightLiteral(b, 1) );
		bMin.push_back( WeightLiteral(c, 1) );
		bMin.push_back( WeightLiteral(d, 1) );
		wsum_t bound[2] = {1,1};
		newMin = buildAndAttach(MinimizeBuilder()
			.addRule(aMin)
			.addRule(bMin)
			, MinimizeMode_t::enumerate, bound, 2);
		
		CPPUNIT_ASSERT(newMin->shared()->optimum(0) == SharedMinimizeData::maxBound());
		CPPUNIT_ASSERT(newMin->shared()->sum(0) == SharedMinimizeData::maxBound());
		CPPUNIT_ASSERT(newMin->shared()->upper(0) == 1);
		Solver& solver = *ctx.master();
		CPPUNIT_ASSERT_EQUAL(true, solver.propagate());
		
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(~a) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(c) && solver.propagate());

		newMin->commitUpperBound(solver);
		solver.undoUntil(0);
		newMin->relaxBound();
		newMin->integrateBound(solver);
		CPPUNIT_ASSERT(solver.queueSize() == 0);

		CPPUNIT_ASSERT_EQUAL(true, solver.assume(d) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(b) && solver.propagate());
		CPPUNIT_ASSERT(solver.isTrue(~c));
		CPPUNIT_ASSERT(solver.isTrue(~a));
	}

	void testComputeImplicationLevel() {
		WeightLitVec aMin;
		aMin.push_back( WeightLiteral(a, 1) );
		aMin.push_back( WeightLiteral(b, 1) );
		aMin.push_back( WeightLiteral(c, 1) );
		aMin.push_back( WeightLiteral(d, 2) );
		newMin = buildAndAttach(MinimizeBuilder()
			.addRule(aMin));
		Solver& solver = *ctx.master();
		solver.assume(a) && solver.propagate();
		solver.force(b,0)&& solver.propagate();
		solver.assume(c) && solver.propagate();
		solver.force(~d,0) && solver.propagate();
		newMin->commitUpperBound(solver);
		solver.undoUntil(1u);
		CPPUNIT_ASSERT(newMin->integrateBound(solver));
		CPPUNIT_ASSERT(solver.isFalse(d));
		LitVec r1, r2;
		solver.reason(~d, r1);
		solver.undoUntil(0);
		solver.assume(a) && solver.propagate();
		solver.reason(~d, r2);
		CPPUNIT_ASSERT(r2.size() <= r1.size() && r2.size() == 1);
		CPPUNIT_ASSERT(r1[0] == r2[0]);
		CPPUNIT_ASSERT(r1.size() == 1 || b == r1[1]);
		CPPUNIT_ASSERT_MESSAGE("TODO: REASON CORRECT BUT NOT MINIMAL!", r1.size() == r2.size());
	}

	void testSetModelMayBacktrackMultiLevels() {
		WeightLitVec aMin;
		aMin.push_back( WeightLiteral(a, 1) );
		newMin = buildAndAttach(MinimizeBuilder().addRule(aMin));
		Solver& solver = *ctx.master();
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(a) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(b) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(c) && solver.propagate());
		newMin->commitUpperBound(solver);
		newMin->integrateBound(solver);
		CPPUNIT_ASSERT(solver.decisionLevel() == 0);
	}

	void testPriorityBug() {
		WeightLitVec aMin, bMin;
		aMin.push_back( WeightLiteral(a, 1) );
		aMin.push_back( WeightLiteral(b, 1) );
		aMin.push_back( WeightLiteral(c, 1) );
		bMin.push_back( WeightLiteral(d, 1) );
		bMin.push_back( WeightLiteral(e, 1) );
		bMin.push_back( WeightLiteral(f, 1) );
		newMin = buildAndAttach(MinimizeBuilder()
			.addRule(aMin)
			.addRule(bMin));
		// disbale backjumping
		ctx.setProject(a.var(), true);
		ctx.setProject(e.var(), true);
		Solver& solver = *ctx.master();
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(a) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(e) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(f) && solver.propagate());
		newMin->commitUpperBound(solver);
		solver.backtrack();
		CPPUNIT_ASSERT_EQUAL(true, newMin->integrateBound(solver));
		CPPUNIT_ASSERT(solver.decisionLevel() == 2);
		solver.backtrack();
		CPPUNIT_ASSERT_EQUAL(true, solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(d) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.isTrue(~b));
		LitVec r;
		solver.reason(~b, r);
		CPPUNIT_ASSERT(LitVec::size_type(1) == r.size());
		CPPUNIT_ASSERT(a == r[0]);
	}

	void testStrengthenImplication() {
		WeightLitVec aMin;
		aMin.push_back( WeightLiteral(a, 1) );
		aMin.push_back( WeightLiteral(b, 2) );
		aMin.push_back( WeightLiteral(c, 1) );
		wsum_t bound   = 2;
		newMin         = buildAndAttach(MinimizeBuilder().addRule(aMin), MinimizeMode_t::optimize, &bound, 1);
		Solver& solver = *ctx.master();
		solver.assume(a) && solver.propagate();
		solver.setBacktrackLevel(1);
		ctx.setProject(a.var(), true);
		CPPUNIT_ASSERT(solver.isTrue(~b));
		LitVec r;
		solver.reason(~b, r);
		CPPUNIT_ASSERT(r.size() == 1 && r[0] == a);
		solver.assume(x) && solver.propagate();
		solver.assume(y) && solver.propagate();
		solver.assume(c) && solver.propagate();
		solver.assume(e) && solver.propagate();
		newMin->commitUpperBound(solver);
		solver.undoUntil(3);
		CPPUNIT_ASSERT(newMin->integrateBound(solver));
		CPPUNIT_ASSERT(solver.decisionLevel() == 1 && solver.isTrue(~b));
		r.clear();
		solver.reason(~b, r);
		CPPUNIT_ASSERT(r.empty() || (r.size() == 1 && r[0] == posLit(0)));
	}

	void testRootLevelMadness() {
		WeightLitVec aMin, bMin;
		aMin.push_back( WeightLiteral(a, 1) );
		aMin.push_back( WeightLiteral(b, 2) );
		aMin.push_back( WeightLiteral(c, 1) );
		bMin.push_back( WeightLiteral(d, 1) );
		bMin.push_back( WeightLiteral(e, 2) );
		bMin.push_back( WeightLiteral(f, 1) );
		newMin = buildAndAttach(MinimizeBuilder()
			.addRule(aMin)
			.addRule(bMin));
		Solver& solver = *ctx.master();
		solver.assume(a) && solver.propagate();
		solver.assume(c) && solver.propagate();
		solver.pushRootLevel(2);
		SumVec opt(newMin->numRules());
		opt[0] = 2;
		opt[1] = 3;
		setOptimum(solver, opt, false);
		LitVec r;
		CPPUNIT_ASSERT(solver.isFalse(b));
		solver.reason(~b, r);
		CPPUNIT_ASSERT(r.size() == 1 && r[0] == a);
		solver.clearAssumptions();
		solver.assume(d) && solver.propagate();
		solver.assume(e) && solver.propagate();
		solver.assume(f) && solver.propagate();
		solver.pushRootLevel(3);
		opt[0] = 2;
		opt[1] = 2;
		setOptimum(solver, opt, false);
		CPPUNIT_ASSERT(solver.isFalse(b));
		r.clear();
		solver.reason(~b, r);
		CPPUNIT_ASSERT(r.size() == 2 && r[0] == d && r[1] == e);
	}

	void testIntegrateOptimum() {
		WeightLitVec aMin;
		aMin.push_back( WeightLiteral(a, 1) );
		aMin.push_back( WeightLiteral(b, 1) );
		aMin.push_back( WeightLiteral(c, 1) );
		aMin.push_back( WeightLiteral(d, 1) );
		Solver& solver = *ctx.master();
		data   = MinimizeBuilder().addRule(aMin).build(ctx);
		newMin = createMin(ctx, solver, data);
		newMin->integrateBound(solver);
		solver.assume(a) && solver.propagate();
		solver.assume(e) && solver.propagate();
		solver.assume(b) && solver.propagate();
		solver.assume(f) && solver.propagate();
		solver.assume(c) && solver.propagate();
		
		SumVec opt(data->numRules());
		opt[0] = 2;
		CPPUNIT_ASSERT(setOptimum(solver, opt, true));
		CPPUNIT_ASSERT(solver.decisionLevel() == 1 && solver.queueSize() == 3);
		newMin->destroy(&solver, true);
		newMin = 0;
	}

	void testIntegrateOptimumConflict() {
		WeightLitVec aMin;
		aMin.push_back( WeightLiteral(a, 1) );
		aMin.push_back( WeightLiteral(b, 1) );
		aMin.push_back( WeightLiteral(c, 1) );
		aMin.push_back( WeightLiteral(d, 1) );
		Solver& solver = *ctx.master();
		data = MinimizeBuilder().addRule(aMin).build(ctx);
		SumVec opt(data->numRules());
		newMin = createMin(ctx, solver, data);
		newMin->integrateBound(solver);
		solver.assume(a) && solver.propagate();
		solver.assume(e) && solver.propagate();
		solver.assume(b) && solver.propagate();
		solver.assume(f) && solver.propagate();
		solver.assume(c) && solver.propagate();
		ctx.setProject(a.var(), true);
		ctx.setProject(b.var(), true);
		solver.setBacktrackLevel(3);
		opt[0] = 2;
		CPPUNIT_ASSERT(setOptimum(solver, opt, true));
		CPPUNIT_ASSERT(solver.decisionLevel() == 1 && solver.queueSize() == 3);
		solver.propagate();
		opt[0] = 0;
		CPPUNIT_ASSERT(!setOptimum(solver, opt, true));
		CPPUNIT_ASSERT(solver.hasConflict());
		CPPUNIT_ASSERT(solver.clearAssumptions());
		CPPUNIT_ASSERT(newMin->integrateBound(solver) == false && solver.hasConflict());
		CPPUNIT_ASSERT(!solver.resolveConflict());
		newMin->destroy(&solver, true);
		newMin = 0;
	}
	void testIntegrateBug() {
		WeightLitVec min;
		min.push_back( WeightLiteral(a, 1) );
		min.push_back( WeightLiteral(b, 1) );
		min.push_back( WeightLiteral(c, 1) );
		data   = MinimizeBuilder().addRule(min).build(ctx);
		wsum_t bound = 2;
		Solver& s = *ctx.master();
		newMin = createMin(ctx, s, data, MinimizeMode_t::bb_step_dec);
		data->setMode(MinimizeMode_t::optimize, &bound, 1);
		s.pushRoot(s.tagLiteral());
		s.pushRoot(a);
		s.pushRoot(b);
		s.pushRoot(c);
		CPPUNIT_ASSERT(!newMin->integrateBound(s));
	}
	void testReasonBug() {
		WeightLitVec aMin, bMin;
		aMin.push_back( WeightLiteral(a, 1) );
		aMin.push_back( WeightLiteral(b, 1) );
		bMin.push_back( WeightLiteral(d, 2) );
		bMin.push_back( WeightLiteral(e, 1) );
		bMin.push_back( WeightLiteral(f, 3) );
		
		newMin = buildAndAttach(MinimizeBuilder()
			.addRule(aMin)
			.addRule(bMin));
		Solver& solver = *ctx.master();
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(a) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(b) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(d) && solver.propagate());
		newMin->commitUpperBound(solver);
		solver.backtrack();
		CPPUNIT_ASSERT_EQUAL(true, newMin->integrateBound(solver));
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(e) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.isTrue(~f));
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(c) && solver.propagate());
		solver.backtrack();
		CPPUNIT_ASSERT_EQUAL(true, solver.isTrue(~f));
		LitVec r;
		solver.reason(~f, r);
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), e) == r.end());
	}

	void testSmartBacktrack() {
		WeightLitVec aMin;
		aMin.push_back( WeightLiteral(a, 1) );
		aMin.push_back( WeightLiteral(b, 1) );
		aMin.push_back( WeightLiteral(c, 1) );
		newMin = buildAndAttach(MinimizeBuilder().addRule(aMin));
		Solver& solver = *ctx.master();
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(a) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(b) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(~c) && solver.propagate());
		
		newMin->commitUpperBound(solver);
		CPPUNIT_ASSERT_EQUAL(true, newMin->integrateBound(solver));
		
		CPPUNIT_ASSERT_EQUAL(true, solver.isTrue(~b));
		CPPUNIT_ASSERT_EQUAL(true, solver.isTrue(~c));
	}

	void testBacktrackToTrue() {
		WeightLitVec min1, min2;
		min1.push_back( WeightLiteral(a, 1) );
		min2.push_back( WeightLiteral(b, 1) );
		newMin = buildAndAttach(MinimizeBuilder()
			.addRule(min1)
			.addRule(min2));
		Solver& solver = *ctx.master();
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(~a) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.force(b, 0) && solver.propagate());
			
		newMin->commitUpperBound(solver);
		solver.backtrack();
		CPPUNIT_ASSERT_EQUAL(false, newMin->integrateBound(solver));
	}

	void testMultiAssignment() {
		WeightLitVec min1, min2;
		min1.push_back( WeightLiteral(a, 1) );
		min1.push_back( WeightLiteral(b, 1) );
		min1.push_back( WeightLiteral(c, 1) );
		min1.push_back( WeightLiteral(d, 1) );
		min1.push_back( WeightLiteral(e, 1) );

		min2.push_back( WeightLiteral(f, 1) );
		
		newMin = buildAndAttach(MinimizeBuilder()
			.addRule(min1)
			.addRule(min2));
		Solver& solver = *ctx.master();
		SumVec opt(newMin->numRules());
		opt[0] = 3;
		opt[1] = 0;
		CPPUNIT_ASSERT_EQUAL(true, setOptimum(solver, opt, false));
	
		solver.assume(f);
		solver.force(a, 0);
		solver.force(b, 0);
		solver.force(c, 0);
		
		CPPUNIT_ASSERT_EQUAL(false, solver.propagate());
	}
	
	void testBugBacktrackFromFalse() {
		WeightLitVec min1, min2;
		min1.push_back( WeightLiteral(a, 1) );
		min1.push_back( WeightLiteral(b, 1) );
		min1.push_back( WeightLiteral(c, 1) );
		min2.push_back( WeightLiteral(d, 1) );
		min2.push_back( WeightLiteral(e, 1) );
		min2.push_back( WeightLiteral(f, 1) );
		
		newMin = buildAndAttach(MinimizeBuilder()
			.addRule(min1)
			.addRule(min2));
		ctx.setProject(x.var(), true);
		Solver& solver = *ctx.master();
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(a) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(b) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(x) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.force(~c,0) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(y) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.force(d,0) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.force(e,0) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.force(~f,0) && solver.propagate());
		
		newMin->commitUpperBound(solver);
		solver.undoUntil(3);
		solver.setBacktrackLevel(3);
		CPPUNIT_ASSERT(newMin->integrateBound(solver));
		CPPUNIT_ASSERT_EQUAL(true, solver.force(f,0) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.isTrue(~d));
		CPPUNIT_ASSERT_EQUAL(true, solver.isTrue(~e));
		
		newMin->commitUpperBound(solver);
		solver.undoUntil(2);
		solver.backtrack();
		CPPUNIT_ASSERT(newMin->integrateBound(solver));
		CPPUNIT_ASSERT_EQUAL(true, solver.isTrue(~x));
		CPPUNIT_ASSERT_EQUAL(true, solver.isTrue(~f));
		CPPUNIT_ASSERT_EQUAL(true, solver.isTrue(~d));
		CPPUNIT_ASSERT_EQUAL(true, solver.isTrue(~e));
		CPPUNIT_ASSERT_EQUAL(true, solver.isTrue(~c));
	}
	
	void testBugBacktrackToTrue() {
		WeightLitVec min1, min2;
		min1.push_back( WeightLiteral(a, 1) );
		min1.push_back( WeightLiteral(b, 1) );
		min1.push_back( WeightLiteral(~b, 2) );
		min2.push_back( WeightLiteral(a, 1) );
		min2.push_back( WeightLiteral(b, 1) );
		min2.push_back( WeightLiteral(c, 1) );
		
		newMin = buildAndAttach(MinimizeBuilder()
			.addRule(min1)
			.addRule(min2));
		Solver& solver = *ctx.master();
		
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(a) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(b) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(c) && solver.propagate());

		newMin->commitUpperBound(solver);
		CPPUNIT_ASSERT(newMin->integrateBound(solver) && 1 == solver.decisionLevel());
		CPPUNIT_ASSERT(solver.propagate());
		
		newMin->commitUpperBound(solver);
		solver.undoUntil(0);
		CPPUNIT_ASSERT(newMin->integrateBound(solver));
		CPPUNIT_ASSERT(solver.isTrue(~a));
		CPPUNIT_ASSERT(solver.value(b.var()) == value_free);
	}

	void testBugInitOptHierarch() {
		WeightLitVec aMin, bMin;
		aMin.push_back( WeightLiteral(a, 1) );
		aMin.push_back( WeightLiteral(b, 1) );
		bMin.push_back( WeightLiteral(c, 1) );
		bMin.push_back( WeightLiteral(d, 1) );
		data = MinimizeBuilder()
			.addRule(aMin)
			.addRule(bMin)
			.build(ctx);
		wsum_t bound[2] = {wsum_t(1),wsum_t(1)};
		data->setMode(MinimizeMode_t::optimize, bound, 2);
		newMin = createMin(ctx, *ctx.master(), data, MinimizeMode_t::bb_step_hier);
		newMin->integrateBound(*ctx.master());
		CPPUNIT_ASSERT(ctx.master()->value(a.var()) == value_free);
		ctx.master()->assume(a) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(b));
		CPPUNIT_ASSERT(ctx.master()->value(c.var()) == value_free);
		ctx.master()->assume(c) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(d));
	}

	void testBugAdjustSum() {
		WeightLitVec aMin, bMin;
		aMin.push_back( WeightLiteral(a, 1) );
		aMin.push_back( WeightLiteral(b, 1) );
		bMin.push_back( WeightLiteral(~a, 1) );
		bMin.push_back( WeightLiteral(d, 1) );
		data = MinimizeBuilder()
			.addRule(aMin)
			.addRule(bMin)
			.build(ctx);
		newMin = static_cast<DefaultMinimize*>(data->attach(*ctx.master(), MinimizeMode_t::opt_bb));
		SumVec opt;
		opt.push_back(1);
		opt.push_back(1);
		setOptimum(*ctx.master(), opt, true);
		// a ~b ~d is a valid model!
		CPPUNIT_ASSERT(ctx.master()->value(a.var()) == value_free);
		CPPUNIT_ASSERT(ctx.master()->assume(a) && ctx.master()->propagate());
		CPPUNIT_ASSERT(ctx.master()->assume(~b) && ctx.master()->propagate());
		CPPUNIT_ASSERT(ctx.master()->assume(~d) && ctx.master()->propagate());
	}

	void testWeightNullBug() {
		WeightLitVec min1;
		min1.push_back( WeightLiteral(a, 1) );
		min1.push_back( WeightLiteral(b, 0) );
		newMin = buildAndAttach(MinimizeBuilder().addRule(min1));
		Solver& solver = *ctx.master();
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(a) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(b) && solver.force(~c,0) && solver.propagate());
		newMin->commitUpperBound(solver);
		newMin->integrateBound(solver);
		CPPUNIT_ASSERT(0u == solver.decisionLevel() && solver.isFalse(a));
	}

	void testAdjust() {
		WeightLitVec min1;
		min1.push_back( WeightLiteral(a, 1) );
		min1.push_back( WeightLiteral(b, 1) );
		newMin = buildAndAttach(MinimizeBuilder().addRule(min1, -2));
		Solver& solver = *ctx.master();
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(a) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(b) && solver.propagate());
		newMin->commitUpperBound(solver);
		CPPUNIT_ASSERT(0 == newMin->shared()->optimum(0));
		
		solver.clearAssumptions();
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(~a) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(~b) && solver.propagate());
		newMin->commitUpperBound(solver);
		CPPUNIT_ASSERT(-2 == newMin->shared()->optimum(0));
	}

	void testAdjustFact() {
		WeightLitVec min1;
		min1.push_back( WeightLiteral(a, 2) );
		min1.push_back( WeightLiteral(b, 1) );
		min1.push_back( WeightLiteral(c, 1) );
		min1.push_back( WeightLiteral(d, 1) );
		data = MinimizeBuilder().addRule(min1, -2).build(ctx);
		Solver& solver = *ctx.master();
		ctx.addUnary(a);
		solver.propagate();
		newMin = createMin(ctx, solver, data);
		newMin->integrateBound(solver);
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(b) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(c) && solver.propagate());
		CPPUNIT_ASSERT_EQUAL(true, solver.assume(d) && solver.propagate());
		newMin->commitUpperBound(solver);
		newMin->integrateBound(solver);
		CPPUNIT_ASSERT(2 == solver.decisionLevel());
	}

	void testAssumption() {
		SharedContext ctx;
		a = posLit(ctx.addVar(Var_t::atom_var));
		b = posLit(ctx.addVar(Var_t::atom_var));
		c = posLit(ctx.addVar(Var_t::atom_var));
		ctx.startAddConstraints();
		WeightLitVec min1;
		min1.push_back( WeightLiteral(a, 1) );
		min1.push_back( WeightLiteral(b, 1) );
		min1.push_back( WeightLiteral(c, 1) );
		Solver& solver = *ctx.master();
		data   = MinimizeBuilder().addRule(min1).build(ctx);
		newMin = createMin(ctx, solver, data, MinimizeMode_t::bb_step_inc);
		Literal minAssume = posLit(solver.pushTagVar(true));
		SumVec opt(1, 0);
		setOptimum(solver, opt, false);
		CPPUNIT_ASSERT(solver.isFalse(a) && solver.reason(~a).constraint() == newMin);
		CPPUNIT_ASSERT(solver.isFalse(b) && solver.reason(~b).constraint() == newMin);
		CPPUNIT_ASSERT(solver.isFalse(c) && solver.reason(~c).constraint() == newMin);

		LitVec r;
		solver.reason(~a, r);
		CPPUNIT_ASSERT(r.size() == 1 && r[0] == minAssume);

		solver.clearAssumptions();
		CPPUNIT_ASSERT(solver.numAssignedVars() == 0);
	}

	void testHierarchicalSetModel() {
		WeightLitVec min;
		min.push_back( WeightLiteral(a, 1) );
		min.push_back( WeightLiteral(b, 1) );
		min.push_back( WeightLiteral(c, 1) );
		MinimizeBuilder builder;
		builder.addRule(min);
		min.clear();
		min.push_back( WeightLiteral(d, 1) );
		min.push_back( WeightLiteral(e, 1) );
		min.push_back( WeightLiteral(f, 1) );
		builder.addRule(min);
		Solver& solver = *ctx.master();
		data   = builder.build(ctx);
		newMin = createMin(ctx, solver, data, MinimizeMode_t::bb_step_hier);
		newMin->integrateBound(solver);
		solver.assume(a); solver.propagate();
		solver.assume(b); solver.propagate();
		solver.assume(c); solver.propagate();
		solver.assume(d); solver.propagate();
		solver.assume(e); solver.propagate();
		solver.assume(f); solver.propagate();
		newMin->commitUpperBound(solver);
		solver.undoUntil(solver.level(b.var()));
		newMin->integrateBound(solver);
		CPPUNIT_ASSERT(solver.isFalse(c));
		CPPUNIT_ASSERT(solver.numAssignedVars() == 4);
	}

	void testHierarchical() {
		MinimizeBuilder builder;
		WeightLitVec min;
		min.push_back( WeightLiteral(a, 1) );
		builder.addRule(min);
		min.clear();
		min.push_back( WeightLiteral(~b, 1) );
		builder.addRule(min);
		
		ctx.addBinary(~a, b);
		ctx.addBinary(a, ~b);
		Solver& solver = *ctx.master();
		data   = builder.build(ctx);
		newMin = createMin(ctx, solver, data, MinimizeMode_t::bb_step_hier);
		newMin->integrateBound(solver);
		solver.assume(a);
		solver.propagate();
		newMin->commitUpperBound(solver);
		solver.backtrack();
		CPPUNIT_ASSERT(newMin->integrateBound(solver));
		CPPUNIT_ASSERT(solver.propagate() == true);
		newMin->commitUpperBound(solver);
		CPPUNIT_ASSERT(!newMin->integrateBound(solver));
	}
	void testInconsistent() {
		MinimizeBuilder builder;
		WeightLitVec min;
		min.push_back( WeightLiteral(a, 1) );
		min.push_back( WeightLiteral(b, 1) );
		min.push_back( WeightLiteral(c, 1) );
		builder.addRule(min);
		wsum_t bound = 1;
		ctx.addUnary(a);
		ctx.addUnary(b);
		CPPUNIT_ASSERT(buildAndAttach(builder, MinimizeMode_t::optimize, &bound, 1) == 0);
	}
private:
	uint32 countMinLits() const {
		uint32 lits = 0;
		const WeightLiteral* it = newMin->shared()->lits;
		for (; !isSentinel(it->first); ++it, ++lits) { ; }
		return lits;
	}
	
	bool setOptimum(Solver& s, SumVec& vec, bool less) {
		SharedMinimizeData* data = const_cast<SharedMinimizeData*>(newMin->shared());
		if (!less) {
			vec.back() += 1;
		}
		data->setOptimum(&vec[0]);
		while (!newMin->integrateBound(s)) {
			if (!s.resolveConflict()) { return false; }
		}
		return true;
	}
	DefaultMinimize* createMin(SharedContext& ctx, Solver& s, SharedMinimizeData* data, MinimizeMode_t::BBOption param = MinimizeMode_t::bb_step_def) {
		ctx.endInit();
		return static_cast<DefaultMinimize*>(data->attach(s, MinimizeMode_t::opt_bb, param));
	}	
	DefaultMinimize* buildAndAttach(MinimizeBuilder& x, MinimizeMode m = MinimizeMode_t::optimize, const wsum_t* b = 0, uint32 bs = 0) {
		DefaultMinimize* con = 0;
		if ( (data = x.build(ctx)) != 0 && data->setMode(m, b, bs) ) {
			con = createMin(ctx, *ctx.master(), data);
			con->integrateBound(*ctx.master());
		}
		return con;
	}
	SharedContext ctx;
	DefaultMinimize* newMin;
	SharedMinimizeData*   data;
	Literal a, b, c, d, e, f, x, y;
};

class UncoreMinimizeTest : public CppUnit::TestFixture {
	CPPUNIT_TEST_SUITE(UncoreMinimizeTest);
	CPPUNIT_TEST(testEmpty);
	CPPUNIT_TEST(testEnumerate);
	CPPUNIT_TEST(testOptimize);
	CPPUNIT_TEST(testOptimizeGP);
	CPPUNIT_TEST(testMtBug1);
	CPPUNIT_TEST(testNegativeLower);
	CPPUNIT_TEST_SUITE_END(); 
public:
	void setUp() {
		data = 0;
		min  = 0;
	}
	void tearDown() {
		if (min) {
			min->destroy(0,false);
		}
		if (data) {
			data->release();
		}
	}
	void testEmpty() {
		MinimizeBuilder b;
		ctx.startAddConstraints();
		data = b.build(ctx);
		ctx.endInit();
		min = data->attach(*ctx.master(), MinimizeMode_t::opt_usc);
		CPPUNIT_ASSERT(min->integrate(*ctx.master()));
	}
	void testEnumerate() {
		Var a = ctx.addVar(Var_t::atom_var);
		Var b = ctx.addVar(Var_t::atom_var);
		Var c = ctx.addVar(Var_t::atom_var);
		ctx.startAddConstraints();
		WeightLitVec lits;
		MinimizeBuilder builder;
		lits.push_back(WeightLiteral(posLit(a), 1));
		lits.push_back(WeightLiteral(posLit(b), 1));
		lits.push_back(WeightLiteral(posLit(c), 1));
		builder.addRule(lits);
		data = builder.build(ctx);
		ctx.endInit();
		wsum_t bound = 1;
		data->setMode(MinimizeMode_t::enumerate, &bound, 1);
		min = data->attach(*ctx.master(), MinimizeMode_t::opt_usc);
		CPPUNIT_ASSERT(min->integrate(*ctx.master()));
		
		ctx.master()->assume(posLit(a));
		ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(posLit(b)));
		CPPUNIT_ASSERT(ctx.master()->isFalse(posLit(c)));
	}
	void testOptimize() {
		Var a = ctx.addVar(Var_t::atom_var);
		Var b = ctx.addVar(Var_t::atom_var);
		Solver& s = ctx.startAddConstraints();
		WeightLitVec lits;
		MinimizeBuilder builder;
		lits.push_back(WeightLiteral(posLit(a), 1));
		lits.push_back(WeightLiteral(posLit(b), 1));
		builder.addRule(lits);
		data = builder.build(ctx);
		ctx.endInit();
		data->setMode(MinimizeMode_t::optimize);
		min = data->attach(s, MinimizeMode_t::opt_usc, MinimizeMode_t::usc_preprocess);
		BasicSolve solve(s);
		LitVec gp;
		while (min->integrate(s) || min->handleUnsat(s, true, gp)) {
			ValueRep v = solve.solve();
			CPPUNIT_ASSERT(v == value_true);
			min->handleModel(s);
		}
		CPPUNIT_ASSERT(gp.empty());
		CPPUNIT_ASSERT(s.isFalse(lits[0].first) && s.isFalse(lits[1].first));
	}
	void testOptimizeGP() {
		Var a = ctx.addVar(Var_t::atom_var);
		Var b = ctx.addVar(Var_t::atom_var);
		Solver& s = ctx.startAddConstraints();
		WeightLitVec lits;
		MinimizeBuilder builder;
		lits.push_back(WeightLiteral(posLit(a), 1));
		lits.push_back(WeightLiteral(posLit(b), 1));
		builder.addRule(lits);
		data = builder.build(ctx);
		ctx.endInit();
		data->setMode(MinimizeMode_t::optimize);
		min = data->attach(s, MinimizeMode_t::opt_usc, MinimizeMode_t::usc_preprocess);
		BasicSolve solve(s);
		LitVec gp; gp.push_back(posLit(a));
		solve.assume(gp);
		gp.clear();
		while (min->integrate(s) || min->handleUnsat(s, true, gp)) {
			ValueRep v = solve.solve();
			CPPUNIT_ASSERT(v == value_true);
			min->handleModel(s);
		}
		CPPUNIT_ASSERT(s.rootLevel() == 1 && s.decision(1) == posLit(a));
		CPPUNIT_ASSERT(s.isTrue(lits[0].first) && s.isFalse(lits[1].first));
	}

	void testMtBug1() {
		WeightLitVec lits;
		lits.push_back(WeightLiteral(posLit(ctx.addVar(Var_t::atom_var)), 1));
		lits.push_back(WeightLiteral(posLit(ctx.addVar(Var_t::atom_var)), 1));
		Solver& s1 = ctx.startAddConstraints();
		data       = MinimizeBuilder().addRule(lits).build(ctx);
		ctx.setConcurrency(2, SharedContext::mode_reserve);
		ctx.endInit(true);
		Solver& s2 = *ctx.solver(1);
		data->setMode(MinimizeMode_t::enumOpt);
		MinimizeConstraint* m1 = data->attach(s1, MinimizeMode_t::opt_usc, MinimizeMode_t::usc_preprocess);
		MinimizeConstraint* m2 = data->attach(s2, MinimizeMode_t::opt_usc, MinimizeMode_t::usc_preprocess);
		s1.setEnumerationConstraint(m1);
		s2.setEnumerationConstraint(m2);
		BasicSolve solve(s1);
		LitVec gp;
		while (m1->integrate(s1) || m1->handleUnsat(s1, true, gp)) {
			ValueRep v = solve.solve();
			CPPUNIT_ASSERT(v == value_true);
			m1->handleModel(s1);
		}
		data->markOptimal();
		m1->relax(s1, true);
		m2->relax(s2, true);
		solve.reset(s2, s2.searchConfig());
		uint32 numModels = 0;
		s2.setPref(1, ValueSet::user_value, value_true);
		for (;;) {
			ValueRep v = m2->integrate(s2) ? solve.solve() : value_false;
			if (v == value_true) {
				++numModels;
				CPPUNIT_ASSERT(s2.isFalse(lits[0].first));
				CPPUNIT_ASSERT(s2.isFalse(lits[1].first));
				if (!s2.backtrack()) { break; }
			}
			else if (v == value_false) {
				break;
			}
		}
		CPPUNIT_ASSERT(numModels == 1);
	}
	void testNegativeLower() {
		Literal a = posLit(ctx.addVar(Var_t::atom_var));
		Literal b = posLit(ctx.addVar(Var_t::atom_var));
		Solver& s = ctx.startAddConstraints();
		ctx.addBinary(a, b);
		WeightLitVec aMin, bMin;
		aMin.push_back( WeightLiteral(a, 1) );
		aMin.push_back( WeightLiteral(b, 1) );
		bMin.push_back( WeightLiteral(~a, 1) );
		data = MinimizeBuilder()
			.addRule(aMin)
			.addRule(bMin)
			.build(ctx);
		ctx.endInit();
		data->setMode(MinimizeMode_t::optimize);
		min = data->attach(s, MinimizeMode_t::opt_usc, MinimizeMode_t::usc_preprocess);
		
		LitVec ignore;
		while (!min->integrate(*ctx.master()) && min->handleUnsat(s, true, ignore)) { ; }
		CPPUNIT_ASSERT(s.assume(~a) && s.propagate());
		CPPUNIT_ASSERT(s.assume(b) && s.propagate());
		CPPUNIT_ASSERT(min->handleModel(s));
		s.undoUntil(0);
		while (!min->integrate(*ctx.master()) && min->handleUnsat(s, true, ignore)) { ; }
		CPPUNIT_ASSERT(s.assume(a) && s.propagate());
		CPPUNIT_ASSERT(s.isFalse(b));
		min->handleModel(s);
		s.undoUntil(0);
		while (!min->integrate(*ctx.master()) && min->handleUnsat(s, true, ignore)) { ; }
		CPPUNIT_ASSERT(s.hasConflict());
	}
private:
	SharedContext       ctx;
	SharedMinimizeData* data;
	MinimizeConstraint* min;
};
CPPUNIT_TEST_SUITE_REGISTRATION(DefaultMinimizeTest);
CPPUNIT_TEST_SUITE_REGISTRATION(UncoreMinimizeTest);
} } 
