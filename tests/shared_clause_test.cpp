//
// Copyright (c) 2009-2017 Benjamin Kaufmann
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
#include <clasp/solver.h>
#include <clasp/clause.h>
#include <algorithm>
#ifdef _MSC_VER
#pragma warning (disable : 4267) //  conversion from 'size_t' to unsigned int
#pragma once
#endif


namespace Clasp { namespace Test {
using namespace Clasp::mt;
class SharedClauseTest : public CppUnit::TestFixture {
	CPPUNIT_TEST_SUITE(SharedClauseTest);
	CPPUNIT_TEST(testClauseCtorAddsWatches);
	CPPUNIT_TEST(testPropSharedClauseConflict);
	CPPUNIT_TEST(testPropRandomClauses);
	CPPUNIT_TEST(testPropAlreadySatisfied);
	CPPUNIT_TEST(testReasonBumpsActivityIfLearnt);
	CPPUNIT_TEST(testSimplifySAT);
	CPPUNIT_TEST(testSimplifyUnique);
	CPPUNIT_TEST(testSimplifyShared);

	CPPUNIT_TEST(testCloneShared);
	CPPUNIT_TEST_SUITE_END();
public:
	typedef ConstraintInfo ClauseInfo;
	SharedClauseTest() {
		a1 = posLit(ctx.addVar(Var_t::Atom));
		a2 = posLit(ctx.addVar(Var_t::Atom));
		a3 = posLit(ctx.addVar(Var_t::Atom));
		b1 = posLit(ctx.addVar(Var_t::Body));
		b2 = posLit(ctx.addVar(Var_t::Body));
		b3 = posLit(ctx.addVar(Var_t::Body));

		for (int i = 6; i < 15; ++i) {
			ctx.addVar(Var_t::Atom);
		}
		ctx.startAddConstraints(10);
	}
	void testClauseCtorAddsWatches() {
		makeLits(2, 2);
		ClauseHead* sharedCl= createShared(ctx, clLits, ClauseInfo());
		ctx.add(sharedCl);
		CPPUNIT_ASSERT_EQUAL(2, countWatches(*ctx.master(), sharedCl, clLits));
	}

	void testPropSharedClauseConflict() {
		makeLits(2, 2);
		ClauseHead* c = createShared(ctx, clLits, ClauseInfo());
		simplePropTest(c);
	}

	void testPropRandomClauses() {
		for (int i = 0; i != 100; ++i) {
			SharedContext cc;
			for (int j = 0; j < 12; ++j) { cc.addVar(Var_t::Atom); }
			cc.startAddConstraints(1);

			makeRandomClause( (rand() % 10) + 2 );
			ClauseHead* c = createShared(cc, clLits, ClauseInfo());
			cc.add(c);
			check(*cc.master(), c);
		}
	}

	void testPropAlreadySatisfied() {
		makeLits(2, 2);
		ClauseHead* c1 = createShared(ctx, clLits, ClauseInfo());
		ctx.add(c1);

		// satisfy the clauses...
		ctx.addUnary(clLits[3]);
		ctx.master()->propagate();

		// ...make all but one literal false
		ctx.addUnary(~clLits[0]);
		ctx.addUnary(~clLits[1]);
		ctx.master()->propagate();

		// ...and assert that the last literal is still unassigned
		CPPUNIT_ASSERT(value_free == ctx.master()->value(clLits[2].var()));
	}

	void testReasonBumpsActivityIfLearnt() {
		makeLits(4, 0);
		ctx.endInit();
		ClauseInfo e(Constraint_t::Conflict);
		ClauseHead* c = createShared(ctx, clLits, e);
		Solver& solver= *ctx.master();
		solver.addLearnt(c, (uint32)clLits.size());

		solver.assume(~clLits[0]);
		solver.propagate();
		solver.assume(~clLits[1]);
		solver.propagate();
		uint32 a = c->activity().activity();
		solver.assume(~clLits[2]);
		solver.force(~clLits[3], Antecedent(0));
		CPPUNIT_ASSERT_EQUAL(false, solver.propagate());
		CPPUNIT_ASSERT_EQUAL(a+1, c->activity().activity());
	}

	void testSimplifySAT() {
		makeLits(3, 2);
		ClauseHead* c1 = createShared(ctx, clLits, ClauseInfo());
		ctx.add(c1);

		ctx.addUnary(~clLits[4]);
		ctx.addUnary(clLits[3]);
		ctx.master()->propagate();

		CPPUNIT_ASSERT_EQUAL(true, c1->simplify(*ctx.master(), false));
	}

	void testSimplifyUnique() {
		makeLits(3, 3);
		ClauseHead* c = createShared(ctx, clLits, ClauseInfo());
		ctx.add(c);

		ctx.addUnary(~clLits[2]);
		ctx.addUnary(~clLits[3]);
		ctx.master()->propagate();

		CPPUNIT_ASSERT_EQUAL(false, c->simplify(*ctx.master(), false));
		CPPUNIT_ASSERT(4 == c->size());
		CPPUNIT_ASSERT_EQUAL(2, countWatches(*ctx.master(), c, clLits));
	}

	void testSimplifyShared() {
		makeLits(3, 3);
		SharedLiterals* sLits   = SharedLiterals::newShareable(clLits, Constraint_t::Conflict);
		CPPUNIT_ASSERT(sLits->unique() && sLits->type() == Constraint_t::Conflict && sLits->size() == 6);
		SharedLiterals* other   = sLits->share();
		CPPUNIT_ASSERT(!sLits->unique());

		ctx.addUnary(~clLits[2]);
		ctx.addUnary(~clLits[3]);
		ctx.master()->propagate();

		CPPUNIT_ASSERT_EQUAL(uint32(4), sLits->simplify(*ctx.master()));
		CPPUNIT_ASSERT_EQUAL(uint32(6), sLits->size());
		sLits->release();
		other->release();
	}

	void testCloneShared() {
		makeLits(3, 2);
		ClauseHead* c = createShared(ctx, clLits, ClauseInfo());
		Solver& solver2 = ctx.pushSolver();
		ctx.endInit(true);
		ClauseHead* clone = (ClauseHead*)c->cloneAttach(solver2);
		LitVec lits;
		clone->toLits(lits);
		CPPUNIT_ASSERT(lits == clLits);
		CPPUNIT_ASSERT(countWatches(solver2, clone, clLits) == 2);
		c->destroy(ctx.master(), true);

		for (uint32 i = 0; i != clLits.size()-1; ++i) {
			solver2.assume(~clLits[i]);
			solver2.propagate();
		}
		CPPUNIT_ASSERT(solver2.isTrue(clLits.back()));
		CPPUNIT_ASSERT(solver2.reason(clLits.back()) == clone);

		clone->destroy(&solver2, true);

	}
private:
	SharedContext ctx;
	LitVec clLits;
	Literal a1, a2, a3, b1, b2, b3;
	ClauseHead* createShared(SharedContext& ctx, const LitVec& lits, const ClauseInfo& e) {
		assert(lits.size() >= 2);
		SharedLiterals* shared_lits = SharedLiterals::newShareable(lits, e.type());
		return SharedLitsClause::newClause(*ctx.master(), shared_lits, e, &lits[0], false);
	}

	void simplePropTest(ClauseHead* c) {
		Solver& solver = *ctx.master();
		solver.add(c);
		solver.assume(~clLits[0]);
		solver.propagate();
		solver.assume( ~clLits.back() );
		solver.propagate();
		solver.assume(~clLits[1]);
		solver.propagate();

		CPPUNIT_ASSERT_EQUAL(true, solver.isTrue( clLits[2] ) );
		CPPUNIT_ASSERT_EQUAL(true, c->locked(solver));
		Antecedent reason = solver.reason(clLits[2]);
		CPPUNIT_ASSERT(reason == c);

		LitVec r;
		reason.reason(solver, clLits[2], r);
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~clLits[0]) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~clLits[1]) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~clLits[3]) != r.end());
	}
	int countWatches(const Solver& s, ClauseHead* c, const LitVec& lits) {
		int w     = 0;
		for (LitVec::size_type i = 0; i != lits.size(); ++i) {
			w += s.hasWatch(~lits[i], c);
		}
		return w;
	}
	void check(Solver& solver, ClauseHead* c) {
		std::string s = toString(clLits);
		std::random_shuffle(clLits.begin(), clLits.end());
		CPPUNIT_ASSERT( value_free == solver.value(clLits.back().var()) );
		for (LitVec::size_type i = 0; i != clLits.size() - 1; ++i) {
			CPPUNIT_ASSERT( value_free == solver.value(clLits[i].var()) );
			solver.force(~clLits[i], 0);
			solver.propagate();
		}
		CPPUNIT_ASSERT_EQUAL_MESSAGE(s.c_str(), true, solver.isTrue(clLits.back()));

		Antecedent reason = solver.reason(clLits.back());
		CPPUNIT_ASSERT(reason == c);
		LitVec r;
		c->reason(solver, clLits.back(), r);
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
	void makeLits(int pos, int neg) {
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
	}
	void makeRandomClause(int size) {
		int pos = rand() % size + 1;
		makeLits( pos, size - pos );
	}
};
CPPUNIT_TEST_SUITE_REGISTRATION(SharedClauseTest);
} }
