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
#include <clasp/unfounded_check.h>
#include <clasp/logic_program.h>
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

	CPPUNIT_TEST(testWeightReason);
	CPPUNIT_TEST(testCardExtSet);
	CPPUNIT_TEST(testCardNoSimp);
	CPPUNIT_TEST_SUITE_END();
public:
	UnfoundedCheckTest() : ufs(0) { }
	void tearDown() {
		ufs = 0;
	}
	Solver& solver() { return *ctx.master(); }
	bool propagateUfs() {
		return ufs->propagateFixpoint(solver(), 0);
	}
	void testAllUncoloredNoUnfounded() {
		setupSimpleProgram();
		uint32 x = solver().numAssignedVars();
		CPPUNIT_ASSERT_EQUAL(true, propagateUfs());
		CPPUNIT_ASSERT_EQUAL(x, solver().numAssignedVars());
	}

	void testAlternativeSourceNotUnfounded() {
		setupSimpleProgram();
		solver().assume( index[6] );
		solver().propagateUntil(ufs.get());
		uint32 old = solver().numAssignedVars();
		CPPUNIT_ASSERT_EQUAL(true, propagateUfs());
		CPPUNIT_ASSERT_EQUAL(old, solver().numAssignedVars());
	}

	void testOnlyOneSourceUnfoundedIfMinus() {
		setupSimpleProgram();
		solver().assume( index[6] );
		solver().assume( index[5] );
		solver().propagateUntil(ufs.get());
		uint32 old = solver().numAssignedVars();
		uint32 oldC = ctx.numConstraints();
		CPPUNIT_ASSERT_EQUAL(true, propagateUfs());
		CPPUNIT_ASSERT(old < solver().numAssignedVars());
		CPPUNIT_ASSERT(solver().isFalse(index[4]));
		CPPUNIT_ASSERT(solver().isFalse(index[1]));
		CPPUNIT_ASSERT(!solver().isFalse(index[2]));
		CPPUNIT_ASSERT(oldC+1 == ctx.numConstraints() + ctx.numLearntShort());
	}

	void testWithSimpleCardinalityConstraint() {
		lpAdd(lp.start(ctx), "{x2}. x1 :- 1 {x1, x2}.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		attachUfs();

		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(2u, solver().numVars());
		CPPUNIT_ASSERT_EQUAL(0u, solver().numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, propagateUfs() );
		CPPUNIT_ASSERT_EQUAL(0u, solver().numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, solver().assume(~lp.getLiteral(2)));
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(1u, solver().numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, propagateUfs() );
		CPPUNIT_ASSERT_EQUAL(2u, solver().numAssignedVars());
		LitVec r;
		solver().reason(~lp.getLiteral(1), r);
		CPPUNIT_ASSERT(1 == r.size());
		CPPUNIT_ASSERT(r[0] == ~lp.getLiteral(2));
	}
	void testWithSimpleWeightConstraint() {
		lpAdd(lp.start(ctx), "{x2;x3}. x1 :- 2 {x1 = 2, x2 = 2, x3}.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		attachUfs();
		ufs->setReasonStrategy(DefaultUnfoundedCheck::only_reason);

		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(3u, solver().numVars());
		CPPUNIT_ASSERT_EQUAL(0u, solver().numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, propagateUfs() );
		CPPUNIT_ASSERT_EQUAL(0u, solver().numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, solver().assume(~lp.getLiteral(3)));
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(1u, solver().numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, propagateUfs() );
		CPPUNIT_ASSERT_EQUAL(1u, solver().numAssignedVars());

		CPPUNIT_ASSERT_EQUAL(true, solver().assume(~lp.getLiteral(2)));
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(2u, solver().numAssignedVars());

		CPPUNIT_ASSERT_EQUAL(true, propagateUfs() );
		CPPUNIT_ASSERT_EQUAL(3u, solver().numAssignedVars());

		LitVec r;
		solver().reason(~lp.getLiteral(1), r);
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~lp.getLiteral(2)) != r.end());

		solver().undoUntil(0);
		CPPUNIT_ASSERT_EQUAL(true, solver().assume(~lp.getLiteral(2)));
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(1u, solver().numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, propagateUfs() );
		CPPUNIT_ASSERT_EQUAL(2u, solver().numAssignedVars());
		r.clear();
		solver().reason(~lp.getLiteral(1), r);
		CPPUNIT_ASSERT(1 == r.size());
		CPPUNIT_ASSERT(r[0] == ~lp.getLiteral(2));
	}

	void testNtExtendedBug() {
		lpAdd(lp.start(ctx),
			"{x1;x2;x3}.\n"
			"x4 :- 2 {x2, x4, x5}.\n"
			"x5 :- x4, x3.\n"
			"x5 :- x1.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		attachUfs();

		// T: {x4,x3}
		solver().assume(Literal(6, false));
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(true, propagateUfs());
		solver().assume(~lp.getLiteral(1));
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(false, propagateUfs());  // {x4, x5} are unfounded!

		solver().undoUntil(0);
		ufs->reset();

		// F: {x4,x3}
		solver().assume(Literal(6, true));
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		// F: x1
		solver().assume(~lp.getLiteral(1));
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		// x5 is false because both of its bodies are false
		CPPUNIT_ASSERT_EQUAL(true, solver().isFalse(lp.getLiteral(5)));

		// x4 is now unfounded but its defining body is not
		CPPUNIT_ASSERT_EQUAL(true, propagateUfs());
		CPPUNIT_ASSERT_EQUAL(true, solver().isFalse(lp.getLiteral(4)));
		LitVec r;
		solver().reason(~lp.getLiteral(4), r);
		CPPUNIT_ASSERT(r.size() == 1 && r[0] == ~lp.getLiteral(5));
	}

	void testNtExtendedFalse() {
		lpAdd(lp.start(ctx, LogicProgram::AspOptions().noEq()),
			"{x3}.\n"
			"x4 :- 2 {x1, x2, x5}.\n"
			"x5 :- x4, x3.\n"
			"x4 :- x5, x3.\n"
			"x1 :- not x3.\n"
			"x2 :- not x3.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		attachUfs();

		solver().assume(lp.getLiteral(3));
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(true, propagateUfs());
		CPPUNIT_ASSERT(solver().numVars() == solver().numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, solver().isFalse(lp.getLiteral(4)));
		CPPUNIT_ASSERT_EQUAL(true, solver().isFalse(lp.getLiteral(5)));

		solver().backtrack();
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(true, propagateUfs());
		CPPUNIT_ASSERT(solver().numVars() == solver().numAssignedVars());
		CPPUNIT_ASSERT_EQUAL(true, solver().isTrue(lp.getLiteral(4)));
		CPPUNIT_ASSERT_EQUAL(true, solver().isFalse(lp.getLiteral(5)));
	}

	void testDependentExtReason() {
		lpAdd(lp.start(ctx, LogicProgram::AspOptions().noEq()),
			"{x3, x4, x5}.\n"
			"x1 :- not x4.\n"
			"x1 :- 2 {x1, x2, x3}.\n"
			"x1 :- x2, x3.\n"
			"x2 :- x1, x5.");

		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		attachUfs();

		// assume ~B1, where B1 = 2 {x1, x2, x3}
		const Asp::PrgDepGraph::AtomNode& a = ufs->graph()->getAtom(lp.getAtom(1)->id());
		Literal x1 = ufs->graph()->getBody(a.body(1)).lit;

		solver().assume(~x1);
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()) && propagateUfs());
		CPPUNIT_ASSERT_EQUAL(value_free, solver().value(lp.getLiteral(1).var()));
		CPPUNIT_ASSERT_EQUAL(value_free, solver().value(lp.getLiteral(2).var()));
		// B1
		CPPUNIT_ASSERT_EQUAL(1u, solver().numAssignedVars());

		// assume x4
		solver().assume(lp.getLiteral(4));
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		// B1 + x4 (hence {not x4})
		CPPUNIT_ASSERT_EQUAL(2u, solver().numAssignedVars());

		// U = {x1, x2}.
		CPPUNIT_ASSERT_EQUAL(true, propagateUfs());
		CPPUNIT_ASSERT_EQUAL(true, solver().isFalse(lp.getLiteral(1)));
		CPPUNIT_ASSERT_EQUAL(true, solver().isFalse(lp.getLiteral(2)));
		Literal extBody = ufs->graph()->getBody(a.body(0)).lit;
		LitVec r;
		solver().reason(~lp.getLiteral(1), r);
		CPPUNIT_ASSERT(r.size() == 1u && r[0] == ~extBody);
	}

	void testEqBodyDiffType() {
		lpAdd(lp.start(ctx),
			"{x1; x4; x5}.\n"
			"{x2} :- x1.\n"
			"x3 :- x1.\n"
			"x2 :- x3, x4.\n"
			"x3 :- x2, x5.");
		lp.endProgram();
		CPPUNIT_ASSERT(lp.stats.sccs == 1);
		attachUfs();

		solver().assume(~lp.getLiteral(1));
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(true, propagateUfs());
		CPPUNIT_ASSERT_EQUAL(true, solver().isFalse(lp.getLiteral(2)));
		CPPUNIT_ASSERT_EQUAL(true, solver().isFalse(lp.getLiteral(3)));
	}

	void testChoiceCardInterplay() {
		lpAdd(lp.start(ctx, LogicProgram::AspOptions().noEq()),
			"{x4}.\n"
			"{x1} :- x4.\n"
			"x2 :- 1 {x1, x3}.\n"
			"x3 :- x2.\n"
			"{x1} :- x3.");
		lp.endProgram();
		CPPUNIT_ASSERT(lp.stats.sccs == 1);
		attachUfs();

		solver().assume(~lp.getLiteral(1));
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
		CPPUNIT_ASSERT_EQUAL(true, propagateUfs());
		CPPUNIT_ASSERT_EQUAL(true, solver().isFalse(lp.getLiteral(2)));
		CPPUNIT_ASSERT_EQUAL(true, solver().isFalse(lp.getLiteral(3)));
	}

	void testCardInterplayOnBT() {
		lpAdd(lp.start(ctx, LogicProgram::AspOptions().noEq()),
			"{x1;x5}.\n"
			"x2 :- 1 {x1, x3}.\n"
			"x2 :- x4.\n"
			"x4 :- x2.\n"
			"x4 :- x5.\n"
			"x3 :- x2, x4.");
		lp.endProgram();
		CPPUNIT_ASSERT(lp.stats.sccs == 1);
		attachUfs();

		solver().assume(~lp.getLiteral(1));
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()) && propagateUfs());
		CPPUNIT_ASSERT_EQUAL(false, solver().isFalse(lp.getLiteral(2)));
		CPPUNIT_ASSERT_EQUAL(false, solver().isFalse(lp.getLiteral(3)));
		solver().undoUntil(0);

		solver().assume(~lp.getLiteral(5));
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()) && propagateUfs());
		CPPUNIT_ASSERT_EQUAL(false, solver().isFalse(lp.getLiteral(2)));
		CPPUNIT_ASSERT_EQUAL(false, solver().isFalse(lp.getLiteral(3)));
	}

	void testInitNoSource() {
		lpAdd(lp.start(ctx, LogicProgram::AspOptions().noEq()),
			"{x3}.\n"
			"{x1;x2} :- x3.\n"
			"x1 :- x2.\n"
			"x2 :- x1.\n");
		lp.endProgram();
		CPPUNIT_ASSERT(lp.stats.sccs == 1);

		solver().force(~lp.getLiteral(3));
		attachUfs();
		CPPUNIT_ASSERT(solver().isFalse(lp.getLiteral(1)));
	}

	void testIncrementalUfs() {
		lp.start(ctx, LogicProgram::AspOptions().noEq());
		lp.updateProgram();
		lpAdd(lp,
			"% I1:\n"
			"x1 :- not x2.\n"
			"x2 :- not x1.\n"
			"#external x3.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.sccGraph.get() == 0);
		lp.updateProgram();
		lpAdd(lp,
			"% I2:\n"
			"{x3;x6}.\n"
			"x4 :- not x3.\n"
			"x4 :- x5, x6.\n"
			"x5 :- x4, x6.\n"
			"#external x3. [release]");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(6u == ctx.sccGraph.get()->nodes());
		CPPUNIT_ASSERT(1 == lp.stats.sccs);
		attachUfs();
		CPPUNIT_ASSERT(6u == ufs->nodes());

		lp.updateProgram();
		lpAdd(lp,
			"% I3:\n"
			"x7 :- x4, not x9.\n"
			"x9 :- not x7.\n"
			"x7 :- x8.\n"
			"x8 :- x7, not x6.\n");

		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(11u == ctx.sccGraph.get()->nodes());
		CPPUNIT_ASSERT(1 == lp.stats.sccs);
		ctx.endInit();
		CPPUNIT_ASSERT(11u == ufs->nodes());
		CPPUNIT_ASSERT(lp.getAtom(7)->scc() != lp.getAtom(4)->scc());
	}

	void testInitialStopConflict() {
		lpAdd(lp.start(ctx),
			"{x3;x4}.\n"
			"x1 :- x3, x4.\n"
			"x1 :- x2, x4.\n"
			"x2 :- x1, x4.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(lp.stats.sccs == 1);
		struct M : PostPropagator {
			uint32 priority() const { return priority_reserved_msg; }
			bool propagateFixpoint(Solver& s, PostPropagator*) {
				s.setStopConflict();
				return false;
			}
		} m;
		solver().addPost(&m);
		ctx.addUnary(~lp.getLiteral(3));
		attachUfs();
		CPPUNIT_ASSERT(solver().hasStopConflict());
		solver().removePost(&m);
		solver().popRootLevel();
		solver().propagate();
		CPPUNIT_ASSERT(solver().isFalse(lp.getLiteral(3)));
		CPPUNIT_ASSERT(solver().isFalse(lp.getLiteral(1)) && solver().isFalse(lp.getLiteral(2)));
	}

	void testIncrementalLearnFact() {
		lp.start(ctx);
		lp.update();
		lpAdd(lp,
			"{x3;x4}.\n"
			"x1 :- x3, x4.\n"
			"x1 :- x2, x4.\n"
			"x2 :- x1, x4.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		attachUfs();
		lp.update();
		lp.endProgram();
		ctx.addUnary(~lp.getLiteral(3));
		CPPUNIT_ASSERT(solver().propagate());
		CPPUNIT_ASSERT(ctx.endInit());
		CPPUNIT_ASSERT(solver().isFalse(lp.getLiteral(3)));
		CPPUNIT_ASSERT(solver().isFalse(lp.getLiteral(1)) && solver().isFalse(lp.getLiteral(2)));
	}

	void testDetachRemovesWatches() {
		lpAdd(lp.start(ctx, LogicProgram::AspOptions().noEq()),
			"{x3;x4;x5}.\n"
			"x1 :- x4.\n"
			"x1 :- 2 {x1, x2, x3}.\n"
			"x1 :- x2, x3.\n"
			"x2 :- x1, x5.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		ctx.endInit();
		uint32 numW = 0;
		for (uint32 i = 1; i <= solver().numVars(); ++i) {
			numW += solver().numWatches(posLit(i));
			numW += solver().numWatches(negLit(i));
		}
		ufs = new DefaultUnfoundedCheck(*ctx.sccGraph);
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
		lpAdd(lp.start(ctx),
			"a | b.\n"
			"c | d.\n"
			"c | e :- b.\n"
			"b | d :- c.\n"
			"c :- d, not b.\n"
			"c :- e.\n"
			"d :- e, not a.\n"
			"e :- c, d.");
		lp.endProgram();
		CPPUNIT_ASSERT(lp.stats.sccs == 1);
		CPPUNIT_ASSERT(lp.getAtom(1)->scc() == PrgNode::noScc);
		CPPUNIT_ASSERT(5u == ctx.sccGraph.get()->numAtoms());
		CPPUNIT_ASSERT(8u == ctx.sccGraph.get()->numBodies());
		attachUfs();
		CPPUNIT_ASSERT_EQUAL(true, solver().assume(lp.getLiteral(2)) && solver().propagate());
		solver().assume(lp.getLiteral(3));
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));

		CPPUNIT_ASSERT(solver().value(lp.getLiteral(4).var()) == value_free);
		CPPUNIT_ASSERT_EQUAL(true, propagateUfs());

		CPPUNIT_ASSERT(solver().isFalse(lp.getLiteral(4)) || "TODO: Implement approx. ufs!");
	}

	void testWeightReason() {
		lpAdd(lp.start(ctx),
			"{x4;x5;x6;x7}.\n"
			"x1 :- 2 {x2, x3 = 2, not x4}.\n"
			"x2 :- x1, x5.\n"
			"x3 :- x2, x6.\n"
			"x3 :- x7.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(lp.stats.sccs == 1);
		attachUfs();
		ufs->setReasonStrategy(DefaultUnfoundedCheck::only_reason);
		ctx.master()->assume(~lp.getLiteral(7)) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(3)));
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(1)));
		ctx.master()->undoUntil(0);

		ctx.master()->assume(lp.getLiteral(4)) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->value(lp.getLiteral(1).var()) == value_free);
		ctx.master()->assume(lp.getLiteral(5)) && ctx.master()->propagate();
		ctx.master()->assume(lp.getLiteral(6)) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->numAssignedVars() == 3);
		ctx.master()->assume(~lp.getLiteral(7)) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(1)));
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(2)));
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(3)));

		LitVec reason;
		ctx.master()->reason(~lp.getLiteral(3), reason);
		CPPUNIT_ASSERT(std::find(reason.begin(), reason.end(), ~lp.getLiteral(7)) != reason.end());
		CPPUNIT_ASSERT(reason.size() == 1);
	}

	void testCardExtSet() {
		lpAdd(lp.start(ctx),
			"{x4; x5; x6; x7; x8}.\n"
			"c :- 2 {a, b, x4, x5}.\n"
			"a :- c,x6.\n"
			"b :- a,x7.\n"
			"a :- x8.\n");
		Var a = 1, b = 2, c = 3, x4 = 4, x5 = 5, x6 = 6, x7 = 7, x8 = 8;
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(lp.stats.sccs == 1);
		attachUfs();
		ufs->setReasonStrategy(DefaultUnfoundedCheck::only_reason);
		Solver& solver = *ctx.master();
		solver.undoUntil(0);
		solver.assume(~lp.getLiteral(x4)) && solver.propagate();
		solver.assume(~lp.getLiteral(x8)) && solver.propagate();
		CPPUNIT_ASSERT(solver.isFalse(lp.getLiteral(a)));
		CPPUNIT_ASSERT(solver.isFalse(lp.getLiteral(b)));
		CPPUNIT_ASSERT(solver.isFalse(lp.getLiteral(c)));

		solver.undoUntil(0);
		solver.assume(~lp.getLiteral(x5)) && solver.propagate();
		solver.assume(~lp.getLiteral(x8)) && solver.propagate();
		CPPUNIT_ASSERT(solver.isFalse(lp.getLiteral(a)));
		CPPUNIT_ASSERT(solver.isFalse(lp.getLiteral(b)));
		CPPUNIT_ASSERT(solver.isFalse(lp.getLiteral(c)));

		solver.undoUntil(0);
		solver.assume(~lp.getLiteral(x4)) && solver.propagate();
		solver.assume(~lp.getLiteral(x5)) && solver.propagate();
		CPPUNIT_ASSERT(solver.numAssignedVars() == 2);

		solver.assume(lp.getLiteral(x6)) && solver.propagate();
		solver.assume(lp.getLiteral(x7)) && solver.propagate();
		CPPUNIT_ASSERT(solver.numAssignedVars() == 4);

		ctx.master()->assume(~lp.getLiteral(x8)) && ctx.master()->propagate();
		CPPUNIT_ASSERT(solver.isFalse(lp.getLiteral(a)));
		CPPUNIT_ASSERT(solver.isFalse(lp.getLiteral(b)));
		CPPUNIT_ASSERT(solver.isFalse(lp.getLiteral(c)));

		LitVec reason;
		ctx.master()->reason(~lp.getLiteral(a), reason);
		bool hasP = std::find(reason.begin(), reason.end(), ~lp.getLiteral(x4)) != reason.end();
		bool hasQ = std::find(reason.begin(), reason.end(), ~lp.getLiteral(x5)) != reason.end();
		bool hasT = std::find(reason.begin(), reason.end(), ~lp.getLiteral(x8)) != reason.end();
		CPPUNIT_ASSERT((hasP ^ hasQ) == true && hasT);
	}

	void testCardNoSimp() {
		lpAdd(lp.start(ctx),
			"b :- 2 {a, c, d, not a}.\n"
			"a :-b.\n"
			"a :- x5.\n"
			"{c;d;x5}.");
		Var a = 1, d = 4, x5 = 5;
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(lp.stats.sccs == 1);
		attachUfs();

		ufs->setReasonStrategy(DefaultUnfoundedCheck::only_reason);
		Solver& solver = *ctx.master();

		solver.assume(~lp.getLiteral(d)) && solver.propagate();
		solver.assume(lp.getLiteral(a)) && solver.propagate();

		CPPUNIT_ASSERT(solver.assume(~lp.getLiteral(x5)) && solver.propagateUntil(ufs.get()));
		CPPUNIT_ASSERT(!propagateUfs());
		solver.resolveConflict();
		CPPUNIT_ASSERT(solver.isTrue(lp.getLiteral(x5)));
		LitVec r;
		solver.reason(lp.getLiteral(x5), r);
		CPPUNIT_ASSERT(r.size() == 2);
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), ~lp.getLiteral(d)) != r.end());
		CPPUNIT_ASSERT(std::find(r.begin(), r.end(), lp.getLiteral(a)) != r.end());
	}
private:
	SharedContext ctx;
	SingleOwnerPtr<DefaultUnfoundedCheck> ufs;
	LogicProgram lp;
	LitVec index;
	void attachUfs() {
		if (ctx.sccGraph.get()) {
			ufs = new DefaultUnfoundedCheck(*ctx.sccGraph);
			solver().addPost(ufs.release());
		}
		ctx.endInit();
	}
	void setupSimpleProgram() {
		lpAdd(lp.start(ctx),
			"{x5;x6;x7;x3}.\n"
			"x2 :- x1.\n"
			"x1 :- x2, x4.\n"
			"x4 :- x1, x3.\n"
			"x1 :- not x5.\n"
			"x2 :- not x7.\n"
			"x4 :- not x6.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		index.assign(1, lit_true());
		for (Var v = 1; v <= lp.numAtoms(); ++v) {
			index.push_back(lp.getLiteral(v));
		}
		attachUfs();
		CPPUNIT_ASSERT_EQUAL(true, solver().propagateUntil(ufs.get()));
	}
};
CPPUNIT_TEST_SUITE_REGISTRATION(UnfoundedCheckTest);
} }
