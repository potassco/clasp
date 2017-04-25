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
#include <clasp/solver.h>
#include <clasp/minimize_constraint.h>
#include <clasp/unfounded_check.h>
#include <potassco/theory_data.h>
#include <sstream>
using namespace std;
namespace Clasp { namespace Test {
using namespace Clasp::Asp;
struct ClauseObserver : public DecisionHeuristic {
	Literal doSelect(Solver&){return Literal();}
	void updateVar(const Solver&, Var, uint32) {}
	void newConstraint(const Solver&, const Literal* first, LitVec::size_type size, ConstraintType) {
		Clause c;
		for (LitVec::size_type i = 0; i < size; ++i, ++first) {
			c.push_back(*first);
		}
		std::sort(c.begin(), c.end());
		clauses_.push_back(c);
	}
	typedef std::vector<Literal> Clause;
	typedef std::vector<Clause> Clauses;
	Clauses clauses_;
};

class LogicProgramTest : public CppUnit::TestFixture {
  CPPUNIT_TEST_SUITE(LogicProgramTest);
	CPPUNIT_TEST(testInvalidNodeId);
	CPPUNIT_TEST(testMergeValue);
	CPPUNIT_TEST(testIgnoreRules);
	CPPUNIT_TEST(testDuplicateRule);
	CPPUNIT_TEST(testNotAChoice);
	CPPUNIT_TEST(testNotAChoiceMerge);
	CPPUNIT_TEST(testMergeToSelfblocker);
	CPPUNIT_TEST(testMergeToSelfblocker2);
	CPPUNIT_TEST(testMergeToSelfblocker3);
	CPPUNIT_TEST(testDerivedTAUT);
	CPPUNIT_TEST(testOneLoop);
	CPPUNIT_TEST(testZeroLoop);
	CPPUNIT_TEST(testEqSuccs);
	CPPUNIT_TEST(testEqCompute);
	CPPUNIT_TEST(testFactsAreAsserted);
	CPPUNIT_TEST(testSelfblockersAreAsserted);
	CPPUNIT_TEST(testConstraintsAreAsserted);
	CPPUNIT_TEST(testConflictingCompute);
	CPPUNIT_TEST(testForceUnsuppAtomFails);
	CPPUNIT_TEST(testTrivialConflictsAreDeteced);
	CPPUNIT_TEST(testBuildEmpty);
	CPPUNIT_TEST(testBuildUnsat);
	CPPUNIT_TEST(testAddOneFact);
	CPPUNIT_TEST(testTwoFactsOnlyOneVar);
	CPPUNIT_TEST(testDontAddOnePredsThatAreNotHeads);
	CPPUNIT_TEST(testDontAddDuplicateBodies);
	CPPUNIT_TEST(testDontAddDuplicateSumBodies);
	CPPUNIT_TEST(testAddLargeSumBody);
	CPPUNIT_TEST(testDontAddDuplicateSimpBodies);
	CPPUNIT_TEST(testDontAddUnsupported);
	CPPUNIT_TEST(testDontAddUnsupportedNoEq);
	CPPUNIT_TEST(testDontAddUnsupportedExtNoEq);
	CPPUNIT_TEST(testAssertSelfblockers);

	CPPUNIT_TEST(testRegressionR1);
	CPPUNIT_TEST(testRegressionR2);
	CPPUNIT_TEST(testFuzzBug);
	CPPUNIT_TEST(testBackpropNoEqBug);

	CPPUNIT_TEST(testCloneProgram);

	CPPUNIT_TEST(testBug);
	CPPUNIT_TEST(testSatBodyBug);
	CPPUNIT_TEST(testDepBodyBug);
	CPPUNIT_TEST(testAddUnknownAtomToMinimize);
	CPPUNIT_TEST(testWriteWeakTrue);
	CPPUNIT_TEST(testSimplifyBodyEqBug);
	CPPUNIT_TEST(testNoEqSameLitBug);

	CPPUNIT_TEST(testAssertEqSelfblocker);
	CPPUNIT_TEST(testAddClauses);
	CPPUNIT_TEST(testAddCardConstraint);
	CPPUNIT_TEST(testAddWeightConstraint);
	CPPUNIT_TEST(testAddMinimizeConstraint);
	CPPUNIT_TEST(testAddEmptyMinimizeConstraint);
	CPPUNIT_TEST(testNonTight);

	CPPUNIT_TEST(testIgnoreCondFactsInLoops);
	CPPUNIT_TEST(testCrEqBug);
	CPPUNIT_TEST(testEqOverChoiceRule);
	CPPUNIT_TEST(testEqOverBodiesOfDiffType);
	CPPUNIT_TEST(testEqOverComp);
	CPPUNIT_TEST(testNoBodyUnification);
	CPPUNIT_TEST(testNoEqAtomReplacement);
	CPPUNIT_TEST(testAllBodiesSameLit);
	CPPUNIT_TEST(testAllBodiesSameLit2);

	CPPUNIT_TEST(testCompLit);
	CPPUNIT_TEST(testFunnySelfblockerOverEqByTwo);

	CPPUNIT_TEST(testRemoveKnownAtomFromWeightRule);
	CPPUNIT_TEST(testMergeEquivalentAtomsInConstraintRule);
	CPPUNIT_TEST(testMergeEquivalentAtomsInWeightRule);
	CPPUNIT_TEST(testBothLitsInConstraintRule);
	CPPUNIT_TEST(testBothLitsInWeightRule);
	CPPUNIT_TEST(testWeightlessAtomsInWeightRule);
	CPPUNIT_TEST(testSimplifyToNormal);
	CPPUNIT_TEST(testSimplifyToCardBug);
	CPPUNIT_TEST(testSimplifyCompBug);
	CPPUNIT_TEST(testSimplifyToTrue);

	CPPUNIT_TEST(testBPWeight);

	CPPUNIT_TEST(testExtLitsAreFrozen);
	CPPUNIT_TEST(writeIntegrityConstraint);
	CPPUNIT_TEST(testComputeTrueBug);
	CPPUNIT_TEST(testBackprop);
	CPPUNIT_TEST(testBackpropTrueCon);
	CPPUNIT_TEST(testBackpropWrite);
	CPPUNIT_TEST(testStatisticsObject);

	CPPUNIT_TEST(testSimpleIncremental);
	CPPUNIT_TEST(testIncrementalDistinctFacts);
	CPPUNIT_TEST(testIncrementalDistinctFactsSimple);
	CPPUNIT_TEST(testIncrementalFreeze);
	CPPUNIT_TEST(testIncrementalFreezeValue);
	CPPUNIT_TEST(testIncrementalFreezeOpen);
	CPPUNIT_TEST(testIncrementalKeepFrozen);
	CPPUNIT_TEST(testIncrementalFreezeCompute);
	CPPUNIT_TEST(testIncrementalUnfreezeUnsupp);
	CPPUNIT_TEST(testIncrementalUnfreezeCompute);
	CPPUNIT_TEST(testIncrementalCompute);
	CPPUNIT_TEST(testIncrementalComputeBackprop);
	CPPUNIT_TEST(testIncrementalBackpropStep);
	CPPUNIT_TEST(testIncrementalEq);
	CPPUNIT_TEST(testIncrementalEqUnfreeze);
	CPPUNIT_TEST(testIncrementalEqComplement);
	CPPUNIT_TEST(testIncrementalEqUpdateAssigned);
	CPPUNIT_TEST(testIncrementalEqResetState);
	CPPUNIT_TEST(testIncrementalUnfreezeUnsuppEq);
	CPPUNIT_TEST(testIncrementalUnfreezeEq);
	CPPUNIT_TEST(testIncrementalStats);
	CPPUNIT_TEST(testIncrementalTransform);
	CPPUNIT_TEST(testIncrementalBackpropCompute);
	CPPUNIT_TEST(testIncrementalFreezeUnfreeze);
	CPPUNIT_TEST(testIncrementalSymbolUpdate);
	CPPUNIT_TEST(testIncrementalBackpropSolver);
	CPPUNIT_TEST(testIncrementalFreezeDefined);
	CPPUNIT_TEST(testIncrementalUnfreezeDefined);
	CPPUNIT_TEST(testIncrementalUnfreezeAsFact);
	CPPUNIT_TEST(testIncrementalImplicitUnfreeze);
	CPPUNIT_TEST(testIncrementalRedefine);
	CPPUNIT_TEST(testIncrementalGetAssumptions);
	CPPUNIT_TEST(testIncrementalSimplifyCard);
	CPPUNIT_TEST(testIncrementalSimplifyMinimize);
	CPPUNIT_TEST(testIncrementalEqOverNeg);

	CPPUNIT_TEST(testIncrementalKeepExternalValue);
	CPPUNIT_TEST(testIncrementalWriteMinimize);
	CPPUNIT_TEST(testIncrementalWriteExternal);
	CPPUNIT_TEST(testIncrementalWriteUnfreeze);
	CPPUNIT_TEST(testIncrementalSetInputAtoms);

	CPPUNIT_TEST(testFreezeIsExternal);
	CPPUNIT_TEST(testUnfreezeIsNotExternal);
	CPPUNIT_TEST(testFreezeStaysExternal);
	CPPUNIT_TEST(testDefinedIsNotExternal);
	CPPUNIT_TEST(testFactIsNotExternal);
	CPPUNIT_TEST(testFactIsDefined);
	CPPUNIT_TEST(testBogusAtomIsNotDefined);
	CPPUNIT_TEST(testMakeAtomicCondition);
	CPPUNIT_TEST(testMakeComplexCondition);
	CPPUNIT_TEST(testMakeFalseCondition);
	CPPUNIT_TEST(testMakeInvalidCondition);
	CPPUNIT_TEST(testExtractCondition);
	CPPUNIT_TEST(testGetConditionAfterDispose);
	CPPUNIT_TEST(testAssumptionsAreVolatile);
	CPPUNIT_TEST(testProjectionIsExplicitAndCumulative);

	CPPUNIT_TEST(testTheoryAtomsAreFrozen);
	CPPUNIT_TEST(testTheoryAtomsAreFrozenIncremental);
	CPPUNIT_TEST(testAcceptIgnoresAuxChoicesFromTheoryAtoms);
	CPPUNIT_TEST(testFalseHeadTheoryAtomsAreRemoved);
	CPPUNIT_TEST(testFalseBodyTheoryAtomsAreKept);
	CPPUNIT_TEST(testFactTheoryAtomsAreNotExternal);
	CPPUNIT_TEST(testTheoryAtomsAreAdded);

	CPPUNIT_TEST(testOutputFactsNotSupportedInSmodels);

	CPPUNIT_TEST(testDisposeBug);
	CPPUNIT_TEST_SUITE_END();
public:
	void setUp() {
		a = 1, b = 2, c = 3, d = 4, e = 5, f = 6;
	}
	void tearDown(){
		ctx.reset();
	}
	void testInvalidNodeId() {
		CPPUNIT_ASSERT_THROW(PrgNode(PrgNode::noNode + 1), std::overflow_error);
	}
	void testMergeValue() {
		PrgAtom lhs(0), rhs(1);
		ValueRep ok[15] = {
			value_free, value_free, value_free,
			value_free, value_true, value_true,
			value_free, value_false, value_false,
			value_free, value_weak_true, value_weak_true,
			value_true, value_weak_true, value_true
		};
		ValueRep fail[4] = { value_true, value_false, value_weak_true, value_false };
		for (uint32 x = 0; x != 2; ++x) {
			for (uint32 i = 0; i != 15; i += 3) {
				lhs.clearLiteral(true);
				rhs.clearLiteral(true);
				CPPUNIT_ASSERT(lhs.assignValue(ok[i+x]));
				CPPUNIT_ASSERT(rhs.assignValue(ok[i+(!x)]));
				CPPUNIT_ASSERT(mergeValue(&lhs, &rhs));
				CPPUNIT_ASSERT(lhs.value() == ok[i+2] && rhs.value() == ok[i+2]);
			}
		}
		for (uint32 x = 0; x != 2; ++x) {
			for (uint32 i = 0; i != 4; i+=2) {
				lhs.clearLiteral(true);
				rhs.clearLiteral(true);
				CPPUNIT_ASSERT(lhs.assignValue(fail[i+x]));
				CPPUNIT_ASSERT(rhs.assignValue(fail[i+(!x)]));
				CPPUNIT_ASSERT(!mergeValue(&lhs, &rhs));
			}
		}
	}
	void testIgnoreRules() {
		lpAdd(lp.start(ctx), "a :- a. b :- a.\n");
		CPPUNIT_ASSERT_EQUAL(1u, lp.stats.rules[0].sum());
	}

	void testDuplicateRule() {
		lpAdd(lp.start(ctx, LogicProgram::AspOptions().iterations(1)),
			"{b}.\n"
			"a :- b.\n"
			"a :- b.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(lp.getLiteral(a) == lp.getLiteral(b));
	}

	void testNotAChoice() {
		lpAdd(lp.start(ctx),
			"{b}.\n"
			"{a} :- not b."
			"a :-not b.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		ctx.master()->assume(~lp.getLiteral(b)) && ctx.master()->propagate();
		// if b is false, a must be true because a :- not b. is stronger than {a} :- not b.
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isTrue(lp.getLiteral(a)));
	}

	void testNotAChoiceMerge() {
		lpAdd(lp.start(ctx),
			"{b}.\n"
			"{a} :- b.\n"
			"a :- b, not c.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(lp.getLiteral(a) == lp.getLiteral(b));
	}

	void testMergeToSelfblocker() {
		lpAdd(lp.start(ctx),
			"a :- not b.\n"
			"b :- a.\n");
		CPPUNIT_ASSERT_EQUAL(false, lp.endProgram() && ctx.endInit());
	}

	void testMergeToSelfblocker2() {
		lpAdd(lp.start(ctx),
			"a :- not d.\n"
			"a :- not c.\n"
			"b :- not c.\n"
			"c :- a.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isTrue(lp.getLiteral(a)));
		CPPUNIT_ASSERT(ctx.numVars() == 0);
	}
	void testMergeToSelfblocker3() {
		lpAdd(lp.start(ctx),
			"b :- a.\n"
			"{c}.\n"
			"d :- 2 {a, b}.\n"
			"e :- 2 {a}.\n"
			"a :- not d, not e.\n");
		CPPUNIT_ASSERT_EQUAL(false, lp.endProgram());
	}

	void testDerivedTAUT() {
		lpAdd(lp.start(ctx),
			"{x1;x2}.\n"
			"x3 :- not x2.\n"
			"x4 :- x3.\n"
			"x3 :- x1, x4.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.numVars() == 2);
	}

	void testOneLoop() {
		lpAdd(lp.start(ctx),
			"a :- not b.\n"
			"b :- not a.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL( 1u, ctx.numVars() );
		CPPUNIT_ASSERT_EQUAL( 0u, ctx.numConstraints() );
		CPPUNIT_ASSERT( lp.getLiteral(a) == ~lp.getLiteral(b) );
	}

	void testZeroLoop() {
		lpAdd(lp.start(ctx),
			"a :- b.\n"
			"b :- a.\n"
			"a :- not c.\n"
			"c :- not a.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL( 1u, ctx.numVars() );
		CPPUNIT_ASSERT_EQUAL( 0u, ctx.numConstraints() );
		CPPUNIT_ASSERT( lp.getLiteral(a) == lp.getLiteral(b) );
	}

	void testEqSuccs() {
		lpAdd(lp.start(ctx),
			"{a;b}.\n"
			"c :- a, b.\n"
			"d :- a, b.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL( 3u, ctx.numVars() );
		CPPUNIT_ASSERT_EQUAL( 3u, ctx.numConstraints() );
		CPPUNIT_ASSERT( lp.getLiteral(c) == lp.getLiteral(d) );
	}

	void testEqCompute() {
		lpAdd(lp.start(ctx),
			"{c}.\n"
			"a :- not c.\n"
			"a :- b.\n"
			"b :- a.\n"
			"  :- not b.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isTrue(lp.getLiteral(a)));
		CPPUNIT_ASSERT_EQUAL(lp.getLiteral(a), lp.getLiteral(b));
		CPPUNIT_ASSERT_EQUAL(true, lp.isFact(a));
		CPPUNIT_ASSERT_EQUAL(true, lp.isFact(b));
	}

	void testFactsAreAsserted() {
		lpAdd(lp.start(ctx),
			"a :- not b.\n"
			"c.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isTrue(lp.getLiteral(a)));
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isTrue(lp.getLiteral(c)));
	}
	void testSelfblockersAreAsserted() {
		lpAdd(lp.start(ctx),
			"x1 :- not x1.\n"
			"x2 :- not x1.\n");
		CPPUNIT_ASSERT_EQUAL(false, lp.endProgram() && ctx.endInit());
	}
	void testConstraintsAreAsserted() {
		lpAdd(lp.start(ctx),
			"a :- not b.\n"
			"b :- not a.\n"
			"  :- a.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isFalse(lp.getLiteral(a)));
	}

	void testConflictingCompute() {
		lpAdd(lp.start(ctx),
			"  :- a.\n"
			"  :- not a.");
		CPPUNIT_ASSERT_EQUAL(false, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(!ctx.ok());
	}
	void testForceUnsuppAtomFails() {
		lpAdd(lp.start(ctx), "a :- not b. :- not b.");
		CPPUNIT_ASSERT_EQUAL(false, lp.endProgram() && ctx.endInit());
	}

	void testTrivialConflictsAreDeteced() {
		lpAdd(lp.start(ctx), "a :- not a. :- not a.");
		CPPUNIT_ASSERT_EQUAL(false, lp.endProgram() && ctx.endInit());

	}
	void testBuildEmpty() {
		lp.start(ctx);
		lp.endProgram();
		CPPUNIT_ASSERT_EQUAL(0u, ctx.numVars());
		CPPUNIT_ASSERT_EQUAL(0u, ctx.numConstraints());
	}
	void testBuildUnsat() {
		lpAdd(lp.start(ctx), "x1. :- x1.");
		CPPUNIT_ASSERT_EQUAL(false, lp.endProgram());
		std::stringstream exp("1 2 0 0\n0\n0\nB+\n0\nB-\n2\n0\n1\n");
		CPPUNIT_ASSERT_EQUAL(true, compareSmodels(exp, lp));
	}
	void testAddOneFact() {
		lpAdd(lp.start(ctx), "a.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT_EQUAL(0u, ctx.numVars());
		// a fact does not introduce a constraint, it is just a top-level assignment
		CPPUNIT_ASSERT_EQUAL(0u, ctx.numConstraints());
		CPPUNIT_ASSERT_EQUAL(true, lp.isFact(a));
	}

	void testTwoFactsOnlyOneVar() {
		lpAdd(lp.start(ctx), "a. b.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT_EQUAL(0u, ctx.numVars());
		CPPUNIT_ASSERT_EQUAL(0u, ctx.numConstraints());
		CPPUNIT_ASSERT_EQUAL(true, lp.isFact(a));
		CPPUNIT_ASSERT_EQUAL(true, lp.isFact(b));
	}

	void testDontAddOnePredsThatAreNotHeads() {
		lpAdd(lp.start(ctx),
			"x1 :-not x2, not x3.\n"
			"x3.\n"
			"#output a : x1.\n"
			"#output b : x2.\n"
			"#output c : x3.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT_EQUAL(0u, ctx.numVars());
		std::stringstream exp("1 3 0 0 \n0\n3 c\n0\nB+\n0\nB-\n0\n1\n");
		CPPUNIT_ASSERT(compareSmodels(exp, lp));
	}

	void testDontAddDuplicateBodies() {
		lpAdd(lp.start(ctx),
			"a :- b, not c.\n"
			"d :- b, not c.\n"
			"b. c.");
		lp.addOutput("a", a).addOutput("b", b).addOutput("c", c);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT_EQUAL(0u, ctx.numVars());
		std::stringstream exp("1 2 0 0 \n1 3 0 0 \n0\n2 b\n3 c\n0\nB+\n0\nB-\n0\n1\n");
		CPPUNIT_ASSERT(compareSmodels(exp, lp));
	}

	void testDontAddDuplicateSumBodies() {
		lpAdd(lp.start(ctx),
			"{a; b; c}.\n"
			"d :- 2 {a=1, b=2, not c=1}.\n"
			"e :- 2 {a=1, b=2, not c=1}.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(lp.numBodies() == 2);
	}

	void testAddLargeSumBody() {
		VarVec atoms;
		Potassco::WLitVec lits;
		lp.start(ctx);
		for (uint32 i = 1; i != 21; ++i) { atoms.push_back(i); }
		lp.addRule(Head_t::Choice, Potassco::toSpan(atoms), Potassco::toSpan<Potassco::Lit_t>());

		atoms.assign(1, 20);
		for (int32 i = 1; i != 20; ++i) {
			Potassco::WeightLit_t wl = {i&1 ? Potassco::lit(i) : Potassco::neg(i), i};
			lits.push_back(wl);
		}
		lp.addRule(Head_t::Disjunctive, Potassco::toSpan(atoms), 10, Potassco::toSpan(lits));
		lits.clear();
		for (int32 i = 20; --i;) {
			Potassco::WeightLit_t wl = {i&1 ? Potassco::lit(i) : Potassco::neg(i), 20 - i};
			lits.push_back(wl);
		}
		lp.addRule(Head_t::Disjunctive, Potassco::toSpan(atoms), 10, Potassco::toSpan(lits));
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(lp.numBodies() == 3u);
	}
	void testDontAddDuplicateSimpBodies() {
		lpAdd(lp.start(ctx),
			"{x1;x2;x3;x4}.\n"
			"x1 :- x2, x3, x4.\n"
			"x1 :- 8 {x3=2, x2=3, x4=4}.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(lp.numBodies() == 2);
	}

	void testDontAddUnsupported() {
		lpAdd(lp.start(ctx),
			"x1 :- x3, x2.\n"
			"x3 :- not x4.\n"
			"x2 :- x1.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		std::stringstream exp("1 3 0 0 \n0");
		CPPUNIT_ASSERT(compareSmodels(exp, lp));
	}

	void testDontAddUnsupportedNoEq() {
		lpAdd(lp.start(ctx, LogicProgram::AspOptions().noEq()),
			"x1 :- x3, x2.\n"
			"x3 :- not x4.\n"
			"x2 :- x1.");
		lp.addOutput("a", a).addOutput("b", b).addOutput("c", c);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(ctx.numVars() <= 2u);
		std::stringstream exp("1 3 0 0 \n0\n3 c\n0\nB+\n0\nB-\n0\n1\n");
		CPPUNIT_ASSERT(compareSmodels(exp, lp));
	}

	void testDontAddUnsupportedExtNoEq() {
		lpAdd(lp.start(ctx, LogicProgram::AspOptions().noEq()),
			"a :- not d.\n"
			"c :- a, d.\n"
			"b :- 2 {a, c, not d}. % -> a\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isFalse(lp.getLiteral(c)));
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isTrue(lp.getLiteral(a)));
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isTrue(lp.getLiteral(b)));
	}

	void testAssertSelfblockers() {
		lpAdd(lp.start(ctx),
			"a :- b, not c.\n"
			"c :- b, not c.\n"
			"b.");
		// Program is unsat because b must be true and false at the same time.
		CPPUNIT_ASSERT_EQUAL(false, lp.endProgram() && ctx.endInit());
	}

	void testRegressionR1() {
		lpAdd(lp.start(ctx), "b. b :- not c.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(lp.getLiteral(b) == lit_true());
		CPPUNIT_ASSERT(lp.getLiteral(c) == lit_false());
		CPPUNIT_ASSERT(ctx.numVars() == 0);
	}

	void testRegressionR2() {
		lpAdd(lp.start(ctx),
			"b :- not c.\n"
			"b :- not d.\n"
			"c :- not b.\n"
			"d :- not b.\n"
			"b.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(lp.getLiteral(b) == lit_true());
		CPPUNIT_ASSERT(lp.getLiteral(c) == lit_false());
		CPPUNIT_ASSERT(lp.getLiteral(d) == lit_false());
		CPPUNIT_ASSERT(ctx.numVars() == 0);
	}
	void testFuzzBug() {
		lpAdd(lp.start(ctx), "x1 :- not x1, not x2, not x3, not x2, not x1, not x4.");
		CPPUNIT_ASSERT_EQUAL(false, lp.endProgram() && ctx.endInit());
	}
	void testBackpropNoEqBug() {
		lpAdd(lp.start(ctx, LogicProgram::AspOptions().noEq().backpropagate()),
			"{x2;x3;x4} :- x5.\n"
			"x1 :- x7, x5.\n"
			"x5.\n"
			"x7 :- x2, x3.\n"
			"x7 :- x6.\n"
			"x6 :- x8.\n"
			"x8 :- x4.\n"
			":- x1.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isFalse(lp.getLiteral(6)));
	}

	void testCloneProgram() {
		lpAdd(lp.start(ctx),
			"{x1;x2;x3}.\n"
			"x4 :- x1, x2, x3.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT( uint32(4) >= ctx.numVars() );
		CPPUNIT_ASSERT( uint32(4) >= ctx.numConstraints() );

		SharedContext ctx2;
		CPPUNIT_ASSERT_EQUAL(true, lp.clone(ctx2) && ctx2.endInit());
		CPPUNIT_ASSERT_EQUAL( ctx.numVars(), ctx2.numVars() );
		CPPUNIT_ASSERT_EQUAL( ctx.numConstraints(), ctx2.numConstraints() );
		CPPUNIT_ASSERT(!ctx.isShared());
		CPPUNIT_ASSERT(!ctx2.isShared());
		CPPUNIT_ASSERT(ctx.output.size() == ctx2.output.size() );
	}

	void testBug() {
		lpAdd(lp.start(ctx),
			"x1 :- x2.\n"
			"x2 :- x3, x1.\n"
			"x3 :- x4.\n"
			"x4 :-not x3.\n");
		CPPUNIT_ASSERT_EQUAL(false, lp.endProgram() && ctx.endInit());
	}

	void testSatBodyBug() {
		lpAdd(lp.start(ctx),
			"{c;b;a}.\n"
			"a.\n"
			"b :- 1 {a, c}.\n"
			"d :- b, c.\n");
		CPPUNIT_ASSERT(std::distance(lp.getAtom(c)->deps_begin(), lp.getAtom(c)->deps_end()) <= 2u);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(std::distance(lp.getAtom(c)->deps_begin(), lp.getAtom(c)->deps_end()) == 1u);
		CPPUNIT_ASSERT(std::distance(lp.getAtom(b)->deps_begin(), lp.getAtom(b)->deps_end()) == 0u);
		CPPUNIT_ASSERT_EQUAL(value_free, ctx.master()->value(lp.getLiteral(c).var()));
	}
	void testDepBodyBug() {
		lpAdd(lp.start(ctx),
			"{d;e;f}.\n"
			"a :- d, e.\n"
			"b :- a."
			"c :- b, f, a.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT((lp.getAtom(a)->deps_end() - lp.getAtom(a)->deps_begin()) == 2);
	}

	void testAddUnknownAtomToMinimize() {
		lpAdd(lp.start(ctx), "#minimize{a}.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(true, lp.hasMinimize());
	}

	void testWriteWeakTrue() {
		lpAdd(lp.start(ctx),
			"{c}.\n"
			"a :- not b, c.\n"
			"b :- not a.\n"
			"  :- not a.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		Var a = lp.falseAtom();
		std::stringstream exp;
		exp << "1 " << a << " 1 1 3\n";
		CPPUNIT_ASSERT(findSmodels(exp, lp));
	}

	void testSimplifyBodyEqBug() {
		lpAdd(lp.start(ctx),
			"{d;e;f}.\n"
			"a :- d,f.\n"
			"b :- d,f.\n"
			"c :- a, e, b.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		PrgAtom* na = lp.getAtom(a);
		PrgAtom* nb = lp.getAtom(b);
		CPPUNIT_ASSERT(nb->eq() && nb->id() == a);
		CPPUNIT_ASSERT((na->deps_end() - na->deps_begin()) == 1);
	}

	void testNoEqSameLitBug() {
		lpAdd(lp.start(ctx, LogicProgram::AspOptions().noEq()),
			"{x4;x5}.\n"
			"x1 :- x4,x5.\n"
			"x2 :- x4,x5.\n"
			"x3 :- x1, x2.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.numVars() == 5);
	}

	void testAssertEqSelfblocker() {
		lpAdd(lp.start(ctx),
			"a :- not b, not c.\n"
			"a :- not d, not e.\n"
			"b :- not c.\n"
			"c :- not b.\n"
			"d :- not e.\n"
			"e :- not d.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(2u, ctx.numVars());
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isFalse(lp.getLiteral(a)));
	}

	void testAddClauses() {
		ClauseObserver o;
		ctx.master()->setHeuristic(&o, Ownership_t::Retain);
		lpAdd(lp.start(ctx),
			"a :- not b.\n"
			"a :- b, c.\n"
			"b :- not a.\n"
			"c :- not b.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(3u, ctx.numVars());
		CPPUNIT_ASSERT_EQUAL(0u, ctx.master()->numAssignedVars());

		CPPUNIT_ASSERT_EQUAL(8u, ctx.numConstraints());

		Var bodyNotB = 1;
		Var bodyBC = 3;
		CPPUNIT_ASSERT_EQUAL(Var_t::Body, ctx.varInfo(3).type());
		Literal litA = lp.getLiteral(a);
		CPPUNIT_ASSERT(lp.getLiteral(b) == ~lp.getLiteral(a));

		// a - HeadClauses
		ClauseObserver::Clause ac;
		ac.push_back(~litA);
		ac.push_back(posLit(bodyNotB));
		ac.push_back(posLit(bodyBC));
		std::sort(ac.begin(), ac.end());
		CPPUNIT_ASSERT(std::find(o.clauses_.begin(), o.clauses_.end(), ac) != o.clauses_.end());

		// bodyNotB - Body clauses
		ClauseObserver::Clause cl;
		cl.push_back(negLit(bodyNotB)); cl.push_back(~lp.getLiteral(b));
		std::sort(cl.begin(), cl.end());
		CPPUNIT_ASSERT(std::find(o.clauses_.begin(), o.clauses_.end(), cl) != o.clauses_.end());
		cl.clear();
		cl.push_back(posLit(bodyNotB)); cl.push_back(lp.getLiteral(b));
		std::sort(cl.begin(), cl.end());
		CPPUNIT_ASSERT(std::find(o.clauses_.begin(), o.clauses_.end(), cl) != o.clauses_.end());
		cl.clear();
		cl.push_back(negLit(bodyNotB)); cl.push_back(litA);
		std::sort(cl.begin(), cl.end());
		CPPUNIT_ASSERT(std::find(o.clauses_.begin(), o.clauses_.end(), cl) != o.clauses_.end());

		// bodyBC - Body clauses
		cl.clear();
		cl.push_back(negLit(bodyBC)); cl.push_back(lp.getLiteral(b));
		std::sort(cl.begin(), cl.end());
		CPPUNIT_ASSERT(std::find(o.clauses_.begin(), o.clauses_.end(), cl) != o.clauses_.end());
		cl.clear();
		cl.push_back(negLit(bodyBC)); cl.push_back(lp.getLiteral(c));
		std::sort(cl.begin(), cl.end());
		CPPUNIT_ASSERT(std::find(o.clauses_.begin(), o.clauses_.end(), cl) != o.clauses_.end());
		cl.clear();
		cl.push_back(posLit(bodyBC)); cl.push_back(~lp.getLiteral(b)); cl.push_back(~lp.getLiteral(c));
		std::sort(cl.begin(), cl.end());
		CPPUNIT_ASSERT(std::find(o.clauses_.begin(), o.clauses_.end(), cl) != o.clauses_.end());
		cl.clear();
		cl.push_back(negLit(bodyBC)); cl.push_back(litA);
		std::sort(cl.begin(), cl.end());
		CPPUNIT_ASSERT(std::find(o.clauses_.begin(), o.clauses_.end(), cl) != o.clauses_.end());
	}

	void testAddCardConstraint() {
		lpAdd(lp.start(ctx),
			"a :- 1 { not b, c, d }.\n"
			"{b;c}.");
		lp.addOutput("a", a).addOutput("b", b).addOutput("c", c);

		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT_EQUAL(3u, ctx.numVars());

		std::stringstream exp("2 1 2 1 1 2 3 \n3 2 2 3 0 0 \n0\n1 a\n2 b\n3 c\n0\nB+\n0\nB-\n0\n1\n");
		CPPUNIT_ASSERT(compareSmodels(exp, lp));
	}

	void testAddWeightConstraint() {
		lpAdd(lp.start(ctx),
			"a :- 2 {not b=1, c=2, d=2}.\n"
			"{b;c}.");
		lp.addOutput("a", a).addOutput("b", b).addOutput("c", c).addOutput("d", d);

		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT_EQUAL(3u, ctx.numVars());
		std::stringstream exp("5 1 2 2 1 2 3 1 2 \n3 2 2 3 0 0 \n0\n1 a\n2 b\n3 c\n0\nB+\n0\nB-\n0\n1\n");
		CPPUNIT_ASSERT(compareSmodels(exp, lp));
	}
	void testAddMinimizeConstraint() {
		lpAdd(lp.start(ctx),
			"a :- not b.\n"
			"b :- not a.\n"
			"#minimize{a}@0.\n"
			"#minimize{b}@1.\n"
			"#output a : a. #output b : b.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		std::stringstream exp;
		exp
			<< "6 0 1 0 1 1 \n"
			<< "6 0 1 0 2 1 \n"
			<< "1 1 1 1 2 \n"
			<< "1 2 1 1 1 \n"
			<< "0\n1 a\n2 b\n0\nB+\n0\nB-\n0\n1\n";
		CPPUNIT_ASSERT(compareSmodels(exp, lp));
	}
	void testAddEmptyMinimizeConstraint() {
		lpAdd(lp.start(ctx), "#minimize{}.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(ctx.hasMinimize());
	}

	void testNonTight() {
		lpAdd(lp.start(ctx),
			"b :- c.\n"
			"c :- b.\n"
			"b :- not a.\n"
			"c :- not a.\n"
			"a :- not b.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT( lp.stats.sccs != 0 );
	}

	void testIgnoreCondFactsInLoops() {
		lpAdd(lp.start(ctx),
			"{a}.\n"
			"b :- a.\n"
			"a :- b.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT( lp.stats.sccs == 0);
	}

	void testCrEqBug() {
		lpAdd(lp.start(ctx),
			"a.\n"
			"{b}.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(1u, ctx.numVars());
		CPPUNIT_ASSERT_EQUAL(value_free, ctx.master()->value(lp.getLiteral(b).var()));
	}

	void testEqOverChoiceRule() {
		lpAdd(lp.start(ctx),
			"{a}.\n"
			"b :- a.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT_EQUAL(1u, ctx.numVars());
		std::stringstream exp;
		exp
			<< "3 1 1 0 0 \n"
			<< "1 2 1 0 1 \n"
			<< "0\n0\nB+\n0\nB-\n0\n1\n";
		CPPUNIT_ASSERT(compareSmodels(exp, lp));
	}

	void testEqOverComp() {
		lpAdd(lp.start(ctx),
			"a :- not b.\n"
			"a :- b.\n"
			"b :- not c.\n"
			"c :- not a.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT_EQUAL(lp.getLiteral(a), lp.getLiteral(b));
		CPPUNIT_ASSERT(ctx.master()->numFreeVars() == 0 && ctx.master()->isTrue(lp.getLiteral(a)));
	}

	void testEqOverBodiesOfDiffType() {
		lpAdd(lp.start(ctx),
			"{a;b}.\n"
			"d :- 2{a, b, c}.\n"
			"c :- d.\n"
			"  :- b.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(3u >= ctx.numVars());
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(b)));
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(c)));
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(d)));
	}

	void testNoBodyUnification() {
		Var g = 7;
		lpAdd(lp.start(ctx),
			"{a;b;c}.\n"
			"d :- a, g.\n"
			"d :- b.\n"
			"e :- not d.\n"
			"f :- not e.\n"
			"g :- d.\n"
			"g :- c.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.sccGraph.get());
		ctx.master()->addPost(new DefaultUnfoundedCheck(*ctx.sccGraph));
		CPPUNIT_ASSERT_EQUAL(true, ctx.endInit());
		ctx.master()->assume(~lp.getLiteral(b));
		ctx.master()->propagate();
		ctx.master()->assume(~lp.getLiteral(c));
		ctx.master()->propagate();
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isFalse(lp.getLiteral(g)));
	}

	void testNoEqAtomReplacement() {
		lpAdd(lp.start(ctx),
			"{a;b}.\n"
			"c :- a.\n"
			"c :- b.\n"
			"d :- not c.\n"
			"e :- not d.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		ctx.master()->assume(~lp.getLiteral(a));
		ctx.master()->propagate();
		ctx.master()->assume(~lp.getLiteral(b));
		ctx.master()->propagate();
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isFalse(lp.getLiteral(c)));
	}

	void testAllBodiesSameLit() {
		lpAdd(lp.start(ctx),
			"{a}.\n"
			"b :- not a.\n"
			"c :- not b.\n"
			"d :- b.\n"
			"d :- not c.\n"
			"b :- d.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(lp.getLiteral(b), lp.getLiteral(d));
		CPPUNIT_ASSERT(lp.getLiteral(a) != lp.getLiteral(c));
		ctx.master()->assume(lp.getLiteral(a)) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->value(lp.getLiteral(c).var()) == value_free);
		ctx.master()->assume(~lp.getLiteral(c)) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->numFreeVars() == 0 && ctx.master()->isTrue(lp.getLiteral(b)));
	}

	void testAllBodiesSameLit2() {
		lpAdd(lp.start(ctx),
			"{a;e}.\n"
			"b :- not a.\n"
			"c :- not b.\n"
			"d :- b.\n"
			"d :- not c.\n"
			"b :- d, e.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(lp.getLiteral(b), lp.getLiteral(d));
		CPPUNIT_ASSERT(lp.getLiteral(a) != lp.getLiteral(c));
		ctx.master()->assume(lp.getLiteral(a)) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->value(lp.getLiteral(c).var()) == value_free);
		ctx.master()->assume(~lp.getLiteral(c)) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->numFreeVars() == 0 && ctx.master()->isTrue(lp.getLiteral(b)));
		CPPUNIT_ASSERT(ctx.numVars() == 4);
	}

	void testCompLit() {
		lpAdd(lp.start(ctx),
			"{d}.\n"
			"a :- not c.\n"
			"c :- not a.\n"
			"b :- a, c.\n"
			"e :- a, d, not c. % a == ~c -> {a,c} = F -> {a, not c} = {a, d}\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(3u, ctx.numVars());
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(b)));
	}

	void testFunnySelfblockerOverEqByTwo() {
		lpAdd(lp.start(ctx),
			"{a,b,c}.\n"
			"d :- a, b.\n"
			"e :- a, b.\n"
			"f :- b, c.\n"
			"g :- b, c.\n"
			"f :- d, not f.\n"
			"h :- e, not g.\n"
			"i :- a, h.\n"
			"% -> d == e, f == g -> {e, not g} == {d, not f} -> F"
			"% -> h == i are both unsupported!");
		Var h = 8, i = 9;
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(h)));
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(i)));
	}

	void testRemoveKnownAtomFromWeightRule() {
		lpAdd(lp.start(ctx),
			"{c, d}.\n"
			"a."
			"e :- 5 {a = 2, not b = 2, c = 1, d = 1}.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		std::stringstream exp;
		exp << "1 1 0 0 \n"       // a.
		    << "3 2 3 4 0 0 \n"   // {c, d}.
		    << "2 5 2 0 1 3 4 \n" // e :- 1 { c, d }.
		    << "0\n";
		CPPUNIT_ASSERT(compareSmodels(exp, lp));
	}

	void testMergeEquivalentAtomsInConstraintRule() {
		lpAdd(lp.start(ctx),
			"{a, c}.\n"
			"a :- b.\n"
			"b :- a.\n"
			"d :-  2 {a, b, c}.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		std::stringstream exp("5 4 2 2 0 1 3 2 1");
		// d :-  2 [a=2, c].
		CPPUNIT_ASSERT(findSmodels(exp, lp));
	}

	void testMergeEquivalentAtomsInWeightRule() {
		lpAdd(lp.start(ctx),
			"{a, c, e}.\n"
			"a :- b.\n"
			"b :- a.\n"
			"d :-  3 {a = 1, c = 4, b = 2, e=1}.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		// x :-  3 [a=3, c=3,d=1].
		std::stringstream exp("5 4 3 3 0 1 3 5 3 3 1");
		CPPUNIT_ASSERT(findSmodels(exp, lp));
	}

	void testBothLitsInConstraintRule() {
		lpAdd(lp.start(ctx),
			"{a}.\n"
			"b :- a.\n"
			"c :- b.\n"
			"d :-  1 {a, b, not b, not c}.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		// d :-  1 [a=2, not a=2].
		std::stringstream exp("5 4 1 2 1 1 1 2 2");
		CPPUNIT_ASSERT(findSmodels(exp, lp));
	}

	void testBothLitsInWeightRule() {
		lpAdd(lp.start(ctx),
			"{a, e}.\n"
			"b :- a.\n"
			"c :- b.\n"
			"d :-  3 {a=3, not b=1, not c=3, e=2}.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		// d :-  3 [a=3, not a=4, e=2].
		std::stringstream exp("5 4 3 3 1 1 1 5 4 3 2");
		CPPUNIT_ASSERT(findSmodels(exp, lp));
	}

	void testWeightlessAtomsInWeightRule() {
		lpAdd(lp.start(ctx),
			"{a, b, c}.\n"
			"d :-  1 {a=1, b=1, c=0}.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		// d :-  1 {a, b}.
		std::stringstream exp("2 4 2 0 1 1 2");
		CPPUNIT_ASSERT(findSmodels(exp, lp));
	}

	void testSimplifyToNormal() {
		lpAdd(lp.start(ctx),
			"{a}.\n"
			"b :-  2 {a=2,not c=1}.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		// b :-  a.
		std::stringstream exp("1 2 1 0 1");
		CPPUNIT_ASSERT(findSmodels(exp, lp));
	}
	void testSimplifyToTrue() {
		lpAdd(lp.start(ctx),
			"a.\n"
			"b :-  1 {c, a}.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(lp.numBodies() <= 1);
	}

	void testSimplifyToCardBug() {
		lpAdd(lp.start(ctx),
			"a. b.\n"
			"c :- 168 {not a = 576, not b=381}.\n"
			"  :- c.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(ctx.master()->numFreeVars() == 0);
	}

	void testSimplifyCompBug() {
		Var h = 8;
		lpAdd(lp.start(ctx, LogicProgram::AspOptions().iterations(1)),
			"a :- not b.\n"
			"a :- b.\n"
			"b :- not c.\n"
			"c :- not a.\n"
			"d. e. g. {f}.\n"
			"h :- d, e, b, f, g.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		PrgAtom* x = lp.getAtom(h);
		PrgBody* B = lp.getBody(x->supps_begin()->node());
		CPPUNIT_ASSERT(B->size() == 2 && !B->goal(0).sign() && B->goal(1).sign());
		CPPUNIT_ASSERT(B->goal(0).var() == f);
		CPPUNIT_ASSERT(B->goal(1).var() == c);
	}

	void testBPWeight() {
		lpAdd(lp.start(ctx),
			"{a, b, c, d}.\n"
			"e :-  2 {a=1, b=2, not c=2, d=1}.\n"
			"  :- e.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isFalse(lp.getLiteral(b)));
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isTrue(lp.getLiteral(c)));
	}

	void testExtLitsAreFrozen() {
		Var g = 7, h = 8, i = 9;
		lpAdd(lp.start(ctx),
			"{a, b, c, d, e, f, g}.\n"
			" h :- 2 {b, c, d}.\n"
			"i :- 2 {c=1, d=2, e=1}.\n"
			"#minimize {f, g}.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT_EQUAL(false, ctx.varInfo(lp.getLiteral(a).var()).frozen());
		CPPUNIT_ASSERT_EQUAL(true, ctx.varInfo(lp.getLiteral(b).var()).frozen());
		CPPUNIT_ASSERT_EQUAL(true, ctx.varInfo(lp.getLiteral(c).var()).frozen());
		CPPUNIT_ASSERT_EQUAL(true, ctx.varInfo(lp.getLiteral(d).var()).frozen());
		CPPUNIT_ASSERT_EQUAL(true, ctx.varInfo(lp.getLiteral(e).var()).frozen());
		CPPUNIT_ASSERT_EQUAL(true, ctx.varInfo(lp.getLiteral(h).var()).frozen());
		CPPUNIT_ASSERT_EQUAL(true, ctx.varInfo(lp.getLiteral(i).var()).frozen());

		// minimize lits only frozen if constraint is actually used
		CPPUNIT_ASSERT_EQUAL(false, ctx.varInfo(lp.getLiteral(f).var()).frozen());
		CPPUNIT_ASSERT_EQUAL(false, ctx.varInfo(lp.getLiteral(g).var()).frozen());
		ctx.minimize();
		CPPUNIT_ASSERT_EQUAL(true, ctx.varInfo(lp.getLiteral(f).var()).frozen());
		CPPUNIT_ASSERT_EQUAL(true, ctx.varInfo(lp.getLiteral(g).var()).frozen());
	}

	void writeIntegrityConstraint() {
		lpAdd(lp.start(ctx),
			"{a;b;c}."
			"a :- c, not b.\n"
			"b :- c, not b.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());

		// falseAtom :- c, not b.
		// compute {not falseAtom}.
		std::stringstream exp("1 4 2 1 2 3\nB-\n4");
		CPPUNIT_ASSERT(findSmodels(exp, lp));
	}

	void testComputeTrueBug() {
		lpAdd(lp.start(ctx),
			"a :- not b.\n"
			"b :- a.\n"
			"a :- c.\n"
			"c :- a.\n"
			"  :- not a.\n");
		CPPUNIT_ASSERT_EQUAL(false, lp.endProgram() && ctx.endInit());
	}

	void testBackprop() {
		lpAdd(lp.start(ctx, LogicProgram::AspOptions().backpropagate()),
			"{e;f;g}.\n"
			"d :- e, a.\n"
			"a :- f, d.\n"
			"b :- e, g.\n"
			"c :- f, g.\n"
			"h :- e, not d.\n"
			"h :- f, not b.\n"
			"h :- g, not c.\n"
			"  :- h.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.numVars() == 0);
	}
	void testBackpropTrueCon() {
		Var x2 = 2, x3 = 3;
		lpAdd(lp.start(ctx, LogicProgram::AspOptions().backpropagate()),
			"x7.\n"
			"{x2;x3}.\n"
			"x4 :- not x6.\n"
			"   :- not x5.\n"
			"x5 :- 1 {not x2, not x3}.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		ctx.master()->assume(lp.getLiteral(x2)) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(x3)));
		ctx.master()->undoUntil(0);
		ctx.master()->assume(lp.getLiteral(x3)) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(x2)));
	}
	void testBackpropWrite() {
		lpAdd(lp.start(ctx, LogicProgram::AspOptions().backpropagate()),
			"a|b.\n"
			"c :- a.\n"
			"a :- c.\n"
			"d :- not c.\n"
			"e :- a,c.\n"
			"  :- e.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.numVars() == 0);
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(a)));
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(c)));
		CPPUNIT_ASSERT(ctx.master()->isTrue(lp.getLiteral(b)));
		CPPUNIT_ASSERT(ctx.master()->isTrue(lp.getLiteral(d)));

		std::stringstream exp("1 2 0 0\n1 4 0 0");
		CPPUNIT_ASSERT(findSmodels(exp, lp));
		CPPUNIT_ASSERT(!lp.isDefined(a));
		CPPUNIT_ASSERT(!lp.isDefined(c));
	}
	void testStatisticsObject() {
		StatisticObject stats = StatisticObject::map(&lp.stats);
		for (uint32 i = 0, end = stats.size(); i != end; ++i) {
			const char* k = stats.key(i);
			StatisticObject x = stats.at(k);
			CPPUNIT_ASSERT(x.value() == 0.0);
		}
		lpAdd(lp.start(ctx),
			"a :- not b.\n"
			"b :- not a.\n");
		lp.endProgram();
		CPPUNIT_ASSERT(stats.at("atoms").value() == (double)lp.stats.atoms);
		CPPUNIT_ASSERT(stats.at("rules").value() == (double)lp.stats.rules[0].sum());
	}
	void testSimpleIncremental() {
		lp.start(ctx);
		lp.updateProgram();
		lpAdd(lp, "a :- not b. b :- not a.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.numVars() == 1);
		CPPUNIT_ASSERT(lp.getLiteral(a) == ~lp.getLiteral(b));
		lp.updateProgram();
		lpAdd(lp,
			"c :- a, not d.\n"
			"d :- b, not c.\n"
			"e :- d.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.numVars() == 3);
		CPPUNIT_ASSERT(lp.getLiteral(a) == ~lp.getLiteral(b));
		CPPUNIT_ASSERT(lp.getLiteral(e) == lp.getLiteral(d));
	}
	void testIncrementalDistinctFacts() {
		lp.start(ctx);
		lp.enableDistinctTrue();
		lp.updateProgram();
		lpAdd(lp,
			"a.\n"
			"b :- c.\n"
			"c.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.numVars() == 0);
		CPPUNIT_ASSERT(lp.getLiteral(a) == lit_true());
		CPPUNIT_ASSERT(lp.getLiteral(b) == lit_true());
		CPPUNIT_ASSERT(lp.getLiteral(c) == lit_true());
		lp.updateProgram();
		lpAdd(lp,
			"d.\n"
			"e :- f.\n"
			"f.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.numVars() == 1);
		CPPUNIT_ASSERT(lp.getLiteral(d) == lit_true());
		CPPUNIT_ASSERT(lp.getLiteral(e) == lit_true());
		CPPUNIT_ASSERT(lp.getLiteral(f) == lit_true());
		CPPUNIT_ASSERT(lp.getLiteral(d, MapLit_t::Refined) == posLit(1));
		CPPUNIT_ASSERT(lp.getLiteral(e, MapLit_t::Refined) == posLit(1));
		CPPUNIT_ASSERT(lp.getLiteral(f, MapLit_t::Refined) == posLit(1));
	}
	void testIncrementalDistinctFactsSimple() {
		lp.start(ctx, LogicProgram::AspOptions().noEq());
		lp.enableDistinctTrue();
		lp.updateProgram();
		lpAdd(lp,"a.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.numVars() == 0);
		CPPUNIT_ASSERT(lp.getLiteral(a) == lit_true());
		lp.updateProgram();
		lpAdd(lp,
			"b :- d.\n"
			"c :- e.\n"
			"d. e.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.numVars() == 1);
		CPPUNIT_ASSERT(lp.getLiteral(b) == lit_true());
		CPPUNIT_ASSERT(lp.getLiteral(c) == lit_true());
		CPPUNIT_ASSERT(lp.getLiteral(d) == lit_true());
		CPPUNIT_ASSERT(lp.getLiteral(b, MapLit_t::Refined) == posLit(1));
		CPPUNIT_ASSERT(lp.getLiteral(c, MapLit_t::Refined) == posLit(1));
		CPPUNIT_ASSERT(lp.getLiteral(d, MapLit_t::Refined) == posLit(1));
		lp.updateProgram();
		lpAdd(lp, "f.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.numVars() == 2);
		CPPUNIT_ASSERT(lp.getLiteral(a, MapLit_t::Refined) == posLit(0));
		CPPUNIT_ASSERT(lp.getLiteral(b, MapLit_t::Refined) == posLit(1));
		CPPUNIT_ASSERT(lp.getLiteral(f, MapLit_t::Refined) == posLit(2));
	}
	void testIncrementalFreeze() {
		lp.start(ctx, LogicProgram::AspOptions().noEq());
		lp.updateProgram();
		lpAdd(lp,
			"{d}.\n"
			"a :- not c.\n"
			"b :- a, d.\n"
			"#external c.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(lp.getLiteral(c) != lit_false());
		Solver& solver = *ctx.master();
		solver.assume(lp.getLiteral(c));
		solver.propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(b)));
		solver.undoUntil(0);

		lp.updateProgram();
		lpAdd(lp,
			"{e}.\n"
			"c :- e.\n"
			"#external c. [release]");

		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		solver.assume(lp.getLiteral(e));
		solver.propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(b)));
		solver.undoUntil(0);
		solver.assume(~lp.getLiteral(e));
		solver.propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(c)));
		solver.assume(lp.getLiteral(d));
		solver.propagate();
		CPPUNIT_ASSERT(ctx.master()->isTrue(lp.getLiteral(b)));
	}
	void testIncrementalFreezeValue() {
		lp.start(ctx, LogicProgram::AspOptions().noEq());
		lp.updateProgram();
		lp.freeze(a).freeze(b, value_true).freeze(c, value_false);

		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		LitVec assume;
		lp.getAssumptions(assume);
		Solver& solver = *ctx.master();
		solver.pushRoot(assume);
		CPPUNIT_ASSERT(solver.isFalse(lp.getLiteral(a)));
		CPPUNIT_ASSERT(solver.isTrue(lp.getLiteral(b)));
		CPPUNIT_ASSERT(solver.isFalse(lp.getLiteral(c)));
		solver.popRootLevel(solver.decisionLevel());

		lp.updateProgram();
		lp.unfreeze(a).freeze(c, value_true).freeze(b, value_true).freeze(b, value_false);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		assume.clear();
		lp.getAssumptions(assume);
		CPPUNIT_ASSERT(assume.size() == 2 && solver.isFalse(lp.getLiteral(a)));
		solver.pushRoot(assume);
		CPPUNIT_ASSERT(solver.isFalse(lp.getLiteral(b)));
		CPPUNIT_ASSERT(solver.isTrue(lp.getLiteral(c)));
	}

	void testIncrementalFreezeOpen() {
		lp.start(ctx, LogicProgram::AspOptions().noEq());
		// I1:
		// freeze(a, value_free)
		lp.updateProgram();
		lp.freeze(a, value_free);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		LitVec assume;
		lp.getAssumptions(assume);
		Solver& solver = *ctx.master();
		CPPUNIT_ASSERT(assume.empty());
		CPPUNIT_ASSERT(solver.value(lp.getLiteral(a).var()) == value_free);

		// I2:
		lp.updateProgram();
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		assume.clear();
		lp.getAssumptions(assume);
		CPPUNIT_ASSERT(assume.empty());
		CPPUNIT_ASSERT(solver.value(lp.getLiteral(a).var()) == value_free);

		// I3:
		lp.updateProgram();
		lp.freeze(a, value_true);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		assume.clear();
		lp.getAssumptions(assume);
		CPPUNIT_ASSERT(assume.size() == 1 && assume[0] == lp.getLiteral(a));
	}
	void testIncrementalKeepFrozen() {
		lp.start(ctx);
		// I0:
		lp.updateProgram();
		lp.freeze(a);

		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		PrgAtom* x   = lp.getAtom(a);
		Literal xLit = x->literal();
		// I1:
		lp.updateProgram();
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(x->literal() == xLit);
		CPPUNIT_ASSERT(x->frozen());
	}
	void testIncrementalFreezeCompute() {
		lp.start(ctx);
		lp.updateProgram();
		lpAdd(lp,
			"#external a. #external b. #external c. #external d.\n"
			":- not a.\n"
			":- not b.\n"
			":- c.\n"
			":- d.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		PrgAtom* x = lp.getAtom(a);
		PrgAtom* y = lp.getAtom(b);
		CPPUNIT_ASSERT(x->frozen() && y->frozen());
		CPPUNIT_ASSERT(x->literal() != y->literal());
		PrgAtom* z  = lp.getAtom(c);
		PrgAtom* z2 = lp.getAtom(d);
		CPPUNIT_ASSERT(z->frozen() && z2->frozen());
		CPPUNIT_ASSERT(z->literal() == z2->literal());
		// I1:
		lp.updateProgram();
		lpAdd(lp, ":- a.");
		CPPUNIT_ASSERT_EQUAL(false, lp.endProgram());
	}
	void testIncrementalUnfreezeUnsupp() {
		lp.start(ctx, LogicProgram::AspOptions().noEq());
		lp.updateProgram();
		lpAdd(lp, "a :- not b. #external b.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		DefaultUnfoundedCheck* ufsCheck = 0;
		if (ctx.sccGraph.get()) {
			ctx.master()->addPost(ufsCheck = new DefaultUnfoundedCheck(*ctx.sccGraph));
		}
		ctx.endInit();
		lp.updateProgram();
		lpAdd(lp,
			"c :- b.\n"
			"b :- c.\n"
			"#external b. [release]");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		if (ctx.sccGraph.get() && !ufsCheck) {
			ctx.master()->addPost(ufsCheck = new DefaultUnfoundedCheck(*ctx.sccGraph));
		}
		ctx.endInit();
		CPPUNIT_ASSERT(ctx.master()->isTrue(lp.getLiteral(a)));
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(b)));
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(c)));
	}

	void testIncrementalUnfreezeCompute() {
		lp.start(ctx);
		lp.updateProgram();
		lpAdd(lp,
			"{d}.\n"
			"a :- b, c.\n"
			"b :- d.\n"
			"#external c.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(3u, ctx.numConstraints());

		lp.updateProgram();
		lpAdd(lp,
			"#external c.[release]\n"
			":- c.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(3u >= ctx.numConstraints());
		CPPUNIT_ASSERT(ctx.master()->numFreeVars() == 1);
	}

	void testIncrementalCompute() {
		lp.start(ctx, LogicProgram::AspOptions());
		lp.updateProgram();
		Var x2 = 2, x3 = 3, x4 = 4;
		lpAdd(lp,
			"{x2;x3}.\n"
			"x1 :- x2, x3.\n"
			"   :- x1.\n");

		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		lp.updateProgram();
		lpAdd(lp, "{x4}. :- x2, x4.");

		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		ctx.master()->assume(lp.getLiteral(x2));
		ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(x3)));
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(x4)));
	}
	void testIncrementalComputeBackprop() {
		lp.start(ctx, LogicProgram::AspOptions().backpropagate());
		lp.updateProgram();
		lpAdd(lp,
			"a :- not b.\n"
			"b :- not a.\n"
			"  :- not a.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		// I2:
		lp.updateProgram();
		lpAdd(lp, "c :- b. d :- not b.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(false, lp.getAtom(c)->hasVar());
		CPPUNIT_ASSERT_EQUAL(lit_true(), lp.getLiteral(d));
	}

	void testIncrementalBackpropStep() {
		lp.start(ctx);
		// I1:
		lp.updateProgram();
		lpAdd(lp, "{a}.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		// I2:
		lp.updateProgram();
		lpAdd(lp, "{c}.    b :- a, c.    :- not b.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.master()->isTrue(lp.getLiteral(a)));
	}

	void testIncrementalEq() {
		lp.start(ctx);
		lp.updateProgram();
		lpAdd(lp,
			"{c;d}.\n"
			"a :- c.\n"
			"a :- d.\n"
			"b :- a.\n");

		// b == a
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(true, lp.isDefined(a));
		CPPUNIT_ASSERT_EQUAL(false, lp.isDefined(b));

		std::stringstream exp("1 2 1 0 1");
		CPPUNIT_ASSERT(findSmodels(exp, lp));
		lp.updateProgram();
		lpAdd(lp,
			"e :- a, b.\n"
			"#output e : e.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		exp.str("1 5 1 0 1\n5 e");
		CPPUNIT_ASSERT(findSmodels(exp, lp));
	}

	void testIncrementalEqUnfreeze() {
		lp.start(ctx);
		lp.updateProgram();
		lp.freeze(a);
		lp.endProgram();
		lp.updateProgram();
		lpAdd(lp,
			"{d}.\n"
			"a :- c.\n"
			"b :- d, not a.\n"
			"#external a. [release]");

		lp.endProgram();
		CPPUNIT_ASSERT(ctx.numVars() == 2 && ctx.master()->numFreeVars() == 1);
		CPPUNIT_ASSERT(lp.getLiteral(b) == lp.getLiteral(d));
	}

	void testIncrementalEqComplement() {
		lp.start(ctx);
		lp.updateProgram();
		lpAdd(lp, "a :- not b.  b :- not a.");

		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		PrgAtom* na = lp.getAtom(a);
		PrgAtom* nb = lp.getAtom(b);
		CPPUNIT_ASSERT(nb->literal() == ~na->literal());
		// I1:
		lp.updateProgram();
		lpAdd(lp, "c :- a, b.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		PrgAtom* nc = lp.getAtom(c);
		CPPUNIT_ASSERT(nc->hasVar() == false);
	}

	void testIncrementalEqUpdateAssigned() {
		lp.start(ctx);
		// I0:
		lp.updateProgram();
		lp.freeze(a);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());

		// I1:
		lp.updateProgram();
		lpAdd(lp, "a :- b.  b :- a.");

		PrgAtom* x = lp.getAtom(a);
		x->setValue(value_weak_true);
		lp.endProgram();
		// only weak-true so still relevant in bodies!
		CPPUNIT_ASSERT(x->deps_begin()->sign() == false);
	}

	void testIncrementalEqResetState() {
		lp.start(ctx);
		// I0:
		lp.updateProgram();
		lpAdd(lp, "{a;b}.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());

		// I1:
		lp.updateProgram();
		lpAdd(lp,
			"c :- f.\n"
			"d :- g.\n"
			"c :- d, a.\n"
			"d :- c, b.\n"
			"f :- e, not h.\n"
			"g :- e, not i.\n"
			"{e}.");
		lp.endProgram();
		CPPUNIT_ASSERT(lp.getAtom(c)->scc() == 0);
		CPPUNIT_ASSERT(lp.getAtom(d)->scc() == 0);
	}

	void testIncrementalUnfreezeUnsuppEq() {
		lp.start(ctx, LogicProgram::AspOptions().noScc());
		// I0:
		lp.updateProgram();
		lp.freeze(a);

		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		// I1:
		lp.updateProgram();
		lpAdd(lp,
			"a :- b.\n"
			"b :- a, c.\n"
			"{c}.\n");
		lp.endProgram();
		PrgAtom* x = lp.getAtom(a);
		PrgAtom* y = lp.getAtom(b);
		CPPUNIT_ASSERT(ctx.master()->isFalse(x->literal()));
		CPPUNIT_ASSERT(ctx.master()->isFalse(y->literal()));
	}

	void testIncrementalUnfreezeEq() {
		lp.start(ctx);
		// I0:
		lp.updateProgram();
		lp.freeze(a);

		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		// I1:
		lp.updateProgram();
		lpAdd(lp,
			"{c}.\n"
			"b :- c.\n"
			"a :- b.\n");
		PrgAtom* x = lp.getAtom(a);
		lp.endProgram();
		// body {b} is eq to body {c}
		CPPUNIT_ASSERT(ctx.master()->value(x->var()) == value_free);
		CPPUNIT_ASSERT(x->supports() == 1 && x->supps_begin()->node() == 1);
	}

	void testIncrementalStats() {
		LpStats incStats;
		lp.start(ctx, LogicProgram::AspOptions().noEq());
		// I1:
		lp.updateProgram();
		lpAdd(lp,
			"a :- not b.\n"
			"b :- not a.\n"
			"#external c.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		incStats = lp.stats;
		CPPUNIT_ASSERT_EQUAL(uint32(3), incStats.atoms);
		CPPUNIT_ASSERT_EQUAL(uint32(2), incStats.bodies[0].sum());
		CPPUNIT_ASSERT_EQUAL(uint32(2), incStats.rules[0].sum());
		CPPUNIT_ASSERT_EQUAL(uint32(0), incStats.ufsNodes);
		CPPUNIT_ASSERT_EQUAL(uint32(0), incStats.sccs);

		// I2:
		lp.updateProgram();
		lpAdd(lp,
			"{c, f}.\n"
			"d :- not c.\n"
			"d :- e, f.\n"
			"e :- d, f.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		incStats.accu(lp.stats);
		CPPUNIT_ASSERT_EQUAL(uint32(6), incStats.atoms);
		CPPUNIT_ASSERT_EQUAL(uint32(5), incStats.bodies[0].sum());
		CPPUNIT_ASSERT_EQUAL(uint32(6), incStats.rules[0].sum());
		CPPUNIT_ASSERT_EQUAL(uint32(1), incStats.sccs);
		// I3:
		lp.updateProgram();
		lpAdd(lp,
			"g :- d, not i.\n"
			"i :- not g.\n"
			"g :- h.\n"
			"h :- g, not f.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		incStats.accu(lp.stats);
		CPPUNIT_ASSERT_EQUAL(uint32(9), incStats.atoms);
		CPPUNIT_ASSERT_EQUAL(uint32(9), incStats.bodies[0].sum());
		CPPUNIT_ASSERT_EQUAL(uint32(10), incStats.rules[0].sum());
		CPPUNIT_ASSERT_EQUAL(uint32(2), incStats.sccs);
	}

	void testIncrementalTransform() {
		lp.start(ctx, LogicProgram::AspOptions().noEq());
		lp.setExtendedRuleMode(LogicProgram::mode_transform);
		// I1:
		lp.updateProgram();
		lpAdd(lp, "{a}. % -> a :- not a'. a' :- not a.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.sccGraph.get() == 0);
		// I2:
		lp.updateProgram();
		lpAdd(lp,
			"% a' must not take up id!\n"
			"b :- a.\n"
			"b :- c.\n"
			"c :- b.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.sccGraph.get() != 0);
	}

	void testIncrementalBackpropCompute() {
		lp.start(ctx);
		// I0:
		lp.updateProgram();
		lpAdd(lp,
			"a :- b.\n"
			"  :- not a.\n"
			"#external b.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(lp.getRootId(a) == 2);
		PrgAtom* x = lp.getAtom(b);
		CPPUNIT_ASSERT(x->value() == value_weak_true);
		// I1:
		lp.updateProgram();
		lpAdd(lp, "b :- c.  c :- b.");

		// UNSAT: no support for b,c
		CPPUNIT_ASSERT_EQUAL(false, lp.endProgram());
	}

	void testIncrementalBackpropSolver() {
		lp.start(ctx);
		// I0:
		lp.updateProgram();
		lpAdd(lp,
			"{a}.\n"
			":- not a.\n"
			":- not b.\n"
			"#external b.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		PrgAtom* na = lp.getAtom(a);
		PrgAtom* nb = lp.getAtom(b);
		CPPUNIT_ASSERT(na->value() == value_true);
		CPPUNIT_ASSERT(nb->value() == value_weak_true);
		// I1:
		lp.updateProgram();
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(na->value() == value_true);
		CPPUNIT_ASSERT(nb->value() == value_weak_true);
	}

	void testIncrementalFreezeUnfreeze() {
		lp.start(ctx);
		// I0:
		lp.updateProgram();
		lpAdd(lp,
			"{a}."
			"#external b.\n"
			"#external b. [release]");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT_EQUAL(lit_false(), lp.getLiteral(b));
		// I1:
		lp.updateProgram();
		lpAdd(lp,
			"#external c.\n"
			"c :- b.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isFalse(lp.getLiteral(b)));
	}
	void testIncrementalSymbolUpdate() {
		lp.start(ctx);
		// I0:
		lp.updateProgram();
		lpAdd(lp, "{a}.");
		lp.addOutput("a", a);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		uint32 os = ctx.output.size();
		// I1:
		lp.updateProgram();
		lpAdd(lp, "{b;c}.");
		lp.addOutput("b", b);

		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(!isSentinel(lp.getLiteral(c)));
		CPPUNIT_ASSERT_EQUAL(os + 1, ctx.output.size());
	}
	void testIncrementalFreezeDefined() {
		lp.start(ctx);
		// I0:
		lp.updateProgram();
		lpAdd(lp, "{a}.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		// I1:
		lp.updateProgram();
		lpAdd(lp, "#external a.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(lp.getAtom(a)->frozen() == false);
	}
	void testIncrementalUnfreezeDefined() {
		lp.start(ctx);
		// I0:
		lp.updateProgram();
		lpAdd(lp, "{a}.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		// I1:
		lp.updateProgram();
		lpAdd(lp, "#external a. [release]");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(!ctx.master()->isFalse(lp.getLiteral(a)));
	}
	void testIncrementalUnfreezeAsFact() {
		lp.start(ctx);
		// I0:
		lp.updateProgram();
		lpAdd(lp, "#external a.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		Literal litA = lp.getLiteral(a);
		// I1:
		lp.updateProgram();
		lpAdd(lp, "a.");
		CPPUNIT_ASSERT_EQUAL(true , lp.endProgram());
		CPPUNIT_ASSERT_EQUAL(litA, lp.getLiteral(a));
		CPPUNIT_ASSERT_EQUAL(false, lp.isExternal(a));
		CPPUNIT_ASSERT_EQUAL(true , lp.isDefined(a));
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isTrue(litA));
	}
	void testIncrementalImplicitUnfreeze() {
		lp.start(ctx);
		// I0:
		lp.updateProgram();
		lpAdd(lp, "#external a.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(lp.getAtom(a)->frozen() == true);
		CPPUNIT_ASSERT(!ctx.master()->isFalse(lp.getLiteral(a)));
		// I1:
		lp.updateProgram();
		lpAdd(lp, "{a}.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(lp.getAtom(a)->frozen() == false);
	}
	void testIncrementalRedefine() {
		lp.start(ctx);
		// I0:
		lp.updateProgram();
		lpAdd(lp, "{a}.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		// I1:
		lp.updateProgram();
		CPPUNIT_ASSERT_THROW(lpAdd(lp, "{a}."), RedefinitionError);
	}
	void testIncrementalGetAssumptions() {
		lp.start(ctx);
		// I0:
		lp.updateProgram();
		lpAdd(lp, "#external a. #external b.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		LitVec assume;
		lp.getAssumptions(assume);
		CPPUNIT_ASSERT(assume.size() == 2 && assume[0] == ~lp.getLiteral(a) && assume[1] == ~lp.getLiteral(b));
	}

	void testIncrementalSimplifyCard() {
		lp.start(ctx);
		// I0:
		lp.updateProgram();
		lpAdd(lp, "a.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		lp.updateProgram();
		lpAdd(lp,
			"b :- 1 {c, a}.\n"
			"d :- 1 {c, b}.\n"
			"c :- a, b.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
	}

	void testIncrementalSimplifyMinimize() {
		lp.start(ctx);
		// I0:
		lp.updateProgram();
		lpAdd(lp, "a. #minimize{a}.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(ctx.minimize()->adjust(0) == 1);
		ctx.removeMinimize();

		lp.updateProgram();
		lpAdd(lp, "#minimize{a}.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(ctx.hasMinimize());
		CPPUNIT_ASSERT(ctx.minimize()->adjust(0) == 1);
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
	}

	void testIncrementalEqOverNeg() {
		lp.start(ctx);
		// I0: {a}.
		lp.updateProgram();
		lpAdd(lp, "{a}.");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		// I1:
		lp.updateProgram();
		lpAdd(lp,
			"b :- not a.\n"
			"c :- b.\n"
			"c :- f.\n"
			"d :- c.\n"
			"e :- d.\n"
			"g :- c.\n"
			"h :- not f, c.\n"
			"  :- not e.\n"
			"  :- not h.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(ctx.numVars() == 1 && ctx.master()->isFalse(lp.getLiteral(a)));
	}
	void testIncrementalKeepExternalValue() {
		lp.start(ctx);
		// I0:
		lp.updateProgram();
		lpAdd(lp,
			"b.\n"
			"a :- c.\n"
			"  :- a.\n"
			"#external c. [true]");

		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		LitVec assume;
		lp.getAssumptions(assume);
		CPPUNIT_ASSERT_EQUAL(false, ctx.master()->pushRoot(assume));

		CPPUNIT_ASSERT_EQUAL(true, lp.update());
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		assume.clear();
		lp.getAssumptions(assume);
		CPPUNIT_ASSERT_EQUAL(false, ctx.master()->pushRoot(assume));

		CPPUNIT_ASSERT_EQUAL(true, lp.update());
		lpAdd(lp, "c.");
		CPPUNIT_ASSERT_EQUAL(false, lp.endProgram());
	}

	void testIncrementalWriteMinimize() {
		lp.start(ctx);
		lp.updateProgram();
		lpAdd(lp, "{a}. #minimize{a}.");
		lp.endProgram();
		std::stringstream exp("6 0 1 0 1 1");
		CPPUNIT_ASSERT(findSmodels(exp, lp));
		lp.updateProgram();
		lpAdd(lp, "{b}. #minimize{b}.");

		lp.endProgram();
		exp.str("6 0 2 0 1 2 1 1");
		CPPUNIT_ASSERT(findSmodels(exp, lp));
		lp.updateProgram();
		lpAdd(lp, "{c}.");
		lp.endProgram();
		exp.clear();
		exp.seekg(0, ios::beg);
		CPPUNIT_ASSERT_EQUAL(false, findSmodels(exp, lp));
	}
	void testIncrementalWriteExternal() {
		lp.start(ctx);
		lp.updateProgram();
		lpAdd(lp, "#external a.");
		lp.endProgram();
		std::stringstream str;
		AspParser::write(lp, str, AspParser::format_aspif);
		bool foundA = false, foundB = false;
		for (std::string x; std::getline(str, x);) {
			if (x.find("5 1 2") == 0) { foundA = true; }
			if (x.find("5 2 2") == 0) { foundB = true; }
		}
		CPPUNIT_ASSERT(foundA && !foundB);
		lp.updateProgram();
		lpAdd(lp, "#external b.");
		lp.endProgram();
		foundA = foundB = false;
		str.clear();
		AspParser::write(lp, str, AspParser::format_aspif);
		for (std::string x; std::getline(str, x);) {
			if (x.find("5 1 2") == 0) { foundA = true; }
			if (x.find("5 2 2") == 0) { foundB = true; }
		}
		CPPUNIT_ASSERT(!foundA && foundB);
	}
	void testIncrementalWriteUnfreeze() {
		lp.start(ctx);
		lp.updateProgram();
		lpAdd(lp, "#external a.");
		lp.endProgram();
		lp.updateProgram();
		lpAdd(lp, "#external a. [release]");
		lp.endProgram();
		CPPUNIT_ASSERT(!lp.isExternal(a));
		std::stringstream str;
		AspParser::write(lp, str, AspParser::format_aspif);
		bool found = false;
		for (std::string x; std::getline(str, x);) {
			if (x.find("5 1 3") == 0) { found = true; break; }
		}
		CPPUNIT_ASSERT(found);
	}
	void testIncrementalSetInputAtoms() {
		lp.start(ctx);
		lp.updateProgram();
		lpAdd(lp, "{a;b;c}.");
		CPPUNIT_ASSERT(lp.numAtoms() == 3);
		lp.setMaxInputAtom(lp.numAtoms());
		Var d = lp.newAtom();
		Var e = lp.newAtom();
		CPPUNIT_ASSERT(d == 4 && e == 5);
		lp.endProgram();
		CPPUNIT_ASSERT(lp.numAtoms() == 5 && lp.startAuxAtom() == 4 && lp.stats.auxAtoms == 2);
		lp.updateProgram();
		CPPUNIT_ASSERT_MESSAGE("aux atoms are removed on update", lp.numAtoms() == 3);
		CPPUNIT_ASSERT_EQUAL(false, lp.validAtom(d));
		CPPUNIT_ASSERT_EQUAL(false, lp.validAtom(e));
		CPPUNIT_ASSERT_EQUAL(d, lp.newAtom());
	}

	void testFreezeIsExternal() {
		lp.start(ctx);
		lp.updateProgram();
		lpAdd(lp, "{b}. #external a.");
		CPPUNIT_ASSERT_EQUAL(true , lp.isExternal(a));
		CPPUNIT_ASSERT_EQUAL(false, lp.isExternal(b));
		lp.endProgram();
		CPPUNIT_ASSERT_EQUAL(true , lp.isExternal(a));
		CPPUNIT_ASSERT_EQUAL(false, lp.isExternal(b));
	}
	void testUnfreezeIsNotExternal() {
		lp.start(ctx);
		lp.updateProgram();
		lpAdd(lp,
			"#external a.\n"
			"#external b. [release]\n"
			"#external a. [release]\n"
			"#external b.\n");
		CPPUNIT_ASSERT_EQUAL(false, lp.isExternal(a));
		CPPUNIT_ASSERT_EQUAL(false, lp.isExternal(b));
		lp.endProgram();
		CPPUNIT_ASSERT_EQUAL(false, lp.isExternal(a));
		CPPUNIT_ASSERT_EQUAL(false, lp.isExternal(b));
	}
	void testFreezeStaysExternal() {
		lp.start(ctx);
		lp.updateProgram();
		lpAdd(lp, "#external a.");
		CPPUNIT_ASSERT_EQUAL(true, lp.isExternal(a));
		lp.endProgram();
		CPPUNIT_ASSERT_EQUAL(true, lp.isExternal(a));
		lp.updateProgram();
		CPPUNIT_ASSERT_EQUAL(true, lp.isExternal(a));
		lp.endProgram();
		CPPUNIT_ASSERT_EQUAL(true, lp.isExternal(a));
	}
	void testDefinedIsNotExternal() {
		lp.start(ctx);
		lp.updateProgram();
		lpAdd(lp, "#external a.");
		lp.endProgram();
		lp.updateProgram();
		lpAdd(lp, "a :- b.");
		CPPUNIT_ASSERT_EQUAL(false, lp.isExternal(a));
		lp.endProgram();
		CPPUNIT_ASSERT_EQUAL(false, lp.isExternal(a));
	}
	void testFactIsNotExternal() {
		lp.start(ctx);
		lp.updateProgram();
		lpAdd(lp, "a. #external a.");
		lp.endProgram();
		CPPUNIT_ASSERT_EQUAL(false, lp.isExternal(a));
	}
	void testFactIsDefined() {
		lp.start(ctx);
		lp.updateProgram();
		lpAdd(lp, "a.");
		lp.endProgram();
		CPPUNIT_ASSERT_EQUAL(true, lp.isDefined(a));
	}
	void testBogusAtomIsNotDefined() {
		lp.start(ctx);
		lp.updateProgram();
		lp.endProgram();
		CPPUNIT_ASSERT_EQUAL(false, lp.isDefined(0xDEAD));
		CPPUNIT_ASSERT_EQUAL(false, lp.isExternal(0xDEAD));
		CPPUNIT_ASSERT_EQUAL(lit_false(), lp.getLiteral(0xDEAD));
	}
	void testMakeAtomicCondition() {
		lpAdd(lp.start(ctx), "{a;b}.");
		Potassco::Lit_t cond[2] = { Potassco::lit(a), Potassco::neg(b) };
		Id_t c1 = lp.newCondition(Potassco::toSpan(cond, 1));
		Id_t c2 = lp.newCondition(Potassco::toSpan(cond + 1, 1));
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT_EQUAL(lp.getLiteral(c1), lp.getLiteral(a));
		CPPUNIT_ASSERT_EQUAL(lp.getLiteral(c2), ~lp.getLiteral(b));
	}

	void testMakeComplexCondition() {
		lpAdd(lp.start(ctx), "{a;b}.");
		Potassco::Lit_t cond[2] = { Potassco::lit(a), Potassco::neg(b) };
		Id_t c1 = lp.newCondition(Potassco::toSpan(cond, 0));
		Id_t c2 = lp.newCondition(Potassco::toSpan(cond, 2));
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(lp.getLiteral(c1), lit_true());
		Literal c2Lit = lp.getLiteral(c2);
		Solver& s = *ctx.master();
		CPPUNIT_ASSERT_EQUAL(value_free, s.value(c2Lit.var()));
		CPPUNIT_ASSERT(s.assume(c2Lit) && s.propagate());
		CPPUNIT_ASSERT(s.isTrue(lp.getLiteral(a)));
		CPPUNIT_ASSERT(s.isFalse(lp.getLiteral(b)));
	}
	void testMakeFalseCondition() {
		lp.start(ctx);
		Var a = lp.newAtom();
		Potassco::Lit_t cond[2] ={Potassco::lit(a), Potassco::neg(a)};
		Id_t c1 = lp.newCondition(Potassco::toSpan(cond, 2));
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(lp.getLiteral(c1), lit_false());
		CPPUNIT_ASSERT_THROW(solverLiteral(lp, c1), std::logic_error);
	}
	void testMakeInvalidCondition() {
		lp.start(ctx);
		Var a = lp.newAtom();
		Var b = lp.newAtom();
		Potassco::Lit_t cond[2] ={Potassco::lit(a), Potassco::neg(b)};
		Id_t c1 = lp.newCondition(Potassco::toSpan(cond, 2));
		Potassco::Lit_t cAsLit = static_cast<Potassco::Lit_t>(c1);
		CPPUNIT_ASSERT_THROW(lp.newCondition(Potassco::toSpan(&cAsLit, 1)), std::overflow_error);
	}
	void testExtractCondition() {
		lpAdd(lp.start(ctx), "{a;b}.");
		Potassco::Lit_t cond[2] = { Potassco::lit(a), Potassco::lit(b) };
		Id_t c1 = lp.newCondition(Potassco::toSpan(cond, 2));
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());

		Potassco::LitVec ext;
		lp.extractCondition(c1, ext);
		CPPUNIT_ASSERT(ext.size() == 2 && std::equal(ext.begin(), ext.end(), cond));

		lp.dispose(false);
		CPPUNIT_ASSERT_THROW(lp.extractCondition(c1, ext), std::logic_error);
	}
	void testGetConditionAfterDispose() {
		lpAdd(lp.start(ctx), "{a;b}.");
		Potassco::Lit_t cond[2] = { Potassco::lit(a), Potassco::lit(b) };
		Id_t c1 = lp.newCondition(Potassco::toSpan(cond, 2));
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());

		CPPUNIT_ASSERT(!isSentinel(lp.getLiteral(c1)));
		lp.dispose(false);
		CPPUNIT_ASSERT_THROW(lp.getLiteral(c1), std::logic_error);
	}

	void testAssumptionsAreVolatile() {
		lp.start(ctx);
		lp.updateProgram();
		lpAdd(lp, "{a}. #assume{a}.");
		CPPUNIT_ASSERT(lp.endProgram());
		LitVec assume;
		lp.getAssumptions(assume);
		CPPUNIT_ASSERT(assume.size() == 1 && assume[0] == lp.getLiteral(a));
		lp.updateProgram();
		lpAdd(lp, "#assume{not a}.");
		CPPUNIT_ASSERT(lp.endProgram());
		assume.clear();
		lp.getAssumptions(assume);
		CPPUNIT_ASSERT(assume.size() == 1 && assume[0] == ~lp.getLiteral(a));
	}

	void testProjectionIsExplicitAndCumulative() {
		lp.start(ctx);
		lp.updateProgram();
		lpAdd(lp, "{a;b}. #project {a}.");
		CPPUNIT_ASSERT(lp.endProgram());

		CPPUNIT_ASSERT(ctx.output.projectMode() == ProjectMode_t::Explicit);
		CPPUNIT_ASSERT(std::find(ctx.output.proj_begin(), ctx.output.proj_end(), lp.getLiteral(a)) != ctx.output.proj_end());
		CPPUNIT_ASSERT(std::find(ctx.output.proj_begin(), ctx.output.proj_end(), lp.getLiteral(b)) == ctx.output.proj_end());

		lp.updateProgram();
		lpAdd(lp, "{c;d}. #project{d}.");
		CPPUNIT_ASSERT(lp.endProgram());

		CPPUNIT_ASSERT(ctx.output.projectMode() == ProjectMode_t::Explicit);
		CPPUNIT_ASSERT(std::find(ctx.output.proj_begin(), ctx.output.proj_end(), lp.getLiteral(a)) != ctx.output.proj_end());
		CPPUNIT_ASSERT(std::find(ctx.output.proj_begin(), ctx.output.proj_end(), lp.getLiteral(b)) == ctx.output.proj_end());
		CPPUNIT_ASSERT(std::find(ctx.output.proj_begin(), ctx.output.proj_end(), lp.getLiteral(c)) == ctx.output.proj_end());
		CPPUNIT_ASSERT(std::find(ctx.output.proj_begin(), ctx.output.proj_end(), lp.getLiteral(d)) != ctx.output.proj_end());
	}

	void testTheoryAtomsAreFrozen() {
		lpAdd(lp.start(ctx), "b :- a.");
		Potassco::TheoryData& t = lp.theoryData();
		t.addTerm(0, "Theory");
		t.addAtom(a, 0, Potassco::toSpan<Potassco::Id_t>());
		lp.endProgram();
		CPPUNIT_ASSERT(lp.getLiteral(a) != lit_false());
		CPPUNIT_ASSERT(lp.isExternal(a));
		CPPUNIT_ASSERT(lp.getLiteral(b) != lit_false());
		ctx.endInit();
		CPPUNIT_ASSERT(ctx.varInfo(lp.getLiteral(a).var()).frozen());
	}
	void testTheoryAtomsAreFrozenIncremental() {
		lp.start(ctx).update();
		lpAdd(lp, "b :- a.");
		Potassco::TheoryData& t = lp.theoryData();
		t.addTerm(0, "Theory");
		t.addAtom(a, 0, Potassco::toSpan<Potassco::Id_t>());
		lp.endProgram();
		CPPUNIT_ASSERT(lp.getLiteral(a) != lit_false());
		CPPUNIT_ASSERT(lp.getLiteral(b) != lit_false());
		std::stringstream str;
		AspParser::write(lp, str, AspParser::format_aspif);
		for (std::string x; std::getline(str, x);) {
			CPPUNIT_ASSERT(x.find("5 1") != 0);
		}
		lp.update();
		lpAdd(lp,
			"{c}."
			"a :- c.");
		lp.endProgram();
		ctx.endInit();
		CPPUNIT_ASSERT(ctx.master()->value(lp.getLiteral(a).var()) == value_free);
		ctx.addUnary(~lp.getLiteral(c));
		ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(a)));
	}
	void testAcceptIgnoresAuxChoicesFromTheoryAtoms() {
		lp.start(ctx);
		a = lp.newAtom();
		Potassco::TheoryData& t = lp.theoryData();
		t.addTerm(0, "Theory");
		t.addAtom(a, 0, Potassco::toSpan<Potassco::Id_t>());
		lp.endProgram();
		CPPUNIT_ASSERT(lp.getLiteral(a) != lit_false());
		std::stringstream str;
		AspParser::write(lp, str, AspParser::format_aspif);
		for (std::string x; std::getline(str, x);) {
			CPPUNIT_ASSERT(x.find("1 1") != 0);
			CPPUNIT_ASSERT(x.find("5 1") != 0);
		}
		ctx.endInit();
		CPPUNIT_ASSERT(ctx.varInfo(lp.getLiteral(a).var()).frozen());
	}
	void testFalseHeadTheoryAtomsAreRemoved() {
		lpAdd(lp.start(ctx), "a :- b.");
		Potassco::TheoryData& t = lp.theoryData();
		t.addTerm(0, "Theory");
		t.addAtom(a, 0, Potassco::toSpan<Potassco::Id_t>());
		lp.endProgram();
		CPPUNIT_ASSERT(lp.getLiteral(a) == lit_false());
		CPPUNIT_ASSERT(lp.getLiteral(b) == lit_false());
		CPPUNIT_ASSERT(t.numAtoms() == 0);
	}
	void testFalseBodyTheoryAtomsAreKept() {
		lp.start(ctx);
		a = lp.newAtom();
		Potassco::TheoryData& t = lp.theoryData();
		t.addTerm(0, "Theory");
		t.addAtom(a, 0, Potassco::toSpan<Potassco::Id_t>());
		lpAdd(lp, ":- a.");
		lp.endProgram();
		CPPUNIT_ASSERT(lp.getLiteral(a) == lit_false());
		CPPUNIT_ASSERT(t.numAtoms() == 1);
		std::stringstream str;
		AspParser::write(lp, str, AspParser::format_aspif);
		CPPUNIT_ASSERT(str.str().find("1 0 0 0 1 1") != std::string::npos);
	}
	void testFactTheoryAtomsAreNotExternal() {
		lp.start(ctx).updateProgram();
		lpAdd(lp, "a.");
		Potassco::TheoryData& t = lp.theoryData();
		t.addAtom(a, 0, Potassco::toSpan<Potassco::Id_t>());
		lp.endProgram();
		CPPUNIT_ASSERT(lp.getLiteral(a) == lit_true());
		CPPUNIT_ASSERT(lp.isDefined(a));
		CPPUNIT_ASSERT(lp.isFact(a));
		CPPUNIT_ASSERT(!lp.isExternal(a));
		CPPUNIT_ASSERT(lp.getRootAtom(a)->supports() == 0);
		lp.updateProgram();
		lpAdd(lp, "b.");
		t.addAtom(b, 0, Potassco::toSpan<Potassco::Id_t>());
		lp.endProgram();
		CPPUNIT_ASSERT(lp.getLiteral(b) == lit_true());
		CPPUNIT_ASSERT(lp.isDefined(b));
		CPPUNIT_ASSERT(lp.isFact(b));
		CPPUNIT_ASSERT(lp.getRootAtom(b)->supports() == 0);
	}
	void testTheoryAtomsAreAdded() {
		lp.start(ctx).updateProgram();
		lpAdd(lp, "{a;b}.");
		Potassco::TheoryData& t = lp.theoryData();
		t.addAtom(c, 0, Potassco::toSpan<Potassco::Id_t>());
		lp.endProgram();
		CPPUNIT_ASSERT(lp.getLiteral(c).var() != 0);
		CPPUNIT_ASSERT(lp.isExternal(c));
		lp.updateProgram();
		lpAdd(lp, "c.");
		lp.endProgram();
		CPPUNIT_ASSERT(lp.isFact(c));
		CPPUNIT_ASSERT(!lp.isExternal(c));
		CPPUNIT_ASSERT(ctx.master()->isTrue(lp.getLiteral(c)));
		LitVec vec;
		lp.getAssumptions(vec);
		CPPUNIT_ASSERT(vec.empty());
	}
	void testOutputFactsNotSupportedInSmodels() {
		lp.start(ctx);
		lp.addOutput("Hallo", Potassco::toSpan<Potassco::Lit_t>());
		lp.addOutput("World", Potassco::toSpan<Potassco::Lit_t>());
		lp.endProgram();
		CPPUNIT_ASSERT_EQUAL(false, lp.supportsSmodels());
	}
	void testDisposeBug() {
		lp.start(ctx);
		lp.theoryData().addTerm(0, 99);
		lp.start(ctx);
		CPPUNIT_ASSERT_EQUAL(false, lp.theoryData().hasTerm(0));
	}
private:
	typedef Asp::PrgDepGraph DG;
	SharedContext ctx;
	LogicProgram  lp;
	Var           a, b, c, d, e, f;
};
class SatBuilderTest : public CppUnit::TestFixture {
	CPPUNIT_TEST_SUITE(SatBuilderTest);
	CPPUNIT_TEST(testPrepare);
	CPPUNIT_TEST(testNoClauses);
	CPPUNIT_TEST(testAddClause);
	CPPUNIT_TEST(testAddSoftClause);
	CPPUNIT_TEST(testAddEmptySoftClause);
	CPPUNIT_TEST(testAddConflicting);
	CPPUNIT_TEST_SUITE_END();
public:
	void setUp() {
		builder.startProgram(ctx);
	}
	void testPrepare() {
		builder.prepareProblem(10);
		builder.endProgram();
		CPPUNIT_ASSERT(ctx.numVars() == 10);
	}
	void testNoClauses() {
		builder.prepareProblem(2);
		builder.endProgram();
		CPPUNIT_ASSERT(ctx.master()->numFreeVars() == 0);
	}
	void testAddClause() {
		builder.prepareProblem(2);
		LitVec clause; clause.push_back(posLit(1)); clause.push_back(posLit(2));
		builder.addClause(clause);
		builder.endProgram();
		CPPUNIT_ASSERT(ctx.numConstraints() == 1);
		CPPUNIT_ASSERT(!ctx.hasMinimize());
	}
	void testAddSoftClause() {
		builder.prepareProblem(3);
		LitVec clause;
		clause.push_back(posLit(1));
		builder.addClause(clause, 1);
		clause.clear();
		clause.push_back(negLit(1));
		clause.push_back(posLit(2));
		clause.push_back(negLit(3));
		builder.addClause(clause, 2);
		builder.endProgram();
		CPPUNIT_ASSERT(ctx.numConstraints() == 1);
		CPPUNIT_ASSERT(ctx.minimize()->numRules() == 1);
		CPPUNIT_ASSERT(ctx.numVars() > 3);
	}
	void testAddEmptySoftClause() {
		builder.prepareProblem(3);
		LitVec clause;
		clause.push_back(posLit(1));
		// force 1
		builder.addClause(clause);

		clause.clear();
		clause.push_back(negLit(1));
		builder.addClause(clause, 1);
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(ctx.minimize()->numRules() == 1);
		CPPUNIT_ASSERT(ctx.minimize()->adjust(0) == 1);
	}
	void testAddConflicting() {
		builder.prepareProblem(3);
		LitVec clause;
		clause.push_back(posLit(1));
		CPPUNIT_ASSERT(builder.addClause(clause));
		clause.clear();
		clause.push_back(negLit(1));
		CPPUNIT_ASSERT(builder.addClause(clause) == false);
		clause.clear();
		clause.push_back(posLit(2));
		clause.push_back(posLit(3));
		CPPUNIT_ASSERT(builder.addClause(clause) == false);
		CPPUNIT_ASSERT(builder.endProgram() == false);
		CPPUNIT_ASSERT(ctx.ok() == false);
	}
private:
	SharedContext ctx;
	SatBuilder    builder;
};

class PBBuilderTest : public CppUnit::TestFixture {
	CPPUNIT_TEST_SUITE(PBBuilderTest);
	CPPUNIT_TEST(testPrepare);
	CPPUNIT_TEST(testNegativeWeight);
	CPPUNIT_TEST(testProduct);
	CPPUNIT_TEST(testProductTrue);
	CPPUNIT_TEST(testProductFalse);
	CPPUNIT_TEST(testInconsistent);
	CPPUNIT_TEST(testInconsistentW);
	CPPUNIT_TEST(testCoefficientReductionOnEq);
	CPPUNIT_TEST_SUITE_END();
public:
	void setUp() {
		builder.startProgram(ctx);
	}
	void testPrepare() {
		builder.prepareProblem(10, 0, 0);
		builder.endProgram();
		CPPUNIT_ASSERT(ctx.numVars() == 10);
	}
	void testNegativeWeight() {
		builder.prepareProblem(5, 0, 0);
		WeightLitVec con;
		con.push_back(WeightLiteral(posLit(1), 2));
		con.push_back(WeightLiteral(posLit(2), -2));
		con.push_back(WeightLiteral(posLit(3), -1));
		con.push_back(WeightLiteral(posLit(4), 1));
		con.push_back(WeightLiteral(posLit(5), 1));
		builder.addConstraint(con, 2);
		builder.endProgram();
		CPPUNIT_ASSERT(ctx.numConstraints() == 1);
		CPPUNIT_ASSERT(ctx.master()->numAssignedVars() == 0);
		ctx.master()->assume(negLit(1)) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->numFreeVars() == 0);
	}
	void testProduct() {
		builder.prepareProblem(3, 1, 1);
		LitVec p1(3), p2;
		p1[0] = posLit(1);
		p1[1] = posLit(2);
		p1[2] = posLit(3);
		p2    = p1;
		Literal x = builder.addProduct(p1);
		Literal y = builder.addProduct(p2);
		CPPUNIT_ASSERT(x.var() == 4 && x == y);
	}
	void testProductTrue() {
		builder.prepareProblem(3, 1, 1);
		LitVec p1(3);
		p1[0] = posLit(1);
		p1[1] = posLit(2);
		p1[2] = posLit(3);
		ctx.master()->force(posLit(1), 0);
		ctx.master()->force(posLit(2), 0);
		ctx.master()->force(posLit(3), 0);
		Literal x = builder.addProduct(p1);
		CPPUNIT_ASSERT(x == lit_true());
	}
	void testProductFalse() {
		builder.prepareProblem(3, 1, 1);
		LitVec p1(3);
		p1[0] = posLit(1);
		p1[1] = posLit(2);
		p1[2] = posLit(3);
		ctx.master()->force(negLit(2), 0);
		Literal x = builder.addProduct(p1);
		CPPUNIT_ASSERT(x == lit_false());
	}
	void testInconsistent() {
		builder.prepareProblem(1, 0, 0);
		WeightLitVec con;
		con.push_back(WeightLiteral(posLit(1), 1));
		CPPUNIT_ASSERT_EQUAL(true, builder.addConstraint(con, 1));
		con.assign(1, WeightLiteral(posLit(1), 1));
		CPPUNIT_ASSERT_EQUAL(false, builder.addConstraint(con, 0, true));
		CPPUNIT_ASSERT_EQUAL(false, builder.endProgram());
	}
	void testInconsistentW() {
		builder.prepareProblem(2, 0, 0);
		WeightLitVec con;
		con.push_back(WeightLiteral(posLit(1), 1));
		CPPUNIT_ASSERT_EQUAL(true, builder.addConstraint(con, 1));
		con.assign(1, WeightLiteral(posLit(1), 3));
		con.push_back(WeightLiteral(posLit(2), 2));
		CPPUNIT_ASSERT_EQUAL(false, builder.addConstraint(con, 2, true));
		CPPUNIT_ASSERT_EQUAL(false, builder.endProgram());
	}
	void testCoefficientReductionOnEq() {
		builder.prepareProblem(4, 0, 0);
		WeightLitVec con;
		con.push_back(WeightLiteral(posLit(1), 3));
		con.push_back(WeightLiteral(posLit(2), 2));
		con.push_back(WeightLiteral(posLit(3), 1));
		con.push_back(WeightLiteral(posLit(4), 1));
		CPPUNIT_ASSERT_EQUAL(true, builder.addConstraint(con, 2, true));
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(ctx.master()->isFalse(posLit(1)));
	}
private:
	SharedContext ctx;
	PBBuilder     builder;
};
CPPUNIT_TEST_SUITE_REGISTRATION(LogicProgramTest);
CPPUNIT_TEST_SUITE_REGISTRATION(SatBuilderTest);
CPPUNIT_TEST_SUITE_REGISTRATION(PBBuilderTest);
 } }
