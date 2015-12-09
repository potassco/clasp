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
#include <clasp/minimize_constraint.h>
#include <clasp/unfounded_check.h>

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
	CPPUNIT_TEST(testMergeValue);
	CPPUNIT_TEST(testIgnoreRules);
	CPPUNIT_TEST(testDuplicateRule);
	CPPUNIT_TEST(testNotAChoice);
	CPPUNIT_TEST(testNotAChoiceMerge);
	CPPUNIT_TEST(testMergeToSelfblocker);
	CPPUNIT_TEST(testMergeToSelfblocker2);
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
	CPPUNIT_TEST(testAddOneFact);
	CPPUNIT_TEST(testTwoFactsOnlyOneVar);
	CPPUNIT_TEST(testDontAddOnePredsThatAreNotHeads);
	CPPUNIT_TEST(testDontAddDuplicateBodies);
	CPPUNIT_TEST(testDontAddDuplicateSumBodies);
	CPPUNIT_TEST(testDontAddDuplicateSimpBodies);
	CPPUNIT_TEST(testDontAddUnsupported);
	CPPUNIT_TEST(testDontAddUnsupportedNoEq);
	CPPUNIT_TEST(testDontAddUnsupportedExtNoEq);
	CPPUNIT_TEST(testAssertSelfblockers);

	CPPUNIT_TEST(testRegressionR1);
	CPPUNIT_TEST(testRegressionR2);
	CPPUNIT_TEST(testFuzzBug);
	CPPUNIT_TEST(testBackpropNoEqBug);
	
	CPPUNIT_TEST(testCloneShare);
	CPPUNIT_TEST(testCloneShareSymbols);
	CPPUNIT_TEST(testCloneFull);

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

	CPPUNIT_TEST(testBPWeight);

	CPPUNIT_TEST(testExtLitsAreFrozen);	
	CPPUNIT_TEST(writeIntegrityConstraint);
	CPPUNIT_TEST(testComputeTrueBug);
	CPPUNIT_TEST(testBackprop);
	CPPUNIT_TEST(testBackpropTrueCon);
	CPPUNIT_TEST(testBackpropWrite);

	CPPUNIT_TEST(testSimpleIncremental);
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
	CPPUNIT_TEST(testIncrementalImplicitUnfreeze);
	CPPUNIT_TEST(testIncrementalRedefine);
	CPPUNIT_TEST(testIncrementalGetAssumptions);
	CPPUNIT_TEST(testIncrementalSimplifyCard);
	CPPUNIT_TEST(testIncrementalSimplifyMinimize);
	CPPUNIT_TEST(testIncrementalEqOverNeg);

	CPPUNIT_TEST(testIncrementalKeepExternalValue);

	CPPUNIT_TEST(testFreezeIsExternal);
	CPPUNIT_TEST(testUnfreezeIsNotExternal);
	CPPUNIT_TEST(testFreezeStaysExternal);
	CPPUNIT_TEST(testDefinedIsNotExternal);
	CPPUNIT_TEST_SUITE_END();	
public:
	void tearDown(){
		ctx.reset();
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
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule().addHead(1).addToBody(1, true).endRule()  // a :- a.
			.startRule().addHead(2).addToBody(1, true).endRule()  // b :- a.
		;
		CPPUNIT_ASSERT_EQUAL(1u, builder.stats.rules());
	}

	void testDuplicateRule() {
		builder.start(ctx, LogicProgram::AspOptions().iterations(1))
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule(CHOICERULE).addHead(2).endRule()  // {b}.
			.startRule().addHead(1).addToBody(2, true).endRule()  // a :- b.
			.startRule().addHead(1).addToBody(2, true).endRule()  // a :- b.
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.symbolTable()[1].lit == ctx.symbolTable()[2].lit);
	}

	void testNotAChoice() {
		// {b}.
		// {a} :- not b.
		// a :- not b.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule(CHOICERULE).addHead(2).endRule()
			.startRule(CHOICERULE).addHead(1).addToBody(2, false).endRule()
			.startRule().addHead(1).addToBody(2, false).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		const SymbolTable& index = ctx.symbolTable();
		ctx.master()->assume(~index[2].lit) && ctx.master()->propagate();
		// if b is false, a must be true because a :- not b. is stronger than {a} :- not b.
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isTrue(index[1].lit));
	}

	void testNotAChoiceMerge() {
		// {b}.
		// {a} :- b.
		// a :- b, not c.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c")
			.startRule(CHOICERULE).addHead(2).endRule()
			.startRule(CHOICERULE).addHead(1).addToBody(2, true).endRule()
			.startRule().addHead(1).addToBody(2, true).addToBody(3, false).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		const SymbolTable& index = ctx.symbolTable();
		CPPUNIT_ASSERT(index[1].lit == index[2].lit);
	}
	
	void testMergeToSelfblocker() {
		// a :- not b.
		// b :- a.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule().addHead(1).addToBody(2, false).endRule()
			.startRule().addHead(2).addToBody(1, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(false, builder.endProgram() && ctx.endInit());
	}
	
	void testMergeToSelfblocker2() {
		// a :- not z.
		// a :- not x.
		// q :- not x.
		// x :- a.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "q").setAtomName(3, "x").setAtomName(4, "z")
			.startRule().addHead(1).addToBody(4, false).endRule()
			.startRule().addHead(1).addToBody(3, false).endRule()
			.startRule().addHead(2).addToBody(3, false).endRule()
			.startRule().addHead(3).addToBody(1, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isTrue(ctx.symbolTable()[1].lit));
		CPPUNIT_ASSERT(ctx.numVars() == 0);
	}

	void testDerivedTAUT() {
		// {y, z}.
		// a :- not z.
		// x :- a.
		// a :- x, y.
		builder.start(ctx)
			.setAtomName(1, "y").setAtomName(2, "z").setAtomName(3, "a").setAtomName(4, "x")
			.startRule(CHOICERULE).addHead(1).addHead(2).endRule()
			.startRule().addHead(3).addToBody(2, false).endRule()
			.startRule().addHead(4).addToBody(3, true).endRule()
			.startRule().addHead(3).addToBody(1, true).addToBody(4, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.numVars() == 2);
	}

	void testOneLoop() {
		// a :- not b.
		// b :- not a.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule().addHead(1).addToBody(2, false).endRule()
			.startRule().addHead(2).addToBody(1, false).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL( 1u, ctx.numVars() );
		CPPUNIT_ASSERT_EQUAL( 0u, ctx.numConstraints() );
		CPPUNIT_ASSERT( ctx.symbolTable()[1].lit == ~ctx.symbolTable()[2].lit );
	}

	void testZeroLoop() {
		// a :- b.
		// b :- a.
		// a :- not x.
		// x :- not a.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "x")
			.startRule().addHead(1).addToBody(2, true).endRule()
			.startRule().addHead(2).addToBody(1, true).endRule()
			.startRule().addHead(1).addToBody(3, false).endRule()
			.startRule().addHead(3).addToBody(1, false).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL( 1u, ctx.numVars() );
		CPPUNIT_ASSERT_EQUAL( 0u, ctx.numConstraints() );
		CPPUNIT_ASSERT( ctx.symbolTable()[1].lit == ctx.symbolTable()[2].lit );
	}

	void testEqSuccs() {
		// {a,b}.
		// c :- a, b.
		// d :- a, b.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "d")
			.startRule(CHOICERULE).addHead(1).addHead(2).endRule()
			.startRule().addHead(3).addToBody(1, true).addToBody(2, true).endRule()
			.startRule().addHead(4).addToBody(1, true).addToBody(2, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL( 3u, ctx.numVars() );
		CPPUNIT_ASSERT_EQUAL( 3u, ctx.numConstraints() );
		CPPUNIT_ASSERT( ctx.symbolTable()[3].lit == ctx.symbolTable()[4].lit );
	}

	void testEqCompute() {
		// {x}.
		// a :- not x.
		// a :- b.
		// b :- a.
		// compute{b}.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "x")
			.startRule(CHOICERULE).addHead(3).endRule()
			.startRule().addHead(1).addToBody(3, false).endRule()
			.startRule().addHead(1).addToBody(2, true).endRule()
			.startRule().addHead(2).addToBody(1, true).endRule()
			.setCompute(2, true);
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isTrue(ctx.symbolTable()[1].lit));
		PrgAtom* a = builder.getAtom(1);
		CPPUNIT_ASSERT(builder.getEqAtom(2) == 1);
		CPPUNIT_ASSERT(a->value() == value_true);
	}

	void testFactsAreAsserted() {
		// a :- not x.
		// y.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "x").setAtomName(3, "y")
			.startRule().addHead(1).addToBody(2, false).endRule()	// dynamic fact
			.startRule().addHead(3).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isTrue(ctx.symbolTable()[1].lit));
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isTrue(ctx.symbolTable()[3].lit));
	}
	void testSelfblockersAreAsserted() {
		// a :- not a.
		// b :- not a.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule().addHead(1).addToBody(1, false).endRule()
			.startRule().addHead(2).addToBody(1, false).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(false, builder.endProgram() && ctx.endInit());
	}
	void testConstraintsAreAsserted() {
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule().addHead(1).addToBody(2, false).endRule()	// a :- not b.
			.startRule().addHead(2).addToBody(1, false).endRule()	// b :- not a.
			.setCompute(1, false)	// force not a
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isFalse(ctx.symbolTable()[1].lit));
	}
	
	void testConflictingCompute() {
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule().addHead(1).addToBody(2, false).endRule()	// a :- not b.
			.startRule().addHead(2).addToBody(1, false).endRule()	// b :- not a.
			.setCompute(1, false)	// force not a
			.setCompute(1, true)	// force a
		;
		CPPUNIT_ASSERT_EQUAL(false, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(!ctx.ok());
	}
	void testForceUnsuppAtomFails() {
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule().addHead(1).addToBody(2, false).endRule()	// a :- not b.
			.setCompute(2, true)	// force b
		;
		CPPUNIT_ASSERT_EQUAL(false, builder.endProgram() && ctx.endInit());
	}

	void testTrivialConflictsAreDeteced() {
		builder.start(ctx)
			.setAtomName(1, "a")
			.startRule().addHead(1).addToBody(1, false).endRule()	// a :- not a.
			.setCompute(1, true)
		;
		CPPUNIT_ASSERT_EQUAL(false, builder.endProgram() && ctx.endInit());

	}
	void testBuildEmpty() {
		builder.start(ctx);
		builder.endProgram();
		builder.write(str);
		CPPUNIT_ASSERT_EQUAL(0u, ctx.numVars());
		CPPUNIT_ASSERT(str.str() == "0\n0\nB+\n0\nB-\n0\n1\n");
	}
	void testAddOneFact() {
		builder.start(ctx);
		builder.startRule().addHead(1).endRule().setAtomName(1, "A");
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT_EQUAL(0u, ctx.numVars());
		builder.write(str);
		std::string lp = "1 1 0 0 \n0\n1 A\n0\nB+\n1\n0\nB-\n0\n1\n";
		CPPUNIT_ASSERT_EQUAL(lp, str.str());

		// a fact does not introduce a constraint, it is just a top-level assignment
		CPPUNIT_ASSERT_EQUAL(0u, ctx.numConstraints());
	}
	
	void testTwoFactsOnlyOneVar() {
		builder.start(ctx)
			.startRule().addHead(1).endRule()
			.startRule().addHead(2).endRule()
			.setAtomName(1, "A").setAtomName(2, "B")
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT_EQUAL(0u, ctx.numVars());
		builder.write(str);
		std::string lp = "1 1 0 0 \n1 2 1 0 1 \n0\n1 A\n2 B\n0\nB+\n1\n0\nB-\n0\n1\n";
		CPPUNIT_ASSERT_EQUAL(lp, str.str());
	}

	void testDontAddOnePredsThatAreNotHeads() {
		// a :- not b, not c.
		// c.
		builder.start(ctx)
			.startRule().addHead(1).addToBody(2, false).addToBody(3, false).endRule()
			.startRule().addHead(3).endRule()
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c")
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT_EQUAL(0u, ctx.numVars());
		builder.write(str);
		std::string lp = "1 3 0 0 \n0\n3 c\n0\nB+\n3\n0\nB-\n0\n1\n"; 
		CPPUNIT_ASSERT_EQUAL(lp, str.str());
	}

	void testDontAddDuplicateBodies() {
		// a :- b, not c.
		// d :- b, not c.
		// b.
		// c.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "d")
			.startRule().addHead(1).addToBody(2, true).addToBody(3, false).endRule()
			.startRule().addHead(4).addToBody(2, true).addToBody(3, false).endRule()
			.startRule().addHead(2).addHead(3).endRule()		
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT_EQUAL(0u, ctx.numVars());
		builder.write(str);
		std::string lp = "1 2 0 0 \n1 3 1 0 2 \n0\n2 b\n3 c\n0\nB+\n2\n0\nB-\n0\n1\n";
		
		CPPUNIT_ASSERT_EQUAL(lp, str.str());
	}

	void testDontAddDuplicateSumBodies() {
		// {a, b, c}.
		// x :- 2 [a=1, b=2, not c=1].
		// y :- 2 [a=1, b=2, not c=1].
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "x").setAtomName(5, "y")
			.startRule(CHOICERULE).addHead(1).addHead(2).addHead(3).endRule()
			.startRule(WEIGHTRULE, 2).addHead(4).addToBody(1, true, 1).addToBody(2, true, 2).addToBody(3, false, 1).endRule()
			.startRule(WEIGHTRULE, 2).addHead(5).addToBody(1, true, 1).addToBody(2, true, 2).addToBody(3, false, 1).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(builder.stats.bodies == 2);	
	}
	void testDontAddDuplicateSimpBodies() {
		// {a, b, c, d}.
		// a :- b, c, d.
		// a :- 8 [c=2, b=3, d=4].
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "d")
			.startRule(CHOICERULE).addHead(1).addHead(2).addHead(3).addHead(4).endRule()
			.startRule().addHead(1).addToBody(2, true).addToBody(3, true).addToBody(4, true).endRule()
			.startRule(WEIGHTRULE, 8).addHead(1).addToBody(3, true, 2).addToBody(2, true, 3).addToBody(4, true, 4).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(builder.stats.bodies == 2);
	}

	void testDontAddUnsupported() {
		// a :- c, b.
		// c :- not d.
		// b :- a.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "d")
			.startRule().addHead(1).addToBody(3, true).addToBody(2, true).endRule()
			.startRule().addHead(3).addToBody(4, false).endRule()
			.startRule().addHead(2).addToBody(1, true).endRule()		
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		builder.write(str);
		std::string lp = "1 3 0 0 \n0";
		CPPUNIT_ASSERT(str.str().find(lp) != std::string::npos);
	}

	void testDontAddUnsupportedNoEq() {
		// a :- c, b.
		// c :- not d.
		// b :- a.
		builder.start(ctx, LogicProgram::AspOptions().noEq())
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "d")
			.startRule().addHead(1).addToBody(3, true).addToBody(2, true).endRule()
			.startRule().addHead(3).addToBody(4, false).endRule()
			.startRule().addHead(2).addToBody(1, true).endRule()		
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(ctx.numVars() <= 2u);
		builder.write(str);
		std::string lp = "1 3 0 0 \n0\n3 c\n0\nB+\n0\nB-\n0\n1\n";
		CPPUNIT_ASSERT_EQUAL(lp, str.str());
	}

	void testDontAddUnsupportedExtNoEq() {
		// a :- not x.
		// c :- a, x.
		// b :- 2 {a, c, not x}.
		// -> 2 {a, c, not x} -> {a}
		builder.start(ctx, LogicProgram::AspOptions().noEq())
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "x")
			.startRule().addHead(1).addToBody(4, false).endRule() // a :- not x
			.startRule().addHead(3).addToBody(1, true).addToBody(4, true).endRule() // c :- a, x
			.startRule(CONSTRAINTRULE, 2).addHead(2).addToBody(1, true).addToBody(3, true).addToBody(4, false).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isFalse(ctx.symbolTable()[3].lit));
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isTrue(ctx.symbolTable()[1].lit));
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isTrue(ctx.symbolTable()[2].lit));
	}

	void testAssertSelfblockers() {
		// a :- b, not c.
		// c :- b, not c.
		// b.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c")
			.startRule().addHead(1).addToBody(2, true).addToBody(3, false).endRule()
			.startRule().addHead(3).addToBody(2, true).addToBody(3, false).endRule()
			.startRule().addHead(2).endRule()		
		;
		// Program is unsat because b must be true and false at the same time.
		CPPUNIT_ASSERT_EQUAL(false, builder.endProgram() && ctx.endInit());
	}

	void testRegressionR1() {
		// q.
		// q :- not p.
		builder.start(ctx)
			.setAtomName(2, "q")
			.startRule().addHead(2).endRule()
			.startRule().addHead(2).addToBody(3, false).endRule()
		;
		// Program is unsat because b must be true and false at the same time.
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(builder.getLiteral(2) == posLit(0));
		CPPUNIT_ASSERT(builder.getLiteral(3) == negLit(0));
		CPPUNIT_ASSERT(ctx.numVars() == 0);
	}

	void testRegressionR2() {
		builder.start(ctx)
			.setAtomName(2, "q")
			.startRule().addHead(2).addToBody(3, false).endRule()
			.startRule().addHead(2).addToBody(4, false).endRule()
			.startRule().addHead(3).addToBody(2, false).endRule()
			.startRule().addHead(4).addToBody(2, false).endRule()
			.startRule().addHead(2).endRule()
		;
		// Program is unsat because b must be true and false at the same time.
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(builder.getLiteral(2) == posLit(0));
		CPPUNIT_ASSERT(builder.getLiteral(3) == negLit(0));
		CPPUNIT_ASSERT(builder.getLiteral(4) == negLit(0));
		CPPUNIT_ASSERT(ctx.numVars() == 0);
	}
	void testFuzzBug() {
		builder.start(ctx)
			.startRule().addHead(1)
			.addToBody(1, false).addToBody(2, false).addToBody(3,false)
			.addToBody(2,false).addToBody(1,false).addToBody(4,false)
			.endRule()
		;
		CPPUNIT_ASSERT_EQUAL(false, builder.endProgram() && ctx.endInit());
	}
	void testBackpropNoEqBug() {
		builder.start(ctx, LogicProgram::AspOptions().noEq().backpropagate());
		Var x[9];
		for (Var i = 1; i != 9; ++i) {
			x[i] = builder.newAtom();
		}
		builder.startRule(CHOICERULE).addHead(x[2]).addHead(x[3]).addHead(x[4]).addToBody(x[5], true).endRule();
		builder.startRule().addHead(x[1]).addToBody(x[7], true).addToBody(x[5], true).endRule();
		builder.startRule().addHead(x[5]).endRule();
		builder.startRule().addHead(x[7]).addToBody(x[2], true).addToBody(x[3], true).endRule();
		builder.startRule().addHead(x[7]).addToBody(x[6], true).endRule();
		builder.startRule().addHead(x[6]).addToBody(x[8], true).endRule();
		builder.startRule().addHead(x[8]).addToBody(x[4], true).endRule();
		builder.setCompute(x[1], false);
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isFalse(builder.getLiteral(x[6])));
	}
	
	void testCloneShare() {
		// {a, b, c}.
		// d :- a, b, c. 
		builder.start(ctx, LogicProgram::AspOptions().noEq()) // no prepro
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "d")
			.startRule(CHOICERULE).addHead(1).addHead(2).addHead(3).endRule()
			.startRule().addHead(4).addToBody(1, true).addToBody(2, true).addToBody(3, true).endRule()
		;
		ctx.setConcurrency(2);
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT( uint32(4) >= ctx.numVars() );
		CPPUNIT_ASSERT( uint32(4) >= ctx.numConstraints() );

		Solver& solver2 = ctx.addSolver();
		ctx.attach(solver2);
		
		CPPUNIT_ASSERT_EQUAL( ctx.numVars(), solver2.numVars() );
		CPPUNIT_ASSERT_EQUAL( ctx.numConstraints(), solver2.numConstraints() );

		CPPUNIT_ASSERT(ctx.isShared());
	}

	void testCloneShareSymbols() {
		// {a, b, c}.
		// d :- a, b, c. 
		builder.start(ctx, LogicProgram::AspOptions().noEq()) // no prepro
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "d")
			.startRule(CHOICERULE).addHead(1).addHead(2).addHead(3).endRule()
			.startRule().addHead(4).addToBody(1, true).addToBody(2, true).addToBody(3, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT( uint32(4) >= ctx.numVars() );
		CPPUNIT_ASSERT( uint32(4) >= ctx.numConstraints() );

		SharedContext ctx2;
		CPPUNIT_ASSERT_EQUAL(true, builder.clone(ctx2, true) && ctx2.endInit());
		CPPUNIT_ASSERT_EQUAL( ctx.numVars(), ctx2.numVars() );
		CPPUNIT_ASSERT_EQUAL( ctx.numConstraints(), ctx2.numConstraints() );
		CPPUNIT_ASSERT(!ctx.isShared());
		CPPUNIT_ASSERT(!ctx2.isShared());
		CPPUNIT_ASSERT( &ctx.symbolTable() == &ctx2.symbolTable() );
	}
	void testCloneFull() {
		// {a, b, c}.
		// d :- a, b, c. 
		builder.start(ctx, LogicProgram::AspOptions().noEq()) // no prepro
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "d")
			.startRule(CHOICERULE).addHead(1).addHead(2).addHead(3).endRule()
			.startRule().addHead(4).addToBody(1, true).addToBody(2, true).addToBody(3, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT( uint32(4) >= ctx.numVars() );
		CPPUNIT_ASSERT( uint32(4) >= ctx.numConstraints() );

		SharedContext ctx2;
		CPPUNIT_ASSERT_EQUAL(true, builder.clone(ctx2) && ctx2.endInit());
		CPPUNIT_ASSERT_EQUAL( ctx.numVars(), ctx2.numVars() );
		CPPUNIT_ASSERT_EQUAL( ctx.numConstraints(), ctx2.numConstraints() );
		CPPUNIT_ASSERT(!ctx.isShared());
		CPPUNIT_ASSERT(!ctx2.isShared());
		CPPUNIT_ASSERT( &ctx.symbolTable() != &ctx2.symbolTable() );
	}

	void testBug() {
		builder.start(ctx)
			.setAtomName(1, "d").setAtomName(2, "c").setAtomName(3, "b").setAtomName(4, "a")
			.startRule().addHead(1).addToBody(2, true).endRule()								// d :- c
			.startRule().addHead(2).addToBody(3, true).addToBody(1, true).endRule() // c :- b, d.
			.startRule().addHead(3).addToBody(4, true).endRule()								// b:-a.
			.startRule().addHead(4).addToBody(3, false).endRule()								// a:-not b.
		;
		CPPUNIT_ASSERT_EQUAL(false, builder.endProgram() && ctx.endInit());
	}

	void testSatBodyBug() {
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "d")
			.startRule(CHOICERULE).addHead(3).addHead(2).addHead(1).endRule()
			.startRule().addHead(1).endRule()		// a.
			.startRule(CONSTRAINTRULE).setBound(1).addHead(2).addToBody(1, true).addToBody(3, true).endRule() // b :- 1 {a, c}.
			.startRule().addHead(4).addToBody(2, true).addToBody(3, true).endRule()
		;
		CPPUNIT_ASSERT(std::distance(builder.getAtom(3)->deps_begin(), builder.getAtom(3)->deps_end()) == 2u);
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(std::distance(builder.getAtom(3)->deps_begin(), builder.getAtom(3)->deps_end()) == 1u);
		CPPUNIT_ASSERT(std::distance(builder.getAtom(2)->deps_begin(), builder.getAtom(2)->deps_end()) == 0u);
		CPPUNIT_ASSERT_EQUAL(value_free, ctx.master()->value(ctx.symbolTable()[3].lit.var()));
	}
	void testDepBodyBug() {
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "x").setAtomName(5, "y").setAtomName(6, "z")
			.startRule(CHOICERULE).addHead(4).addHead(5).addHead(6).endRule()
			.startRule().addHead(1).addToBody(4, true).addToBody(5, true).endRule()
			.startRule().addHead(2).addToBody(1, true).endRule()
			.startRule().addHead(3).addToBody(2, true).addToBody(6, true).addToBody(1, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT((builder.getAtom(1)->deps_end() - builder.getAtom(1)->deps_begin()) == 2);
	}

	void testAddUnknownAtomToMinimize() {
		builder.start(ctx)
			.startRule(OPTIMIZERULE).addToBody(1, true, 1).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(true, builder.hasMinimize());
	}

	void testWriteWeakTrue() {
		// {z}.
		// x :- not y, z.
		// y :- not x.
		// compute{x}.
		builder.start(ctx)
			.setAtomName(1, "x").setAtomName(2, "y").setAtomName(3, "z")
			.startRule(CHOICERULE).addHead(3).endRule()
			.startRule().addHead(1).addToBody(2, false).addToBody(3, true).endRule()
			.startRule().addHead(2).addToBody(1, false).endRule()
			.setCompute(1, true)
		; 
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		builder.write(str);
		std::string bp("B+\n1\n");
		CPPUNIT_ASSERT(str.str().find(bp) != std::string::npos);
	}

	void testSimplifyBodyEqBug() {
		// {x,y,z}.
		// a :- x,z.
		// b :- x,z.
		// c :- a, y, b.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "x").setAtomName(5, "y").setAtomName(6, "z")
			.startRule(CHOICERULE).addHead(4).addHead(5).addHead(6).endRule()
			.startRule().addHead(1).addToBody(4, true).addToBody(6, true).endRule()
			.startRule().addHead(2).addToBody(4, true).addToBody(6, true).endRule()
			.startRule().addHead(3).addToBody(1, true).addToBody(5, true).addToBody(2, true).endRule()
		; 
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		PrgAtom* a = builder.getAtom(1);
		PrgAtom* b = builder.getAtom(2);
		CPPUNIT_ASSERT(b->eq() && b->id() == 1);
		CPPUNIT_ASSERT((a->deps_end() - a->deps_begin()) == 1);
	}

	void testNoEqSameLitBug() {
		// {x,y}.
		// a :- x,y.
		// b :- x,y.
		// c :- a, b.
		builder.start(ctx, LogicProgram::AspOptions().noEq())
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "x").setAtomName(5, "y")
			.startRule(CHOICERULE).addHead(4).addHead(5).endRule()
			.startRule().addHead(1).addToBody(4, true).addToBody(5, true).endRule()
			.startRule().addHead(2).addToBody(4, true).addToBody(5, true).endRule()
			.startRule().addHead(3).addToBody(1, true).addToBody(2, true).endRule()
		; 
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.numTernary() == 1);
	}

	void testAssertEqSelfblocker() {
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "x").setAtomName(3, "y").setAtomName(4, "q").setAtomName(5, "r")
			.startRule().addHead(1).addToBody(2, false).addToBody(3, false).endRule()	// a :- not x, not y.
			.startRule().addHead(1).addToBody(4, false).addToBody(5, false).endRule()	// a :- not q, not r.
			.startRule().addHead(2).addToBody(3, false).endRule() // x :- not y.
			.startRule().addHead(3).addToBody(2, false).endRule()	// y :- not x.
			.startRule().addHead(4).addToBody(5, false).endRule() // q :- not r.
			.startRule().addHead(5).addToBody(4, false).endRule()	// r :- not q.								
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(2u, ctx.numVars());
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isFalse(ctx.symbolTable()[1].lit));
	}

	void testAddClauses() {
		ClauseObserver* o = new ClauseObserver;
		ctx.master()->setHeuristic(o);
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c")
			.startRule().addHead(1).addToBody(2, false).endRule()								// a :- not b.
			.startRule().addHead(1).addToBody(2, true).addToBody(3, true).endRule() // a :- b, c.
			.startRule().addHead(2).addToBody(1, false).endRule()								// b :- not a.
			.startRule().addHead(3).addToBody(2, false).endRule()								// c :- not b.
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(3u, ctx.numVars());
		CPPUNIT_ASSERT_EQUAL(0u, ctx.master()->numAssignedVars());
	
		CPPUNIT_ASSERT_EQUAL(8u, ctx.numConstraints());

		Var bodyNotB = 1;
		Var bodyBC = 3;
		CPPUNIT_ASSERT_EQUAL(Var_t::body_var, ctx.varInfo(3).type());
		Literal a = ctx.symbolTable()[1].lit;
		CPPUNIT_ASSERT(ctx.symbolTable()[2].lit == ~ctx.symbolTable()[1].lit);

		// a - HeadClauses
		ClauseObserver::Clause ac;
		ac.push_back(~a);
		ac.push_back(posLit(bodyNotB));
		ac.push_back(posLit(bodyBC));
		std::sort(ac.begin(), ac.end());
		CPPUNIT_ASSERT(std::find(o->clauses_.begin(), o->clauses_.end(), ac) != o->clauses_.end());
		
		// bodyNotB - Body clauses
		ClauseObserver::Clause cl;
		cl.push_back(negLit(bodyNotB)); cl.push_back(~ctx.symbolTable()[2].lit);
		std::sort(cl.begin(), cl.end());
		CPPUNIT_ASSERT(std::find(o->clauses_.begin(), o->clauses_.end(), cl) != o->clauses_.end());
		cl.clear();
		cl.push_back(posLit(bodyNotB)); cl.push_back(ctx.symbolTable()[2].lit);
		std::sort(cl.begin(), cl.end());
		CPPUNIT_ASSERT(std::find(o->clauses_.begin(), o->clauses_.end(), cl) != o->clauses_.end());
		cl.clear();
		cl.push_back(negLit(bodyNotB)); cl.push_back(a);
		std::sort(cl.begin(), cl.end());
		CPPUNIT_ASSERT(std::find(o->clauses_.begin(), o->clauses_.end(), cl) != o->clauses_.end());
		
		// bodyBC - Body clauses
		cl.clear();
		cl.push_back(negLit(bodyBC)); cl.push_back(ctx.symbolTable()[2].lit);
		std::sort(cl.begin(), cl.end());
		CPPUNIT_ASSERT(std::find(o->clauses_.begin(), o->clauses_.end(), cl) != o->clauses_.end());
		cl.clear();
		cl.push_back(negLit(bodyBC)); cl.push_back(ctx.symbolTable()[3].lit);
		std::sort(cl.begin(), cl.end());
		CPPUNIT_ASSERT(std::find(o->clauses_.begin(), o->clauses_.end(), cl) != o->clauses_.end());
		cl.clear();
		cl.push_back(posLit(bodyBC)); cl.push_back(~ctx.symbolTable()[2].lit); cl.push_back(~ctx.symbolTable()[3].lit);
		std::sort(cl.begin(), cl.end());
		CPPUNIT_ASSERT(std::find(o->clauses_.begin(), o->clauses_.end(), cl) != o->clauses_.end());
		cl.clear();
		cl.push_back(negLit(bodyBC)); cl.push_back(a);
		std::sort(cl.begin(), cl.end());
		CPPUNIT_ASSERT(std::find(o->clauses_.begin(), o->clauses_.end(), cl) != o->clauses_.end());
	}

	void testAddCardConstraint() {
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "d")
			// a :- 1 { not b, c, d }
			// {b,c}.
			.startRule(CONSTRAINTRULE).setBound(1).addHead(1).addToBody(2, false).addToBody(3, true).addToBody(4, true).endRule()
			.startRule(CHOICERULE).addHead(2).addHead(3).endRule();
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT_EQUAL(3u, ctx.numVars());

		builder.write(str);
		std::string exp = "2 1 2 1 1 2 3 \n3 2 2 3 0 0 \n0\n1 a\n2 b\n3 c\n0\nB+\n0\nB-\n0\n1\n";
		CPPUNIT_ASSERT_EQUAL(exp, str.str());		
	}

	void testAddWeightConstraint() {
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "d")
			// a :- 2 [not b=1, c=2, d=2 ]
			.startRule(WEIGHTRULE).setBound(2).addHead(1).addToBody(2, false, 1).addToBody(3, true, 2).addToBody(4, true, 2).endRule()
			.startRule(CHOICERULE).addHead(2).addHead(3).endRule();
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT_EQUAL(3u, ctx.numVars());

		builder.write(str);
		std::string exp = "5 1 2 2 1 2 3 1 2 \n3 2 2 3 0 0 \n0\n1 a\n2 b\n3 c\n0\nB+\n0\nB-\n0\n1\n";
		CPPUNIT_ASSERT_EQUAL(exp, str.str());		
	}
	void testAddMinimizeConstraint() {
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule(BASICRULE).addHead(1).addToBody(2, false).endRule()
			.startRule(BASICRULE).addHead(2).addToBody(1, false).endRule()
			.startRule(OPTIMIZERULE).addToBody(1, true).endRule()
			.startRule(OPTIMIZERULE).addToBody(2, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		builder.write(str);
		std::stringstream exp; 
		exp
			<< "6 0 1 0 1 1 \n"
			<< "6 0 1 0 2 1 \n"
			<< "1 1 1 1 2 \n"
			<< "1 2 1 1 1 \n"
			<< "0\n1 a\n2 b\n0\nB+\n0\nB-\n0\n1\n";
		CPPUNIT_ASSERT_EQUAL(exp.str(), str.str());
	}
	void testAddEmptyMinimizeConstraint() {
		builder.start(ctx)
			.startRule(OPTIMIZERULE).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(builder.getMinimizeConstraint() != 0);
	}

	void testNonTight() {
		// p :- q.
		// q :- p.
		// p :- not a.
		// q :- not a.
		// a :- not p.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "p").setAtomName(3, "q")
			.startRule().addHead(2).addToBody(3, true).endRule()
			.startRule().addHead(3).addToBody(2, true).endRule()
			.startRule().addHead(2).addToBody(1, false).endRule()
			.startRule().addHead(3).addToBody(1, false).endRule()
			.startRule().addHead(1).addToBody(2, false).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT( builder.stats.sccs != 0 );
	}

	void testIgnoreCondFactsInLoops() {
		// {a}.
		// b :- a.
		// a :- b.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule(CHOICERULE).addHead(1).endRule()
			.startRule().addHead(2).addToBody(1, true).endRule()
			.startRule().addHead(1).addToBody(2, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT( builder.stats.sccs == 0);
	}

	void testCrEqBug() {
		// a.
		// {b}.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule().addHead(1).endRule()
			.startRule(CHOICERULE).addHead(2).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(1u, ctx.numVars());
		CPPUNIT_ASSERT_EQUAL(value_free, ctx.master()->value(ctx.symbolTable()[2].lit.var()));
	}

	void testEqOverChoiceRule() {
		// {a}.
		// b :- a.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule(CHOICERULE).addHead(1).endRule()
			.startRule().addHead(2).addToBody(1, true).endRule()	
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT_EQUAL(1u, ctx.numVars());
		builder.write(str);
		std::stringstream exp; 
		exp
			<< "3 1 1 0 0 \n"
			<< "1 2 1 0 1 \n"
			<< "0\n1 a\n2 b\n0\nB+\n0\nB-\n0\n1\n";
		CPPUNIT_ASSERT_EQUAL(exp.str(), str.str());
	}

	void testEqOverComp() {
		// x1 :- not x2.
		// x1 :- x2.
		// x2 :- not x3.
		// x3 :- not x1.
		builder.start(ctx)
			.setAtomName(1, "x1").setAtomName(2, "x2").setAtomName(3, "x3")
			.startRule().addHead(1).addToBody(2, false).endRule()
			.startRule().addHead(1).addToBody(2, true).endRule()
			.startRule().addHead(2).addToBody(3, false).endRule()
			.startRule().addHead(3).addToBody(1, false).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT_EQUAL(ctx.symbolTable()[1].lit, ctx.symbolTable()[2].lit);
		CPPUNIT_ASSERT(ctx.master()->numFreeVars() == 0 && ctx.master()->isTrue(ctx.symbolTable()[1].lit));
	}

	void testEqOverBodiesOfDiffType() {
		builder.start(ctx)
			.setAtomName(1, "z").setAtomName(2, "y").setAtomName(3, "x").setAtomName(4, "t")
			.startRule(CHOICERULE).addHead(1).addHead(2).endRule() // {z,y}
			.startRule(CONSTRAINTRULE,2).addHead(4).addToBody(1,true).addToBody(2,true).addToBody(3,true).endRule()
			.startRule().addHead(3).addToBody(4,true).endRule()
			.setCompute(2, false)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(3u >= ctx.numVars());
		CPPUNIT_ASSERT(ctx.master()->isFalse(ctx.symbolTable()[2].lit));
		CPPUNIT_ASSERT(ctx.master()->isFalse(ctx.symbolTable()[3].lit));
		CPPUNIT_ASSERT(ctx.master()->isFalse(ctx.symbolTable()[4].lit));
	}


	void testNoBodyUnification() {
		// {x, y, z}.
		// p :- x, s.
		// p :- y.
		// q :- not p.
		// r :- not q.
		// s :- p.
		// s :- z. 
		builder.start(ctx)
			.setAtomName(1, "x").setAtomName(2, "y").setAtomName(3, "z")
			.setAtomName(4, "p").setAtomName(5, "q").setAtomName(6, "r").setAtomName(7, "s")
			.startRule(CHOICERULE).addHead(1).addHead(2).addHead(3).endRule()
			.startRule().addHead(4).addToBody(1, true).addToBody(7,true).endRule()
			.startRule().addHead(4).addToBody(2, true).endRule()
			.startRule().addHead(5).addToBody(4, false).endRule()
			.startRule().addHead(6).addToBody(5, false).endRule()
			.startRule().addHead(7).addToBody(4, true).endRule()
			.startRule().addHead(7).addToBody(3, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		ctx.master()->addPost(new DefaultUnfoundedCheck());
		CPPUNIT_ASSERT_EQUAL(true, ctx.endInit());
		ctx.master()->assume(~ctx.symbolTable()[2].lit);	// ~y
		ctx.master()->propagate();
		ctx.master()->assume(~ctx.symbolTable()[3].lit);	// ~z
		ctx.master()->propagate();
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isFalse(ctx.symbolTable()[7].lit));
	}

	void testNoEqAtomReplacement() {
		// {x, y}.
		// p :- x.
		// p :- y.
		// q :- not p.
		// r :- not q.
		builder.start(ctx)
			.setAtomName(1, "x").setAtomName(2, "y").setAtomName(3, "p")
			.setAtomName(4, "q").setAtomName(5, "r")
			.startRule(CHOICERULE).addHead(1).addHead(2).endRule()
			.startRule().addHead(3).addToBody(1, true).endRule()
			.startRule().addHead(3).addToBody(2, true).endRule()
			.startRule().addHead(4).addToBody(3, false).endRule()
			.startRule().addHead(5).addToBody(4, false).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		ctx.master()->assume(~ctx.symbolTable()[1].lit);	// ~x
		ctx.master()->propagate();
		ctx.master()->assume(~ctx.symbolTable()[2].lit);	// ~y
		ctx.master()->propagate();
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isFalse(ctx.symbolTable()[3].lit));
	}

	void testAllBodiesSameLit() {
		// {z}.
		// r :- not z.
		// q :- not r.
		// s :- r.
		// s :- not q.
		// r :- s.
		builder.start(ctx)
			.setAtomName(1, "z").setAtomName(2, "r").setAtomName(3, "q").setAtomName(4, "s")
			.startRule(CHOICERULE).addHead(1).endRule()
			.startRule().addHead(2).addToBody(1, false).endRule()
			.startRule().addHead(3).addToBody(2, false).endRule()
			.startRule().addHead(4).addToBody(2, true).endRule()
			.startRule().addHead(4).addToBody(3, false).endRule()
			.startRule().addHead(2).addToBody(4, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(ctx.symbolTable()[2].lit, ctx.symbolTable()[4].lit);
		CPPUNIT_ASSERT(ctx.symbolTable()[1].lit != ctx.symbolTable()[3].lit);
		ctx.master()->assume(ctx.symbolTable()[1].lit) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->value(ctx.symbolTable()[3].lit.var()) == value_free);
		ctx.master()->assume(~ctx.symbolTable()[3].lit) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->numFreeVars() == 0 && ctx.master()->isTrue(ctx.symbolTable()[2].lit));
	}

	void testAllBodiesSameLit2() {
		// {z, y}.
		// r :- not z.
		// q :- not r.
		// s :- r.
		// s :- not q.
		// r :- s, y.
		builder.start(ctx)
			.setAtomName(1, "z").setAtomName(2, "r").setAtomName(3, "q").setAtomName(4, "s").setAtomName(5, "y")
			.startRule(CHOICERULE).addHead(1).addHead(5).endRule()
			.startRule().addHead(2).addToBody(1, false).endRule()
			.startRule().addHead(3).addToBody(2, false).endRule()
			.startRule().addHead(4).addToBody(2, true).endRule()
			.startRule().addHead(4).addToBody(3, false).endRule()
			.startRule().addHead(2).addToBody(4, true).addToBody(5, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(ctx.symbolTable()[2].lit, ctx.symbolTable()[4].lit);
		CPPUNIT_ASSERT(ctx.symbolTable()[1].lit != ctx.symbolTable()[3].lit);
		ctx.master()->assume(ctx.symbolTable()[1].lit) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->value(ctx.symbolTable()[3].lit.var()) == value_free);
		ctx.master()->assume(~ctx.symbolTable()[3].lit) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->numFreeVars() == 0 && ctx.master()->isTrue(ctx.symbolTable()[2].lit));
		CPPUNIT_ASSERT(ctx.numVars() == 4);
	}
	
	void testCompLit() {
		// {y}.
		// a :- not x.
		// x :- not a.
		// b :- a, x.
		// c :- a, y, not x
		// -> a == ~x -> {a,x} = F -> {a, not x} = {a, y}
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "x").setAtomName(4, "y").setAtomName(5, "c")
			.startRule(CHOICERULE).addHead(4).endRule()
			.startRule().addHead(1).addToBody(3, false).endRule()
			.startRule().addHead(3).addToBody(1, false).endRule()
			.startRule().addHead(2).addToBody(1, true).addToBody(3, true).endRule()
			.startRule().addHead(5).addToBody(1, true).addToBody(4, true).addToBody(3, false).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(3u, ctx.numVars());
		CPPUNIT_ASSERT(ctx.master()->isFalse(ctx.symbolTable()[2].lit));
	}

	void testFunnySelfblockerOverEqByTwo() {
		// {x,y,z}.
		// q :- x, y.
		// d :- x, y.
		// c :- y, z.
		// a :- y, z.
		// c :- q, not c.
		// r :- d, not a.
		// s :- x, r.
		// -> q == d, c == a -> {d, not a} == {q, not c} -> F
		// -> r == s are both unsupported!
		builder.start(ctx)
			.setAtomName(1, "x").setAtomName(2, "y").setAtomName(3, "z").setAtomName(4, "q")
			.setAtomName(5, "d").setAtomName(6, "c").setAtomName(7, "a").setAtomName(8, "r").setAtomName(9, "s")
			.startRule(CHOICERULE).addHead(1).addHead(2).addHead(3).endRule()
			.startRule().addHead(4).addToBody(1, true).addToBody(2,true).endRule()
			.startRule().addHead(5).addToBody(1, true).addToBody(2,true).endRule()
			.startRule().addHead(6).addToBody(2, true).addToBody(3,true).endRule()
			.startRule().addHead(7).addToBody(2, true).addToBody(3,true).endRule()
			.startRule().addHead(6).addToBody(4, true).addToBody(6, false).endRule()
			.startRule().addHead(8).addToBody(5, true).addToBody(7, false).endRule()
			.startRule().addHead(9).addToBody(1, true).addToBody(8, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.master()->isFalse(ctx.symbolTable()[8].lit));
		CPPUNIT_ASSERT(ctx.master()->isFalse(ctx.symbolTable()[9].lit));
	}
	
	void testRemoveKnownAtomFromWeightRule() {
		// {q, r}.
		// a.
		// x :- 5 [a = 2, not b = 2, q = 1, r = 1].
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "q").setAtomName(4, "r").setAtomName(5, "x")
			.startRule(CHOICERULE).addHead(3).addHead(4).endRule()
			.startRule().addHead(1).endRule()
			.startRule(WEIGHTRULE).addHead(5).setBound(5).addToBody(1, true,2).addToBody(2, false,2).addToBody(3, true).addToBody(4, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		builder.write(str);
		// {q, r}.
		// a. 
		// x :- 1 [ q=1, r=1 ].
		std::stringstream exp; 
		exp
			<< "1 1 0 0 \n"
			<< "3 2 3 4 0 0 \n"
			<< "5 5 1 2 0 3 4 1 1 \n"
			<< "0\n1 a\n3 q\n4 r\n5 x\n0\nB+\n1\n0\nB-\n0\n1\n";
		CPPUNIT_ASSERT_EQUAL(exp.str(), str.str());
	}

	void testMergeEquivalentAtomsInConstraintRule() {
		// {a, c}.
		// a :- b.
		// b :- a.
		// x :-  2 {a, b, c}.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "x")
			.startRule(CHOICERULE).addHead(1).addHead(3).endRule()
			.startRule().addHead(1).addToBody(2, true).endRule()
			.startRule().addHead(2).addToBody(1, true).endRule()
			.startRule(CONSTRAINTRULE).addHead(4).setBound(2).addToBody(1, true).addToBody(2, true).addToBody(3, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		builder.write(str);
		std::string x = str.str();
		// x :-  2 [a=2, c].
		CPPUNIT_ASSERT(x.find("5 4 2 2 0 1 3 2 1") != std::string::npos);
	}

	void testMergeEquivalentAtomsInWeightRule() {
		// {a, c, d}.
		// a :- b.
		// b :- a.
		// x :-  3 [a = 1, c = 4, b = 2, d=1].
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "x").setAtomName(5, "d")
			.startRule(CHOICERULE).addHead(1).addHead(3).addHead(5).endRule()
			.startRule().addHead(1).addToBody(2, true).endRule()
			.startRule().addHead(2).addToBody(1, true).endRule()
			.startRule(WEIGHTRULE).addHead(4).setBound(3).addToBody(1, true,1).addToBody(3, true,4).addToBody(2, true,2).addToBody(5, true, 1).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		builder.write(str);
		std::string x = str.str();
		// x :-  3 [a=3, c=3,d=1].
		CPPUNIT_ASSERT(x.find("5 4 3 3 0 1 3 5 3 3 1") != std::string::npos);
	}


	void testBothLitsInConstraintRule() {
		// {a}.
		// b :- a.
		// c :- b.
		// x :-  1 {a, b, not b, not c}.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "x")
			.startRule(CHOICERULE).addHead(1).endRule()
			.startRule().addHead(2).addToBody(1, true).endRule()
			.startRule().addHead(3).addToBody(2, true).endRule()
			.startRule(CONSTRAINTRULE).addHead(4).setBound(1).addToBody(1, true).addToBody(2, false).addToBody(2, true,2).addToBody(3,false).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		builder.write(str);
		std::string x = str.str();
		// x :-  1 [a=2, not a=2].
		CPPUNIT_ASSERT(x.find("5 4 1 2 1 1 1 2 2") != std::string::npos);
	}

	void testBothLitsInWeightRule() {
		// {a, d}.
		// b :- a.
		// c :- b.
		// x :-  3 [a=3, not b=1, not c=3, d=2].
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "x").setAtomName(5, "d")
			.startRule(CHOICERULE).addHead(1).addHead(5).endRule()
			.startRule().addHead(2).addToBody(1, true).endRule()
			.startRule().addHead(3).addToBody(2, true).endRule()
			.startRule(WEIGHTRULE).addHead(4).setBound(3).addToBody(1, true,3).addToBody(2, false,1).addToBody(3,false,3).addToBody(5, true, 2).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		builder.write(str);
		std::string x = str.str();
		// x :-  3 [a=3, not a=4, d=2].
		CPPUNIT_ASSERT(x.find("5 4 3 3 1 1 1 5 4 3 2") != std::string::npos);
	}

	void testWeightlessAtomsInWeightRule() {
		// {a, b, c}.
		// x :-  1 [a=1, b=1, c=0].
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "x")
			.startRule(CHOICERULE).addHead(1).addHead(2).addHead(3).endRule()
			.startRule(WEIGHTRULE).addHead(4).setBound(1).addToBody(1, true,1).addToBody(2, true,1).addToBody(3,true,0).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		builder.write(str);
		std::string x = str.str();
		// x :-  1 {a, b}.
		CPPUNIT_ASSERT(x.find("2 4 2 0 1 1 2 ") != std::string::npos);
	}

	void testSimplifyToNormal() {
		// {a}.
		// b :-  2 [a=2,not c=1].
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c")
			.startRule(CHOICERULE).addHead(1).endRule()
			.startRule(WEIGHTRULE).addHead(2).setBound(2).addToBody(1, true,2).addToBody(3, false,1).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		builder.write(str);
		std::string x = str.str();
		// b :-  a.
		CPPUNIT_ASSERT(x.find("1 2 1 0 1 ") != std::string::npos);
	}

	void testSimplifyToCardBug() {
		// x1.
		// x2.
		// t :- 168 [not x1 = 576, not x2=381].
		// compute { not t }.
		builder.start(ctx)
			.setAtomName(1, "x1").setAtomName(2, "x2").setAtomName(3, "t")
			.startRule().addHead(1).addHead(2).endRule()
			.startRule(WEIGHTRULE).addHead(3).setBound(168).addToBody(1,false,576).addToBody(2,false,381).endRule()
			.setCompute(3, false)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(ctx.master()->numFreeVars() == 0);
	}

	void testSimplifyCompBug() {
		// x1 :- not x2.
		// x1 :- x2.
		// x2 :- not x3.
		// x3 :- not x1.
		// a. b. f.
		// x4 :- a, b, x2, e, f.
		builder.start(ctx, LogicProgram::AspOptions().iterations(1))
			.setAtomName(1, "x1").setAtomName(2, "x2").setAtomName(3, "x3")
			.setAtomName(4, "a").setAtomName(5, "b").setAtomName(6, "e").setAtomName(7, "f")
			.startRule().addHead(1).addToBody(2, false).endRule()
			.startRule().addHead(1).addToBody(2, true).endRule()
			.startRule().addHead(2).addToBody(3, false).endRule()
			.startRule().addHead(3).addToBody(1, false).endRule()
			.startRule().addHead(4).addHead(5).addHead(7).endRule()
			.startRule(CHOICERULE).addHead(6).endRule()
			.startRule().addHead(8).addToBody(4, true).addToBody(5, true).addToBody(2, true).addToBody(6, true).addToBody(7, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		PrgAtom* x = builder.getAtom(8);
		PrgBody* B = builder.getBody(x->supps_begin()->node());
		CPPUNIT_ASSERT(B->size() == 2 && !B->goal(0).sign() && B->goal(1).sign());
		CPPUNIT_ASSERT(B->goal(0).var() == 6);
		CPPUNIT_ASSERT(B->goal(1).var() == 3);
	}

	void testBPWeight() {
		// {a, b, c, d}.
		// x :-  2 [a=1, b=2, not c=2, d=1].
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "d").setAtomName(5, "x")
			.startRule(CHOICERULE).addHead(1).addHead(2).addHead(3).addHead(4).endRule()
			.startRule(WEIGHTRULE).addHead(5).setBound(2).addToBody(1, true,1).addToBody(2, true,2).addToBody(3,false,2).addToBody(4, true, 1).endRule()
			.setCompute(5, false)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isFalse(ctx.symbolTable()[2].lit));
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isTrue(ctx.symbolTable()[3].lit));
	}

	void testExtLitsAreFrozen() {
		// {a, b, c, d, e, f, g}.
		// x :- 2 {b, c, d}.
		// y :- 2 [c=1, d=2, e=1].
		// minimize {f, g}.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c")
			.setAtomName(4, "d").setAtomName(5, "e").setAtomName(6, "f")
			.setAtomName(7, "g").setAtomName(8, "x").setAtomName(9, "y")
			.startRule(CHOICERULE).addHead(1).addHead(2).addHead(3).addHead(4).addHead(5).addHead(6).addHead(7).endRule()
			.startRule(CONSTRAINTRULE,2).addHead(8).addToBody(2, true).addToBody(3,true).addToBody(4, true).endRule()
			.startRule(WEIGHTRULE,2).addHead(9).addToBody(3, true,1).addToBody(4,true,2).addToBody(5, true,1).endRule()
			.startRule(OPTIMIZERULE).addToBody(6,true).addToBody(7,true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT_EQUAL(false, ctx.varInfo(ctx.symbolTable()[1].lit.var()).frozen());
		CPPUNIT_ASSERT_EQUAL(true, ctx.varInfo(ctx.symbolTable()[2].lit.var()).frozen());
		CPPUNIT_ASSERT_EQUAL(true, ctx.varInfo(ctx.symbolTable()[3].lit.var()).frozen());
		CPPUNIT_ASSERT_EQUAL(true, ctx.varInfo(ctx.symbolTable()[4].lit.var()).frozen());
		CPPUNIT_ASSERT_EQUAL(true, ctx.varInfo(ctx.symbolTable()[5].lit.var()).frozen());
		CPPUNIT_ASSERT_EQUAL(true, ctx.varInfo(ctx.symbolTable()[8].lit.var()).frozen());
		CPPUNIT_ASSERT_EQUAL(true, ctx.varInfo(ctx.symbolTable()[9].lit.var()).frozen());

		// minimize lits only frozen if constraint is actually used
		CPPUNIT_ASSERT_EQUAL(false, ctx.varInfo(ctx.symbolTable()[6].lit.var()).frozen());
		CPPUNIT_ASSERT_EQUAL(false, ctx.varInfo(ctx.symbolTable()[7].lit.var()).frozen());
		builder.getMinimizeConstraint();
		CPPUNIT_ASSERT_EQUAL(true, ctx.varInfo(ctx.symbolTable()[6].lit.var()).frozen());
		CPPUNIT_ASSERT_EQUAL(true, ctx.varInfo(ctx.symbolTable()[7].lit.var()).frozen());
	}

	void writeIntegrityConstraint() {
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "x")
			.startRule(CHOICERULE).addHead(1).addHead(2).addHead(3).endRule()
			.startRule(BASICRULE).addHead(1).addToBody(3, true).addToBody(2, false).endRule()
			.startRule(BASICRULE).addHead(2).addToBody(3, true).addToBody(2, false).endRule();
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		
		builder.write(str);
		
		// falseAtom :- x, not b.
		CPPUNIT_ASSERT(str.str().find("1 4 2 1 2 3") != std::string::npos);
		// compute {not falseAtom}.
		CPPUNIT_ASSERT(str.str().find("B-\n4") != std::string::npos);
	}

	void testComputeTrueBug() {
		// a :- not b.
		// b :- a.
		// a :- y.
		// y :- a.
		// compute{a}.
		builder.start(ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "y")
			.startRule().addHead(1).addToBody(2, false).endRule()
			.startRule().addHead(2).addToBody(1, true).endRule()
			.startRule().addHead(1).addToBody(3, true).endRule()
			.startRule().addHead(3).addToBody(1, true).endRule()
			.setCompute(1, true)
		;
		CPPUNIT_ASSERT_EQUAL(false, builder.endProgram() && ctx.endInit());
	}

	void testBackprop() {
		builder.start(ctx, LogicProgram::AspOptions().backpropagate())
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "d")
			.setAtomName(5, "x").setAtomName(6, "y").setAtomName(7, "z").setAtomName(8, "_false")
			.startRule(CHOICERULE).addHead(5).addHead(6).addHead(7).endRule()       // {x,y,z}.
			.startRule().addHead(4).addToBody(5, true).addToBody(1, true).endRule() // d :- x,a
			.startRule().addHead(1).addToBody(6, true).addToBody(4, true).endRule() // a :- y,d
			.startRule().addHead(2).addToBody(5, true).addToBody(7, true).endRule() // b :- x,z
			.startRule().addHead(3).addToBody(6, true).addToBody(7, true).endRule() // c :- y,z
			.startRule().addHead(8).addToBody(5, true).addToBody(4, false).endRule() //  :- x,not d
			.startRule().addHead(8).addToBody(6, true).addToBody(2, false).endRule() //  :- y,not b
			.startRule().addHead(8).addToBody(7, true).addToBody(3, false).endRule() //  :- z,not c
			.setCompute(8, false)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.numVars() == 0);
	}

	void testBackpropTrueCon() {
		Var r, s, x, y, a, t;
		builder.start(ctx, LogicProgram::AspOptions().backpropagate())
			.setAtomName(r = 2, "r").setAtomName(s = 3, "s").setAtomName(x=4, "x").setAtomName(a=5, "a").setAtomName(y=6, "y").setAtomName(t=7, "t")
			.startRule().addHead(t).endRule() // t.
			.startRule(CHOICERULE).addHead(r).addHead(s).endRule() // {r,s}.
			.startRule().addHead(x).addToBody(y, false).endRule()  // x :- not y.
			.startRule().addHead(1).addToBody(a, false).endRule()  // :- not a.
			.startRule(CONSTRAINTRULE, 1).addHead(a).addToBody(r, false).addToBody(s, false).endRule() // a :- 1 {not r, not s}.
			.setCompute(1, false)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		ctx.master()->assume(builder.getLiteral(r)) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(builder.getLiteral(s)));
		ctx.master()->undoUntil(0);
		ctx.master()->assume(builder.getLiteral(s)) && ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(builder.getLiteral(r)));
	}
	void testBackpropWrite() {
		builder.start(ctx, LogicProgram::AspOptions().backpropagate())
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "d").setAtomName(5, "_FAIL")
			.startRule(DISJUNCTIVERULE).addHead(1).addHead(2).endRule()       // a | b.
			.startRule().addHead(3).addToBody(1, true).endRule() // c :- a.
			.startRule().addHead(1).addToBody(3, true).endRule() // a :- c.
			.startRule().addHead(4).addToBody(3, false).endRule() // d :- not c.
			.startRule().addHead(5).addToBody(1, true).addToBody(3, true).endRule() // _FAIL :- a,c.
			.setCompute(5, false)
			;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.numVars() == 0);
		CPPUNIT_ASSERT(ctx.master()->isFalse(builder.getLiteral(1)));
		CPPUNIT_ASSERT(ctx.master()->isFalse(builder.getLiteral(3)));
		CPPUNIT_ASSERT(ctx.master()->isTrue(builder.getLiteral(2)));
		CPPUNIT_ASSERT(ctx.master()->isTrue(builder.getLiteral(4)));
		builder.write(str);
		std::string x = str.str();
		CPPUNIT_ASSERT(x.find("1 2 0 0") != std::string::npos || x.find("1 2 1 0 4"));
		CPPUNIT_ASSERT(x.find("1 4 0 0") != std::string::npos || x.find("1 4 1 0 2"));
		CPPUNIT_ASSERT(x.find("1 1") == std::string::npos);
		CPPUNIT_ASSERT(x.find("1 3") == std::string::npos);
	}

	void testSimpleIncremental() {
		builder.start(ctx);
		// I1: 
		// a :- not b.
		// b :- not a.
		builder.updateProgram();
		builder.setAtomName(1, "a").setAtomName(2, "b")
			.startRule().addHead(1).addToBody(2, false).endRule()
			.startRule().addHead(2).addToBody(1, false).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.numVars() == 1);
		CPPUNIT_ASSERT(ctx.symbolTable()[1].lit == ~ctx.symbolTable()[2].lit);
	
		// I2: 
		// c :- a, not d.
		// d :- b, not c.
		// x :- d.
		builder.updateProgram();
		builder.setAtomName(3, "c").setAtomName(4, "d").setAtomName(5, "x")
			.startRule().addHead(3).addToBody(1, true).addToBody(4, false).endRule()
			.startRule().addHead(4).addToBody(2, true).addToBody(3, false).endRule()
			.startRule().addHead(5).addToBody(4, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.numVars() == 3);
		CPPUNIT_ASSERT(ctx.symbolTable()[1].lit == ~ctx.symbolTable()[2].lit);
		CPPUNIT_ASSERT(ctx.symbolTable()[5].lit == ctx.symbolTable()[4].lit);
	}

	void testIncrementalFreeze() {
		builder.start(ctx, LogicProgram::AspOptions().noEq());
		// I1:
		// {y}.
		// a :- not x.
		// b :- a, y.
		// freeze(x)
		builder.updateProgram();
		builder.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "x").setAtomName(4, "y")
			.startRule(CHOICERULE).addHead(4).endRule()
			.startRule().addHead(1).addToBody(3, false).endRule()
			.startRule().addHead(2).addToBody(1, true).addToBody(4, true).endRule()
			.freeze(3)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.symbolTable()[3].lit != negLit(0));
		Solver& solver = *ctx.master();
		solver.assume(ctx.symbolTable()[3].lit);
		solver.propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(ctx.symbolTable()[2].lit));
		solver.undoUntil(0);
		// I2: 
		// {z}.
		// x :- z.
		// unfreeze(x)
		builder.updateProgram();
		builder.setAtomName(5, "z")
			.startRule(CHOICERULE).addHead(5).endRule()
			.startRule().addHead(3).addToBody(5, true).endRule()
			.unfreeze(3)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		solver.assume(ctx.symbolTable()[5].lit);
		solver.propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(ctx.symbolTable()[2].lit));
		solver.undoUntil(0);
		solver.assume(~ctx.symbolTable()[5].lit);	// ~z
		solver.propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(ctx.symbolTable()[3].lit));
		solver.assume(ctx.symbolTable()[4].lit);	// y
		solver.propagate();
		CPPUNIT_ASSERT(ctx.master()->isTrue(ctx.symbolTable()[2].lit));
	}

	void testIncrementalFreezeValue() {
		builder.start(ctx, LogicProgram::AspOptions().noEq());
		// I1:
		// freeze(x)
		// freeze(y, true)
		// freeze(z, false)
		builder.updateProgram();
		builder.setAtomName(1, "x").setAtomName(2, "y").setAtomName(3, "z")
			.freeze(1).freeze(2, value_true).freeze(3, value_false)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		LitVec assume;
		builder.getAssumptions(assume);
		Solver& solver = *ctx.master();
		solver.pushRoot(assume);
		CPPUNIT_ASSERT(solver.isFalse(ctx.symbolTable()[1].lit));
		CPPUNIT_ASSERT(solver.isTrue(ctx.symbolTable()[2].lit));
		CPPUNIT_ASSERT(solver.isFalse(ctx.symbolTable()[3].lit));
		solver.popRootLevel(solver.decisionLevel());
		
		// I2: 
		// unfreeze(x)
		// freeze(z, value_true)
		// freeze(y, value_true)
		// freeze(y, value_false)
		builder.updateProgram();
		builder.unfreeze(1).freeze(3, value_true).freeze(2, value_true).freeze(2, value_false);
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		assume.clear();
		builder.getAssumptions(assume);
		CPPUNIT_ASSERT(assume.size() == 2 && solver.isFalse(ctx.symbolTable()[1].lit));
		solver.pushRoot(assume);
		CPPUNIT_ASSERT(solver.isFalse(ctx.symbolTable()[2].lit));
		CPPUNIT_ASSERT(solver.isTrue(ctx.symbolTable()[3].lit));
	}

	void testIncrementalFreezeOpen() {
		builder.start(ctx, LogicProgram::AspOptions().noEq());
		// I1:
		// freeze(x, value_free)
		builder.updateProgram();
		builder.setAtomName(1, "x").freeze(1, value_free);
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		LitVec assume;
		builder.getAssumptions(assume);
		Solver& solver = *ctx.master();
		CPPUNIT_ASSERT(assume.empty());
		CPPUNIT_ASSERT(solver.value(ctx.symbolTable()[1].lit.var()) == value_free);
		
		// I2: 
		builder.updateProgram();
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		assume.clear();
		builder.getAssumptions(assume);
		CPPUNIT_ASSERT(assume.empty());
		CPPUNIT_ASSERT(solver.value(ctx.symbolTable()[1].lit.var()) == value_free);

		// I3:
		builder.updateProgram();
		builder.freeze(1, value_true);
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		assume.clear();
		builder.getAssumptions(assume);
		CPPUNIT_ASSERT(assume.size() == 1 && assume[0] == ctx.symbolTable()[1].lit);
	}
	void testIncrementalKeepFrozen() {
		builder.start(ctx);
		// I0:
		// freeze{x}.
		builder.updateProgram();
		builder.setAtomName(1, "x")
			.freeze(1)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		PrgAtom* x   = builder.getAtom(1);
		Literal xLit = x->literal();
		// I1:
		builder.updateProgram();
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(x->literal() == xLit);
		CPPUNIT_ASSERT(x->frozen());
	}
	void testIncrementalFreezeCompute() {
		builder.start(ctx);
		// I0:
		// freeze{x}.
		builder.updateProgram();
		builder.setAtomName(1, "x").setAtomName(2, "y").setAtomName(3, "z").setAtomName(4, "z2")
			.freeze(1).freeze(2).freeze(3).freeze(4)
			.setCompute(1, true).setCompute(2, true).setCompute(3, false).setCompute(4, false)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		PrgAtom* x = builder.getAtom(1);
		PrgAtom* y = builder.getAtom(2);
		CPPUNIT_ASSERT(x->frozen() && y->frozen());
		CPPUNIT_ASSERT(x->literal() != y->literal());
		PrgAtom* z  = builder.getAtom(3);
		PrgAtom* z2 = builder.getAtom(4);
		CPPUNIT_ASSERT(z->frozen() && z2->frozen());
		CPPUNIT_ASSERT(z->literal() == z2->literal());
		// I1:
		builder.updateProgram();
		builder.setCompute(1, false);
		CPPUNIT_ASSERT_EQUAL(false, builder.endProgram());
	}
	void testIncrementalUnfreezeUnsupp() {
		builder.start(ctx, LogicProgram::AspOptions().noEq());
		// I1:
		// a :- not x.
		// freeze(x)
		builder.updateProgram();
		builder.setAtomName(1, "a").setAtomName(2, "x")
			.startRule().addHead(1).addToBody(2, false).endRule()
			.freeze(2)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		DefaultUnfoundedCheck* ufsCheck = new DefaultUnfoundedCheck();
		if (ctx.sccGraph.get()) {
			ctx.master()->addPost(ufsCheck);
			ufsCheck = 0;
		}
		ctx.endInit();;
		// I2: 
		// x :- y.
		// y :- x.
		// -> unfreeze(x)
		builder.updateProgram();
		builder.setAtomName(3, "y")
			.startRule().addHead(3).addToBody(2, true).endRule()
			.startRule().addHead(2).addToBody(3, true).endRule()
			.unfreeze(2)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		if (ctx.sccGraph.get() && ufsCheck) {
			ctx.master()->addPost(ufsCheck);
			ufsCheck = 0;
		}
		ctx.endInit();
		delete ufsCheck;
		CPPUNIT_ASSERT(ctx.master()->isTrue(ctx.symbolTable()[1].lit));
		CPPUNIT_ASSERT(ctx.master()->isFalse(ctx.symbolTable()[2].lit));
		CPPUNIT_ASSERT(ctx.master()->isFalse(ctx.symbolTable()[3].lit));
	}

	void testIncrementalUnfreezeCompute() {
		builder.start(ctx, LogicProgram::AspOptions().noEq());
		// I1:
		// {z}.
		// a :- x, y.
		// x :- z.
		// freeze(y)
		builder.updateProgram();
		builder.setAtomName(1, "a").setAtomName(2, "x").setAtomName(3, "y").setAtomName(4, "z")
			.startRule(CHOICERULE).addHead(4).endRule()
			.startRule().addHead(1).addToBody(2,true).addToBody(3, true).endRule()
			.startRule().addHead(2).addToBody(4,true).endRule()
			.freeze(3)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(3u, ctx.numConstraints());
		
		builder.updateProgram();
		builder.unfreeze(3);
		builder.setCompute(3, false);
		
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(3u >= ctx.numConstraints());
		CPPUNIT_ASSERT(ctx.master()->numFreeVars() == 1);
	}

	void testIncrementalCompute() {
		builder.start(ctx, LogicProgram::AspOptions());
		// I1: 
		// {a, b}.
		// FALSE :- a, b.
		builder.updateProgram();
		builder.setAtomName(1, "FALSE").setAtomName(2, "a").setAtomName(3, "b")
			.startRule(CHOICERULE).addHead(2).addHead(3).endRule()
			.startRule().addHead(1).addToBody(2, true).addToBody(3, true).endRule()
			.setCompute(1, false)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		// I2:
		// {c}.
		// FALSE :- a, c.
		builder.updateProgram();
		builder.setAtomName(4, "c")
			.startRule(CHOICERULE).addHead(4).endRule()
			.startRule().addHead(1).addToBody(2, true).addToBody(4, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		ctx.master()->assume(ctx.symbolTable()[2].lit);
		ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(ctx.symbolTable()[3].lit));
		CPPUNIT_ASSERT(ctx.master()->isFalse(ctx.symbolTable()[4].lit));
	}

	void testIncrementalComputeBackprop() {
		builder.start(ctx, LogicProgram::AspOptions().backpropagate());
		// I1: 
		// a :- not b.
		// b :- not a.
		builder.updateProgram();
		builder.setAtomName(1, "a").setAtomName(2, "b")
			.startRule().addHead(1).addToBody(2, false).endRule()
			.startRule().addHead(2).addToBody(1, false).endRule()
			.setCompute(1, true)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		// I2:
		builder.updateProgram();
		builder.setAtomName(3, "c").setAtomName(4, "d");
		builder.startRule().addHead(3).addToBody(2, true).endRule();
		builder.startRule().addHead(4).addToBody(2, false).endRule();
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT_EQUAL(false, builder.getAtom(3)->hasVar());
		CPPUNIT_ASSERT_EQUAL(posLit(0), builder.getLiteral(4));
	}

	void testIncrementalBackpropStep() {
		builder.start(ctx);
		// I1: 
		// {x}.
		builder.updateProgram();
		builder.setAtomName(1, "x")
			.startRule(CHOICERULE).addHead(1).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		// I2:
		// a :- x, y.
		// compute a.
		builder.updateProgram();
		builder.setAtomName(2, "a").setAtomName(3, "y")
			.startRule(CHOICERULE).addHead(3).endRule()
			.startRule().addHead(2).addToBody(1, true).addToBody(3, true).endRule()
			.setCompute(2, true)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.master()->isTrue(builder.getAtom(1)->literal()));
	}

	void testIncrementalEq() {
		builder.start(ctx);
		builder.updateProgram();
		builder.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3,"x").setAtomName(4, "y")
			.startRule(CHOICERULE).addHead(3).addHead(4).endRule() // {x, y}
			.startRule().addHead(1).addToBody(3, true).endRule() // a :- x.
			.startRule().addHead(1).addToBody(4, true).endRule() // a :- y.
			.startRule().addHead(2).addToBody(1, true).endRule() // b :- a.
		;
		// b == a
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		builder.write(str);
		CPPUNIT_ASSERT(str.str().find("1 2 1 0 1") != std::string::npos);
		builder.updateProgram();
		builder.setAtomName(5, "c")
			.startRule().addHead(5).addToBody(1, true).addToBody(2, true).endRule() // c :- a,b --> c :- a
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		builder.write(str);
		CPPUNIT_ASSERT(str.str().find("1 5 1 0 1") != std::string::npos);
	}

	void testIncrementalEqUnfreeze() {
		builder.start(ctx);
		builder.updateProgram();
		builder.setAtomName(1, "a")
			.freeze(1)
		;
		builder.endProgram();
		// I1:
		// {x}.
		// a :- c.
		// b :- x, not a.
		builder.updateProgram();
		builder.setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "x")
			.startRule(CHOICERULE).addHead(4).endRule()
			.startRule().addHead(1).addToBody(3, true).endRule()
			.startRule().addHead(2).addToBody(4, true).addToBody(1, false).endRule()
			.unfreeze(1)
		;
		builder.endProgram();
		CPPUNIT_ASSERT(ctx.numVars() == 2 && ctx.master()->numFreeVars() == 1);
		const SymbolTable& index = ctx.symbolTable();
		CPPUNIT_ASSERT(index[2].lit == index[4].lit);
	}

	void testIncrementalEqComplement() {
		builder.start(ctx);
		// I0:
		// a :- not b.
		// b :- not a.
		builder.updateProgram();
		builder.setAtomName(1, "a").setAtomName(2, "b")
			.startRule().addHead(1).addToBody(2, false).endRule()
			.startRule().addHead(2).addToBody(1, false).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		PrgAtom* a = builder.getAtom(1);
		PrgAtom* b = builder.getAtom(2);
		CPPUNIT_ASSERT(b->literal() == ~a->literal());
		// I1: 
		// c :- a, b.
		builder.updateProgram();
		builder.setAtomName(3, "c")
			.startRule().addHead(3).addToBody(1, false).addToBody(2, false).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());		
		PrgAtom* c = builder.getAtom(3);
		CPPUNIT_ASSERT(c->hasVar() == false);
	}

	void testIncrementalEqUpdateAssigned() {
		builder.start(ctx);
		// I0:
		// freeze{x}.
		builder.updateProgram();
		builder.setAtomName(1, "x")
			.freeze(1)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		
		// I1: 
		// x :- y.
		// y :- x.
		// unfreeze{x}.
		builder.updateProgram();
		builder.setAtomName(2, "y")
			.startRule().addHead(1).addToBody(2, true).endRule()
			.startRule().addHead(2).addToBody(1, true).endRule()
			.unfreeze(1)
		;
		PrgAtom* x = builder.getAtom(1);
		x->setValue(value_weak_true);
		builder.endProgram();
		// only weak-true so still relevant in bodies!
		CPPUNIT_ASSERT(x->deps_begin()->sign() == false);
	}

	void testIncrementalEqResetState() {
		builder.start(ctx);
		// I0:
		// {a,b}.
		builder.updateProgram();
		builder.setAtomName(1, "a").setAtomName(2, "b")
			.startRule(CHOICERULE).addHead(1).addHead(2).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		
		// I1: 
		// {z}.
		// x :- c.
		// x :- y, a.
		// y :- d.
		// y :- x, b.
		// c :- z, not s.
		// d :- z, not r.
		builder.updateProgram();
		builder.setAtomName(3, "x").setAtomName(4, "y").setAtomName(5, "z").setAtomName(6, "c").setAtomName(7, "d")
			.startRule().addHead(3).addToBody(6, true).endRule() // x :- c.
			.startRule().addHead(4).addToBody(7, true).endRule() // y :- d.
			
			.startRule().addHead(3).addToBody(4, true).addToBody(1, true).endRule() // x :- y, a.
			.startRule().addHead(4).addToBody(3, true).addToBody(2, true).endRule() // y :- x, b.

			.startRule().addHead(6).addToBody(5, true).addToBody(8, false).endRule() // c :- z, not r.
			.startRule().addHead(7).addToBody(5, true).addToBody(9, false).endRule() // d :- z, not s.
			.startRule(CHOICERULE).addHead(5).endRule() // {z}.
		;
		builder.endProgram();
		CPPUNIT_ASSERT(builder.getAtom(3)->scc() == 0);
		CPPUNIT_ASSERT(builder.getAtom(4)->scc() == 0);
	}

	void testIncrementalUnfreezeUnsuppEq() {
		builder.start(ctx, LogicProgram::AspOptions().noScc());
		// I0:
		// freeze{x}.
		builder.updateProgram();
		builder.setAtomName(1, "x")
			.freeze(1)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		// I1: 
		// {z}.
		// x :- y.
		// y :- x, z.
		// unfreeze{x}.
		builder.updateProgram();
		builder.setAtomName(2, "y").setAtomName(3, "z")
			.startRule().addHead(1).addToBody(2, true).endRule()
			.startRule().addHead(2).addToBody(1, true).addToBody(3, true).endRule()
			.startRule(CHOICERULE).addHead(3).endRule()
			.unfreeze(1)
		;
		builder.endProgram();
		PrgAtom* x = builder.getAtom(1);
		PrgAtom* y = builder.getAtom(2);
		CPPUNIT_ASSERT(ctx.master()->isFalse(x->literal()));
		CPPUNIT_ASSERT(ctx.master()->isFalse(y->literal()));
	}

	void testIncrementalUnfreezeEq() {
		builder.start(ctx);
		// I0:
		// freeze{x}.
		builder.updateProgram();
		builder.setAtomName(1, "x")
			.freeze(1)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		// I1: 
		// {z}.
		// y :- z.
		// x :- y.
		// unfreeze{x}.
		builder.updateProgram();
		builder.setAtomName(2, "y").setAtomName(3, "z")
			.startRule(CHOICERULE).addHead(3).endRule()
			.startRule().addHead(2).addToBody(3, true).endRule()
			.startRule().addHead(1).addToBody(2, true).endRule()
			.unfreeze(1)
		;
		PrgAtom* x = builder.getAtom(1);
		builder.endProgram();
		// body {y} is eq to body {z} 
		CPPUNIT_ASSERT(ctx.master()->value(x->var()) == value_free);
		CPPUNIT_ASSERT(x->supports() == 1 && x->supps_begin()->node() == 1);
	}

	void testIncrementalStats() {
		LpStats incStats;
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
		incStats = builder.stats;
		CPPUNIT_ASSERT_EQUAL(uint32(3), incStats.atoms);
		CPPUNIT_ASSERT_EQUAL(uint32(2), incStats.bodies);
		CPPUNIT_ASSERT_EQUAL(uint32(2), incStats.rules());
		CPPUNIT_ASSERT_EQUAL(uint32(0), incStats.ufsNodes);
		CPPUNIT_ASSERT_EQUAL(uint32(0), incStats.sccs);
		
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
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		incStats.accu(builder.stats);
		CPPUNIT_ASSERT_EQUAL(uint32(6), incStats.atoms);
		CPPUNIT_ASSERT_EQUAL(uint32(6), incStats.bodies);
		CPPUNIT_ASSERT_EQUAL(uint32(6), incStats.rules());
		CPPUNIT_ASSERT_EQUAL(uint32(1), incStats.sccs);
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
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		incStats.accu(builder.stats);
		CPPUNIT_ASSERT_EQUAL(uint32(9), incStats.atoms);
		// +1 because of support body for atoms from previous steps
		CPPUNIT_ASSERT_EQUAL(uint32(10) + 1, incStats.bodies);
		CPPUNIT_ASSERT_EQUAL(uint32(10), incStats.rules());
		CPPUNIT_ASSERT_EQUAL(uint32(2), incStats.sccs);
	}

	void testIncrementalTransform() {
		builder.start(ctx, LogicProgram::AspOptions().noEq());
		builder.setExtendedRuleMode(LogicProgram::mode_transform);
		// I1:
		// {a}.
		// --> 
		// a :- not a'
		// a':- not a.
		builder.updateProgram();
		builder.setAtomName(1, "a")
			.startRule(CHOICERULE).addHead(1).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.sccGraph.get() == 0);
		// I2:
		// b :- a.
		// b :- c.
		// c :- b.
		// NOTE: b must not have the same id as a'
		builder.updateProgram();
		builder.setAtomName(2, "b").setAtomName(3, "c")
			.startRule().addHead(2).addToBody(1, true).endRule()
			.startRule().addHead(2).addToBody(3, true).endRule()
			.startRule().addHead(3).addToBody(2, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		CPPUNIT_ASSERT(ctx.sccGraph.get() != 0);
	}

	void testIncrementalBackpropCompute() {
		builder.start(ctx);
		// I0:
		// a :- x.
		// freeze{x}.
		// compute{a}.
		builder.updateProgram();
		builder.setAtomName(1, "a").setAtomName(2, "x")
			.startRule().addHead(1).addToBody(2, true).endRule()
			.setCompute(1, true)
			.freeze(2)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(builder.getEqAtom(1) == 2);
		PrgAtom* x = builder.getAtom(2);
		CPPUNIT_ASSERT(x->value() == value_weak_true);
		// I1: 
		// x :- y.
		// y :- x.
		// unfreeze{x}.
		builder.updateProgram();
		builder.setAtomName(3, "y")
			.startRule().addHead(3).addToBody(2, true).endRule()
			.startRule().addHead(2).addToBody(3, true).endRule()
			.unfreeze(2)
		;
		// UNSAT: no support for x,y
		CPPUNIT_ASSERT_EQUAL(false, builder.endProgram());
	}

	void testIncrementalBackpropSolver() {
		builder.start(ctx);
		// I0:
		// {a}.
		// freeze{x}.
		builder.updateProgram();
		builder.setAtomName(1, "a").setAtomName(2, "x")
			.startRule(CHOICERULE).addHead(1).endRule()
			.setCompute(1, true)
			.setCompute(2, true)
			.freeze(2)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		PrgAtom* a = builder.getAtom(1);
		PrgAtom* x = builder.getAtom(2);
		CPPUNIT_ASSERT(a->value() == value_true);
		CPPUNIT_ASSERT(x->value() == value_weak_true);
		// I1: 
		builder.updateProgram();
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(a->value() == value_true);
		CPPUNIT_ASSERT(x->value() == value_weak_true);
	}

	void testIncrementalFreezeUnfreeze() {
		builder.start(ctx);
		// I0:
		// {a}.
		// freeze{x}.
		// unfreeze{x}.
		builder.updateProgram();
		builder.setAtomName(1, "a").setAtomName(2, "x")
			.startRule(CHOICERULE).addHead(1).endRule()
			.freeze(2)
			.unfreeze(2)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT_EQUAL(negLit(0), ctx.symbolTable()[2].lit);
		// I1:
		// freeze(y).
		// y :- x.
		builder.updateProgram();
		builder.setAtomName(3, "y")
			.freeze(3)
			.startRule().addHead(3).addToBody(2, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT_EQUAL(true, ctx.master()->isFalse(ctx.symbolTable()[2].lit));
	}
	void testIncrementalSymbolUpdate() {
		builder.start(ctx);
		// I0:
		// {a}.
		builder.updateProgram();
		builder.setAtomName(1, "a")
			.startRule(CHOICERULE).addHead(1).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		// I1:
		// {_unnamed, b}.
		builder.updateProgram();
		builder.setAtomName(3, "b")
			.startRule(CHOICERULE).addHead(2).addHead(3).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(ctx.symbolTable().find(2) == 0);
		CPPUNIT_ASSERT(!isSentinel(ctx.symbolTable()[3].lit));
	}
	void testIncrementalFreezeDefined() {
		builder.start(ctx);
		// I0:
		// {a}.
		builder.updateProgram();
		builder.setAtomName(1, "a")
			.startRule(CHOICERULE).addHead(1).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		// I1:
		builder.updateProgram();
		builder.freeze(1);
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(builder.getAtom(1)->frozen() == false);
	}
	void testIncrementalUnfreezeDefined() {
		builder.start(ctx);
		// I0:
		// {a}.
		builder.updateProgram();
		builder.setAtomName(1, "a")
			.startRule(CHOICERULE).addHead(1).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		// I1:
		builder.updateProgram();
		builder.unfreeze(1);
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(!ctx.master()->isFalse(builder.getLiteral(1)));
	}
	void testIncrementalImplicitUnfreeze() {
		builder.start(ctx);
		// I0:
		// freeze(a).
		builder.updateProgram();
		builder.setAtomName(1, "a")
			.freeze(1)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(builder.getAtom(1)->frozen() == true);
		CPPUNIT_ASSERT(!ctx.master()->isFalse(builder.getLiteral(1)));
		// I1:
		// {a}.
		builder.updateProgram();
		builder.startRule(CHOICERULE).addHead(1).endRule();
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(builder.getAtom(1)->frozen() == false);
	}
	void testIncrementalRedefine() {
		builder.start(ctx);
		// I0:
		// {a}.
		builder.updateProgram();
		builder.setAtomName(1, "a")
			.startRule(CHOICERULE).addHead(1).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		// I1:
		// {a}.
		builder.updateProgram();
		CPPUNIT_ASSERT_THROW(builder.startRule(CHOICERULE).addHead(1).endRule(), RedefinitionError);
	}
	void testIncrementalGetAssumptions() {
		builder.start(ctx);
		// I0:
		builder.updateProgram();
		builder.setAtomName(1, "a").setAtomName(2, "b")
			.freeze(1).freeze(2)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		LitVec a;
		builder.getAssumptions(a);
		CPPUNIT_ASSERT(a.size() == 2 && a[0] == ~builder.getLiteral(1) && a[1] == ~builder.getLiteral(2));
	}

	void testIncrementalSimplifyCard() {
		builder.start(ctx);
		// I0:
		builder.updateProgram();
		builder.setAtomName(1, "a")
			.startRule().addHead(1).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		builder.updateProgram();
		builder.setAtomName(2, "b").setAtomName(3, "c").setAtomName(4, "d")
			.startRule(CONSTRAINTRULE,1).addHead(2).addToBody(3, true).addToBody(1, true).endRule()
			.startRule(CONSTRAINTRULE,1).addHead(4).addToBody(3, true).addToBody(2, true).endRule()
			.startRule(BASICRULE).addHead(3).addToBody(1, true,2).addToBody(2,true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
	}

	void testIncrementalSimplifyMinimize() {
		builder.start(ctx);
		// I0:
		builder.updateProgram();
		builder.setAtomName(1, "a")
			.startRule().addHead(1).endRule() // a.
			.startRule(OPTIMIZERULE).addToBody(1, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(builder.getMinimizeConstraint()->adjust(0) == 1);
		builder.disposeMinimizeConstraint();
		
		builder.updateProgram();
		builder.startRule(OPTIMIZERULE).addToBody(1, true).endRule();
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(builder.getMinimizeConstraint());
		CPPUNIT_ASSERT(builder.getMinimizeConstraint()->adjust(0) == 1);
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
	}
	
	void testIncrementalEqOverNeg() {
		builder.start(ctx);
		// I0: {a(1)}.
		builder.updateProgram();
		builder.setAtomName(1, "a(1)")
			.startRule(CHOICERULE).addHead(1).endRule() // {a(1)}.
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		
		// I1:
		// a(2) :- not a(1).
		// a(3) :- a(2).
		// a(3) :- a(6).
		// a(4) :- a(3).
		// a(5) :- a(4).
		// a(7) :- a(3).
		// a(8) :- not a(6), a(3).
		// compute a(5),a(8).
		builder.updateProgram();
		builder.setAtomName(2, "a(2)").setAtomName(3, "a(3)").setAtomName(4, "a(4)").setAtomName(5, "a(5)").setAtomName(6, "a(6)").setAtomName(7, "a(7)").setAtomName(8, "a(8)");
		builder.startRule().addHead(2).addToBody(1, false).endRule(); // a(2) :- not a(1).
		builder.startRule().addHead(3).addToBody(2, true).endRule();  // a(3) :- a(2).
		builder.startRule().addHead(3).addToBody(6, true).endRule();  // a(3) :- a(6).
		builder.startRule().addHead(4).addToBody(3, true).endRule();  // a(4) :- a(3).
		builder.startRule().addHead(5).addToBody(4, true).endRule();  // a(5) :- a(4).
		builder.startRule().addHead(7).addToBody(3, true).endRule();  // a(7) :- a(3).
		builder.startRule().addHead(8).addToBody(6, false).addToBody(3,true).endRule();  // a(8) :- not a(6), a(3).
		builder.setCompute(5, true);
		builder.setCompute(8, true);
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		CPPUNIT_ASSERT(ctx.numVars() == 1 && ctx.master()->isFalse(builder.getLiteral(1)));
	}

	void testIncrementalKeepExternalValue() {
		builder.start(ctx);
		// I0:
		builder.updateProgram();
		builder.setAtomName(2, "a").setAtomName(3, "h")
			.startRule().addHead(2).endRule()
			.startRule().addHead(1).addToBody(3, true).endRule()
			.setCompute(1, false)
			.freeze(3, value_true)
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		LitVec a;
		builder.getAssumptions(a);
		CPPUNIT_ASSERT_EQUAL(false, ctx.master()->pushRoot(a));

		CPPUNIT_ASSERT_EQUAL(true, builder.update());
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram() && ctx.endInit());
		a.clear();
		builder.getAssumptions(a);
		CPPUNIT_ASSERT_EQUAL(false, ctx.master()->pushRoot(a));

		CPPUNIT_ASSERT_EQUAL(true, builder.update());
		builder.startRule().addHead(3).endRule();
		CPPUNIT_ASSERT_EQUAL(false, builder.endProgram());
	}

	void testFreezeIsExternal() {
		builder.start(ctx);
		builder.updateProgram();
		builder.startRule(Asp::CHOICERULE).addHead(2).endRule();
		builder.freeze(1);
		CPPUNIT_ASSERT_EQUAL(true , builder.isExternal(1));
		CPPUNIT_ASSERT_EQUAL(false, builder.isExternal(2));
		builder.endProgram();
		CPPUNIT_ASSERT_EQUAL(true , builder.isExternal(1));
		CPPUNIT_ASSERT_EQUAL(false, builder.isExternal(2));
	}
	void testUnfreezeIsNotExternal() {
		builder.start(ctx);
		builder.updateProgram();
		builder.freeze(1);
		builder.unfreeze(2);
		builder.unfreeze(1);
		builder.freeze(2);
		CPPUNIT_ASSERT_EQUAL(false, builder.isExternal(1));
		CPPUNIT_ASSERT_EQUAL(false, builder.isExternal(2));
		builder.endProgram();
		CPPUNIT_ASSERT_EQUAL(false, builder.isExternal(1));
		CPPUNIT_ASSERT_EQUAL(false, builder.isExternal(2));
	}
	void testFreezeStaysExternal() {
		builder.start(ctx);
		builder.updateProgram();
		builder.freeze(1);
		CPPUNIT_ASSERT_EQUAL(true, builder.isExternal(1));
		builder.endProgram();
		CPPUNIT_ASSERT_EQUAL(true, builder.isExternal(1));
		builder.updateProgram();
		CPPUNIT_ASSERT_EQUAL(true, builder.isExternal(1));
		builder.endProgram();
		CPPUNIT_ASSERT_EQUAL(true, builder.isExternal(1));
	}
	void testDefinedIsNotExternal() {
		builder.start(ctx);
		builder.updateProgram();
		builder.freeze(1);
		builder.endProgram();
		builder.updateProgram();
		builder.startRule().addHead(1).addToBody(2, true).endRule();
		CPPUNIT_ASSERT_EQUAL(false, builder.isExternal(1));
		builder.endProgram();
		CPPUNIT_ASSERT_EQUAL(false, builder.isExternal(1));
	}
private:
	typedef SharedDependencyGraph DG;
	SharedContext ctx;
	LogicProgram  builder;
	stringstream  str;
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
		CPPUNIT_ASSERT(!builder.getMinimizeConstraint());
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
		CPPUNIT_ASSERT(builder.getMinimizeConstraint()->numRules() == 1);
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
		CPPUNIT_ASSERT(builder.getMinimizeConstraint()->numRules() == 1);
		CPPUNIT_ASSERT(builder.getMinimizeConstraint()->adjust(0) == 1);
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
		CPPUNIT_ASSERT(x == posLit(0));
	}
	void testProductFalse() {
		builder.prepareProblem(3, 1, 1);
		LitVec p1(3);
		p1[0] = posLit(1);
		p1[1] = posLit(2);
		p1[2] = posLit(3);
		ctx.master()->force(negLit(2), 0);
		Literal x = builder.addProduct(p1);
		CPPUNIT_ASSERT(x == negLit(0));
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
