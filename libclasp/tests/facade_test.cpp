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
#include <clasp/clasp_facade.h>
#include <clasp/minimize_constraint.h>
#include <clasp/heuristics.h>
#include <clasp/lookahead.h>

namespace Clasp { namespace Test {
using namespace Clasp::mt;

class FacadeTest : public CppUnit::TestFixture {
	CPPUNIT_TEST_SUITE(FacadeTest);
	CPPUNIT_TEST(testPrepareIsIdempotent);
	CPPUNIT_TEST(testPrepareIsImplicit);
	CPPUNIT_TEST(testCannotPrepareSolvedProgram);
	CPPUNIT_TEST(testCannotSolveSolvedProgram);
	
	CPPUNIT_TEST(testUpdateWithoutPrepareDoesNotIncStep);
	CPPUNIT_TEST(testUpdateWithoutSolveDoesNotIncStep);
	CPPUNIT_TEST(testInterruptBeforePrepareInterruptsNext);
	CPPUNIT_TEST(testInterruptBeforeSolveInterruptsNext);
	CPPUNIT_TEST(testShutdownStopsStep);

	CPPUNIT_TEST(testSolveUnderAssumptions);
	CPPUNIT_TEST(testPrepareTooStrongBound);

	CPPUNIT_TEST(testIncrementalSolve);
	CPPUNIT_TEST(testIncrementalEnum);
	CPPUNIT_TEST(testIncrementalCons);
	CPPUNIT_TEST(testIncrementalMin);
	CPPUNIT_TEST(testIncrementalMinIgnore);
	CPPUNIT_TEST(testUpdateConfig);
	CPPUNIT_TEST(testIncrementalProjectUpdate);
	CPPUNIT_TEST(testIncrementalConfigUpdateBug);
	CPPUNIT_TEST(testIncrementalLookaheadAddHeuristic);
	CPPUNIT_TEST(testIncrementalDisableLookahead);
	CPPUNIT_TEST(testIncrementalChangeLookahead);
	CPPUNIT_TEST(testIncrementalExtendLookahead);
	CPPUNIT_TEST(testIncrementalAddSolver);
	CPPUNIT_TEST(testIncrementalRemoveSolver);
	CPPUNIT_TEST(testStats);
#if WITH_THREADS
	CPPUNIT_TEST(testShareModeRegression);
	CPPUNIT_TEST(testAsyncSolveTrivialUnsat);
	CPPUNIT_TEST(testInterruptBeforeSolve);
	CPPUNIT_TEST(testCancelAsyncOperation);
	CPPUNIT_TEST(testAsyncResultDtorCancelsOp);
	CPPUNIT_TEST(testDestroyAsyncResultNoFacade);
	CPPUNIT_TEST(testDestroyDanglingAsyncResult);
	CPPUNIT_TEST(testCancelDanglingAsyncOperation);
#endif
	CPPUNIT_TEST_SUITE_END(); 
public:
	typedef ClaspFacade::Result Result;
	void addProgram(Clasp::Asp::LogicProgram& prg) {
		prg.setAtomName(1, "a").setAtomName(2, "b");
		prg.startRule().addHead(1).addToBody(2, false).endRule();
		prg.startRule().addHead(2).addToBody(1, false).endRule();
	}
	
	void testPrepareIsIdempotent() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		addProgram(asp);
		libclasp.prepare();
		libclasp.prepare();
		
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 2);
		CPPUNIT_ASSERT(libclasp.summary().step == 0);
	}

	void testPrepareIsImplicit() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config);
		addProgram(asp);

		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 2);
		CPPUNIT_ASSERT(libclasp.summary().step == 0);
	}

	void testCannotPrepareSolvedProgram() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		addProgram(asp);
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT_THROW(libclasp.prepare(), std::logic_error);
	}
	void testCannotSolveSolvedProgram() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		addProgram(asp);
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT_THROW(libclasp.solve(), std::logic_error);
	}
	void testUpdateWithoutPrepareDoesNotIncStep() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		addProgram(asp);
		CPPUNIT_ASSERT(libclasp.update().ok());
		CPPUNIT_ASSERT(libclasp.update().ok());
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 2);
		CPPUNIT_ASSERT(libclasp.summary().step == 0);
	}
	void testUpdateWithoutSolveDoesNotIncStep() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		addProgram(asp);
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.update().ok());
		libclasp.prepare();
		
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 2);
		CPPUNIT_ASSERT(libclasp.summary().step == 0);
	}

	void testInterruptBeforePrepareInterruptsNext() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		addProgram(asp);
		struct FH : EventHandler {
			FH() : finished(0) {}
			virtual void onEvent(const Event& ev) {
				finished += event_cast<ClaspFacade::StepReady>(ev) != 0;
			}
			int finished;
		} fh;
		CPPUNIT_ASSERT(libclasp.terminate(1) == false);
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve(&fh).interrupted());
		CPPUNIT_ASSERT(libclasp.solved());
		CPPUNIT_ASSERT(fh.finished == 1);
	}

	void testInterruptBeforeSolveInterruptsNext() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		addProgram(asp);
		struct FH : EventHandler {
			FH() : finished(0) {}
			virtual void onEvent(const Event& ev) {
				finished += event_cast<ClaspFacade::StepReady>(ev) != 0;
			}
			int finished;
		} fh;
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.terminate(1) == false);
		CPPUNIT_ASSERT(!libclasp.solved());
		CPPUNIT_ASSERT(libclasp.solve(&fh).interrupted());
		CPPUNIT_ASSERT(libclasp.solved());
		CPPUNIT_ASSERT(fh.finished == 1);
	}


	void testShutdownStopsStep() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		addProgram(asp);
		libclasp.prepare();
		libclasp.shutdown();
		CPPUNIT_ASSERT(libclasp.solved());
	}

	void testSolveUnderAssumptions() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		addProgram(asp);
		Var ext = asp.newAtom();
		asp.setAtomName(ext, "ext");
		asp.freeze(ext, value_true);
		libclasp.prepare();
		LitVec assume(1, asp.getLiteral(1));
		struct MH : public Clasp::EventHandler {
			MH() : models(0) {}
			bool onModel(const Clasp::Solver&, const Clasp::Model& m) {
				for (LitVec::const_iterator it = exp.begin(), end = exp.end(); it != end; ++it) {
					CPPUNIT_ASSERT(m.isTrue(*it));
				}
				++models;
				return true;
			}
			LitVec exp;
			int    models;
		} mh1, mh2;
		mh1.exp.push_back(asp.getLiteral(1));
		mh1.exp.push_back(~asp.getLiteral(2));
		mh1.exp.push_back(asp.getLiteral(ext));
		libclasp.assume(assume);
		libclasp.solve(&mh1);
		CPPUNIT_ASSERT(mh1.models == 1);
		libclasp.update();
		asp.freeze(ext, value_false);
		assume.assign(1, asp.getLiteral(2));
		mh2.exp.push_back(~asp.getLiteral(1));
		mh2.exp.push_back(asp.getLiteral(2));
		mh2.exp.push_back(~asp.getLiteral(ext));
		libclasp.prepare();
		libclasp.assume(assume);
		libclasp.solve(&mh2);
		CPPUNIT_ASSERT(mh2.models == 1);
		libclasp.update();
		libclasp.prepare();
		libclasp.solve();
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 2);
	}
	
	void testPrepareTooStrongBound() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		config.solve.optBound.assign(1, 0);
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		addProgram(asp);
		Var c = asp.newAtom();
		asp.setAtomName(c, "c");
		asp.startRule().addHead(c).endRule();
		asp.startRule(Asp::OPTIMIZERULE).addToBody(c, true).addToBody(1, true).addToBody(2, true).endRule();
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().unsat());
	}

	void testRunIncremental(Result::Base stop, int maxStep, int minStep, Result::Base expectedRes, int expectedSteps) {
		ClaspConfig config;
		ClaspFacade f;
		f.ctx.enableStats(2);
		config.asp.noEq();
		Asp::LogicProgram& asp = f.startAsp(config, true);
		Result::Base       res = Result::UNKNOWN;
		do {
			f.update();
			switch(f.step()) {
			default: break;
			case 0:
				asp.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "x")
					 .startRule().addHead(1).addToBody(2, true).endRule()
					 .startRule().addHead(2).addToBody(1, true).endRule()
					 .startRule().addHead(1).addToBody(3, true).endRule()
					 .freeze(3)
					 .setCompute(1, true);
				break;
			case 1:
				asp.setAtomName(4, "y").setAtomName(5, "z")
				   .startRule().addHead(3).addToBody(4, true).endRule()
				   .startRule().addHead(4).addToBody(3, true).endRule()
				   .startRule().addHead(4).addToBody(5, true).endRule()
				   .freeze(5);
				break;
			case 2:
				asp.setAtomName(6, "q").setAtomName(7, "r")
				   .startRule().addHead(5).addToBody(6, true).addToBody(7, true).endRule()
				   .startRule().addHead(6).addToBody(3, false).endRule()
				   .startRule().addHead(7).addToBody(1, false).addToBody(2, false).endRule()
				   .startRule(Asp::CHOICERULE).addHead(5).endRule();
				break;
			case 3:
				asp.setAtomName(8,"f").startRule(Asp::CHOICERULE).addHead(8).endRule();
				break;
			}
			f.prepare();
			res = f.solve();
		} while (--maxStep && ((minStep > 0 && --minStep) || res != stop));
		CPPUNIT_ASSERT_EQUAL(expectedRes,  (Result::Base)f.result());
		CPPUNIT_ASSERT_EQUAL(expectedSteps, f.step());
	}
	void testIncrementalSolve() {
		testRunIncremental(Result::SAT  , -1, -1, Result::SAT  , 2);
		testRunIncremental(Result::UNSAT, -1, -1, Result::UNSAT, 0);
		testRunIncremental(Result::SAT  ,  2, -1, Result::UNSAT, 1);
		testRunIncremental(Result::SAT  , -1,  4, Result::SAT  , 3);
	}
	void testIncrementalEnum() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		config.solve.enumMode  = EnumOptions::enum_record;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		asp.setAtomName(1, "a");
		asp.startRule(Clasp::Asp::CHOICERULE).addHead(1).endRule();
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 2);
		CPPUNIT_ASSERT(libclasp.update().ok());
		asp.setAtomName(2, "b");
		asp.startRule(Clasp::Asp::CHOICERULE).addHead(2).endRule();
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 4);
	}
	void testIncrementalCons() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		config.solve.enumMode  = EnumOptions::enum_cautious;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		asp.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c");
		asp.startRule(Clasp::Asp::CHOICERULE).addHead(1).addHead(2).addHead(3).endRule();
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		config.solve.enumMode = EnumOptions::enum_brave;
		libclasp.update(true);
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum > 1);
	}
	void testIncrementalMin() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		config.solve.enumMode  = EnumOptions::enum_auto;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		asp.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c");
		asp.startRule(Clasp::Asp::CHOICERULE).addHead(1).addHead(2).addHead(3).endRule();
		asp.startRule(Clasp::Asp::OPTIMIZERULE).addToBody(1,true).addToBody(2, true).addToBody(3, true).endRule();
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum < 8u);
		libclasp.update().disposeMinimizeConstraint();
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 8);
	}
	void testIncrementalMinIgnore() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.optMode = MinimizeMode_t::ignore;
		config.solve.numModels = 0;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		asp.setAtomName(1, "a").setAtomName(2, "b");
		asp.startRule(Clasp::Asp::CHOICERULE).addHead(1).addHead(2).endRule();
		asp.startRule(Clasp::Asp::OPTIMIZERULE).addToBody(1, true).addToBody(2, true).endRule();
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 4u);
		config.solve.optMode = MinimizeMode_t::optimize;
		libclasp.update(true);
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 1u);
	}
	void testUpdateConfig() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		config.solve.enumMode  = EnumOptions::enum_auto;
		config.addSolver(0).heuId  = Heuristic_t::heu_berkmin;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		asp.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c");
		asp.startRule(Clasp::Asp::CHOICERULE).addHead(1).addHead(2).addHead(3).endRule();
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		config.addSolver(0).heuId = Heuristic_t::heu_vsids;
		libclasp.update(true);
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(dynamic_cast<ClaspVsids*>(libclasp.ctx.master()->heuristic()));
	}
	void testIncrementalProjectUpdate() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		config.solve.enumMode  = EnumOptions::enum_auto;
		config.solve.project   = 1;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		asp.setAtomName(1, "_a").setAtomName(2, "b");
		asp.startRule(Clasp::Asp::CHOICERULE).addHead(1).addHead(2).endRule();
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.ctx.varInfo(libclasp.ctx.symbolTable()[2].lit.var()).project());
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 2);
		config.solve.project = 0;
		libclasp.update(true);
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 4);
		config.solve.project = 1;
		libclasp.update(true);
		asp.setAtomName(3, "_x").setAtomName(4, "y");
		asp.startRule(Clasp::Asp::CHOICERULE).addHead(3).addHead(4).endRule();
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.ctx.varInfo(libclasp.ctx.symbolTable()[2].lit.var()).project());
		CPPUNIT_ASSERT(libclasp.ctx.varInfo(libclasp.ctx.symbolTable()[4].lit.var()).project());
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT_EQUAL(uint64(4), libclasp.summary().numEnum);
	}
	void testIncrementalConfigUpdateBug() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.asp.erMode = Asp::LogicProgram::mode_transform;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		Var a = asp.newAtom(), b = asp.newAtom();
		asp.setAtomName(a, "a").setAtomName(b, "b");
		asp.startRule(Asp::CHOICERULE).addHead(a).addHead(b).endRule();
		libclasp.prepare();
		CPPUNIT_ASSERT(asp.stats.auxAtoms == 2);
		config.asp.erMode = Asp::LogicProgram::mode_native;
		libclasp.update(true);
		Var c = asp.newAtom(), d = asp.newAtom();
		asp.setAtomName(c, "c").setAtomName(d, "d");
		asp.startRule(Asp::CHOICERULE).addHead(c).addHead(d).endRule();
		libclasp.prepare();
		CPPUNIT_ASSERT(asp.stats.auxAtoms == 0);
	}
	
	void testIncrementalLookaheadAddHeuristic() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.addSolver(0).lookType = Lookahead::atom_lookahead;
		libclasp.startAsp(config, true).setAtomName(1, "a").setAtomName(2, "b").startRule(Asp::CHOICERULE).addHead(1).addHead(2).endRule();
		libclasp.prepare();
		PostPropagator* look = libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look);
		CPPUNIT_ASSERT(look && look->next == 0);
		config.addSolver(0).heuId = Heuristic_t::heu_unit;
		libclasp.update(true);
		libclasp.prepare();
		look = libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look);
		CPPUNIT_ASSERT(look && look->next == 0);
	}
	void testIncrementalDisableLookahead() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.addSolver(0).lookType = Lookahead::atom_lookahead;
		libclasp.startAsp(config, true).setAtomName(1, "a").setAtomName(2, "b").startRule(Asp::CHOICERULE).addHead(1).addHead(2).endRule();
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look));
		config.addSolver(0).lookType = Lookahead::no_lookahead;
		libclasp.update(true);
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look) == 0);
	}
	void testIncrementalChangeLookahead() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.addSolver(0).lookType = Lookahead::atom_lookahead;
		libclasp.startAsp(config, true).setAtomName(1, "a").setAtomName(2, "b").startRule(Asp::CHOICERULE).addHead(1).addHead(2).endRule();
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look));
		config.addSolver(0).lookType = Lookahead::body_lookahead;
		libclasp.update(true);
		libclasp.prepare();
		Lookahead* look = static_cast<Lookahead*>(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look));
		CPPUNIT_ASSERT(look && look->score.types == Var_t::body_var );
	}
	void testIncrementalExtendLookahead() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.addSolver(0).lookType = Lookahead::atom_lookahead;
		config.addSolver(0).lookOps  = 3;
		libclasp.startAsp(config, true).setAtomName(1, "a").setAtomName(2, "b").startRule(Asp::CHOICERULE).addHead(1).addHead(2).endRule();
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look));
		config.addSolver(0).lookOps  = 0;
		static_cast<Asp::LogicProgram&>(libclasp.update(true)).startRule(Asp::CHOICERULE).addHead(3).addHead(4).endRule();
		libclasp.prepare();
		Lookahead* look = static_cast<Lookahead*>(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look));
		CPPUNIT_ASSERT(look && look->next == 0 );
		while (libclasp.ctx.master()->numFreeVars() != 0) {
			libclasp.ctx.master()->decideNextBranch();
			libclasp.ctx.master()->propagate();
			CPPUNIT_ASSERT(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look) == look);
		}
	}
	void testIncrementalAddSolver() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		libclasp.startAsp(config, true).setAtomName(1, "a").setAtomName(2, "b").startRule(Asp::CHOICERULE).addHead(1).addHead(2).endRule();
		libclasp.prepare();
		CPPUNIT_ASSERT(!isSentinel(libclasp.ctx.stepLiteral()));
		config.solve.setSolvers(2);
		static_cast<Asp::LogicProgram&>(libclasp.update(true)).startRule(Asp::CHOICERULE).addHead(3).addHead(4).endRule();
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.ctx.concurrency() == 2 && libclasp.ctx.hasSolver(1));
	}
	
	void testIncrementalRemoveSolver() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		config.solve.setSolvers(4);
		libclasp.startAsp(config, true)
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule(Asp::CHOICERULE).addHead(1).addHead(2).addHead(4).addHead(3).endRule()
			.startRule(Asp::CONSTRAINTRULE, 3).addHead(7).addToBody(1, true).addToBody(2, true).addToBody(3, true).addToBody(4, true).endRule()
			.setCompute(7, false);
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT_EQUAL(uint64(11), libclasp.summary().numEnum);

		config.solve.setSolvers(1);
		static_cast<Asp::LogicProgram&>(libclasp.update(true)).startRule().addHead(7).addToBody(1, true).addToBody(2, true).endRule();
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat() && libclasp.summary().numEnum == 10);

		config.solve.setSolvers(2);
		libclasp.update(true);
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat() && libclasp.summary().numEnum == 10);
	}

	void testStats() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.stats = 2;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		asp.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c");
		asp.startRule(Clasp::Asp::CHOICERULE).addHead(1).addHead(2).addHead(3).endRule();
		asp.startRule(Clasp::Asp::OPTIMIZERULE).addToBody(1, true).addToBody(2, true).endRule();
		libclasp.prepare();
		libclasp.solve();
		std::vector<std::string> keys;
		getKeys(libclasp, keys, "");
		CPPUNIT_ASSERT(!keys.empty());
		for (std::vector<std::string>::const_iterator it = keys.begin(), end = keys.end(); it != end; ++it) {
			CPPUNIT_ASSERT(libclasp.getStat(it->c_str()).valid());
		}
		CPPUNIT_ASSERT(libclasp.getStat("lp.rules") == double(asp.stats.rules()));
		CPPUNIT_ASSERT(libclasp.getStat("enumerated") == double(libclasp.summary().enumerated()));
		CPPUNIT_ASSERT(libclasp.getStat("solvers.choices") == double(libclasp.ctx.master()->stats.choices));
		CPPUNIT_ASSERT(libclasp.getStat("costs.0") == double(libclasp.summary().costs()->at(0)));
		CPPUNIT_ASSERT(libclasp.getStat("optimal") == double(libclasp.summary().optimal()));
	}

	void getKeys(const ClaspFacade& f, std::vector<std::string>& out, const std::string& p) {
		typedef std::pair<std::string, double> Stat;
		std::size_t len = 0;
		for (const char* k = f.getKeys(p.c_str()); (len = std::strlen(k)) != 0; k += len + 1) {
			if (k[len-1] != '.') { 
				out.push_back(p+k);
				if (std::strcmp(k, "__len") == 0 && f.getStat(out.back().c_str()) > 0.0) {
					if (f.getKeys((p+"0").c_str())) { getKeys(f, out, p+"0."); }
					else                            { out.push_back(p+"0"); }
				}
			}
			else                 { getKeys(f, out, p+k); }
		}
	}
#if WITH_THREADS
	void testShareModeRegression() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.shareMode = ContextParams::share_auto;
		config.solve.algorithm.threads = 2;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		asp.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c");
		asp.startRule(Clasp::Asp::CHOICERULE).addHead(1).addHead(2).addHead(3).endRule();
		libclasp.prepare();
		CPPUNIT_ASSERT_EQUAL(true, libclasp.ctx.physicalShare(Constraint_t::static_constraint));
		CPPUNIT_ASSERT_EQUAL(true, libclasp.ctx.physicalShare(Constraint_t::learnt_conflict));
	}
	typedef ClaspFacade::AsyncResult AsyncResult;
	void testAsyncSolveTrivialUnsat() {
		ClaspConfig config;
		ClaspFacade libclasp;
		config.solve.numModels = 0;
		Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		asp.setAtomName(1, "a");
		asp.startRule().addHead(1).addToBody(1, false).endRule();
		libclasp.prepare();
		AsyncResult it = libclasp.startSolveAsync();
		CPPUNIT_ASSERT(it.end());
		CPPUNIT_ASSERT(it.get().unsat());
	}
	void testInterruptBeforeSolve() {
		ClaspConfig config;
		ClaspFacade libclasp;
		config.solve.numModels = 0;
		Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		asp.setAtomName(1, "a");
		asp.startRule(Asp::CHOICERULE).addHead(1).endRule();
		libclasp.prepare();
		libclasp.terminate(2);
		AsyncResult it = libclasp.startSolveAsync();
		CPPUNIT_ASSERT(it.end());
		CPPUNIT_ASSERT(it.get().interrupted());
	}
	void testCancelAsyncOperation() {
		ClaspConfig config;
		ClaspFacade libclasp;
		config.solve.numModels = 0;
		Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		asp.setAtomName(1, "a");
		asp.startRule(Asp::CHOICERULE).addHead(1).endRule();
		libclasp.prepare();
		AsyncResult it = libclasp.startSolveAsync();
		while (!it.end()) { 
			CPPUNIT_ASSERT(it.model().num == 1);
			if (it.cancel()){ break; }
		}
		CPPUNIT_ASSERT(it.end() && !libclasp.solving() && it.interrupted());
		libclasp.update();
		libclasp.prepare();
		it = libclasp.startSolveAsync();
		int mod = 0;
		while (!it.end()) { ++mod; it.next(); }
		CPPUNIT_ASSERT(!libclasp.solving() && mod == 2);
	}
	void testAsyncResultDtorCancelsOp() {
		ClaspConfig config;
		ClaspFacade libclasp;
		Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		asp.setAtomName(1, "a");
		asp.startRule(Asp::CHOICERULE).addHead(1).endRule();
		libclasp.prepare();
		{ AsyncResult it = libclasp.startSolveAsync(); }
		CPPUNIT_ASSERT(!libclasp.solving() && libclasp.result().interrupted());
	}
	void testDestroyAsyncResultNoFacade() {
		ClaspConfig  config;
		AsyncResult* handle   = 0;
		ClaspFacade* libclasp = new ClaspFacade();
		Asp::LogicProgram& asp= libclasp->startAsp(config, true);
		asp.setAtomName(1, "a");
		asp.startRule(Asp::CHOICERULE).addHead(1).endRule();
		libclasp->prepare();
		handle = new AsyncResult( libclasp->startSolveAsync() );
		delete libclasp;
		CPPUNIT_ASSERT(handle->interrupted());
		CPPUNIT_ASSERT_NO_THROW(delete handle);
	}
	void testDestroyDanglingAsyncResult() {
		ClaspConfig  config;
		ClaspFacade  libclasp;
		AsyncResult* handle = 0;
		Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		asp.setAtomName(1, "a");
		asp.startRule(Asp::CHOICERULE).addHead(1).endRule();
		libclasp.prepare();
		handle = new AsyncResult( libclasp.solveAsync() );
		handle->wait();
		libclasp.update();
		libclasp.prepare();
		AsyncResult* it = new AsyncResult(libclasp.startSolveAsync());
		delete handle;
		CPPUNIT_ASSERT(!it->interrupted() && libclasp.solving());
		CPPUNIT_ASSERT_NO_THROW(delete it);
		CPPUNIT_ASSERT(!libclasp.solving());
	}
	void testCancelDanglingAsyncOperation() {
		ClaspConfig  config;
		ClaspFacade  libclasp;
		
		Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		asp.setAtomName(1, "a");
		asp.startRule(Asp::CHOICERULE).addHead(1).endRule();
		libclasp.prepare();
		AsyncResult step0 = libclasp.solveAsync();
		step0.wait();
		libclasp.update();
		libclasp.prepare();
		AsyncResult step1 = libclasp.startSolveAsync();
		
		CPPUNIT_ASSERT_EQUAL(false, step0.cancel());
		CPPUNIT_ASSERT(libclasp.solving());
		CPPUNIT_ASSERT_EQUAL(true, step1.cancel());
		CPPUNIT_ASSERT(!libclasp.solving());
	}
#endif
};
CPPUNIT_TEST_SUITE_REGISTRATION(FacadeTest);
} } 

