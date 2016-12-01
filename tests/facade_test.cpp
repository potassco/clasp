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
#include "lpcompare.h"
#include <signal.h>
#include <clasp/solver.h>
#include <clasp/clause.h>
#include <clasp/clasp_facade.h>
#include <clasp/minimize_constraint.h>
#include <clasp/heuristics.h>
#include <clasp/lookahead.h>
#include <clasp/clingo.h>
#include <clasp/model_enumerators.h>

namespace Clasp { namespace Test {
using namespace Clasp::mt;

class FacadeTest : public CppUnit::TestFixture {
	CPPUNIT_TEST_SUITE(FacadeTest);
	CPPUNIT_TEST(testPrepareIsIdempotent);
	CPPUNIT_TEST(testPrepareIsImplicit);
	CPPUNIT_TEST(testPrepareSolvedProgram);
	CPPUNIT_TEST(testSolveSolvedProgram);
	CPPUNIT_TEST(testSolveAfterStopConflict);
	CPPUNIT_TEST(testRestartAfterPrepare);

	CPPUNIT_TEST(testUpdateWithoutPrepareDoesNotIncStep);
	CPPUNIT_TEST(testUpdateWithoutSolveDoesNotIncStep);
	CPPUNIT_TEST(testInterruptBeforePrepareInterruptsNext);
	CPPUNIT_TEST(testInterruptBeforeSolveInterruptsNext);
	CPPUNIT_TEST(testInterruptAfterSolveInterruptsNext);
	CPPUNIT_TEST(testInterruptBeforeUpdateInterruptsNext);
	CPPUNIT_TEST(testUpdateCanIgnoreQueuedSignals);
	CPPUNIT_TEST(testShutdownStopsStep);

	CPPUNIT_TEST(testSolveUnderAssumptions);
	CPPUNIT_TEST(testPrepareTooStrongBound);

	CPPUNIT_TEST(testComputeBraveViaOutput);
	CPPUNIT_TEST(testComputeBraveViaProject);
	CPPUNIT_TEST(testComputeQuery);
	CPPUNIT_TEST(testOptN);
	CPPUNIT_TEST(testOptNGenerator);

	CPPUNIT_TEST(testIncrementalSolve);
	CPPUNIT_TEST(testIncrementalEnum);
	CPPUNIT_TEST(testIncrementalCons);
	CPPUNIT_TEST(testIncrementalMin);
	CPPUNIT_TEST(testIncrementalMinIgnore);
	CPPUNIT_TEST(testIncrementalMinAdd);
	CPPUNIT_TEST(testUpdateConfig);
	CPPUNIT_TEST(testIncrementalProjectUpdate);
	CPPUNIT_TEST(testIncrementalDomRecUpdate);
	CPPUNIT_TEST(testIncrementalConfigUpdateBug);
	CPPUNIT_TEST(testIncrementalLookaheadAddHeuristic);
	CPPUNIT_TEST(testIncrementalDisableLookahead);
	CPPUNIT_TEST(testIncrementalChangeLookahead);
	CPPUNIT_TEST(testIncrementalExtendLookahead);
	CPPUNIT_TEST(testIncrementalAddSolver);
	CPPUNIT_TEST(testIncrementalRemoveSolver);
	CPPUNIT_TEST(testClingoStats);
	CPPUNIT_TEST(testClingoStatsKeyIntegrity);
	CPPUNIT_TEST(testClingoStatsWithoutStats);
#if CLASP_HAS_THREADS
	CPPUNIT_TEST(testClingoSolverStatsRemainValid);
	CPPUNIT_TEST(testShareModeRegression);
	CPPUNIT_TEST(testAsyncSolveTrivialUnsat);
	CPPUNIT_TEST(testInterruptBeforeSolve);
	CPPUNIT_TEST(testCancelAsyncOperation);
	CPPUNIT_TEST(testAsyncResultDtorCancelsOp);
	CPPUNIT_TEST(testDestroyAsyncResultNoFacade);
	CPPUNIT_TEST(testDestroyDanglingAsyncResult);
	CPPUNIT_TEST(testCancelDanglingAsyncOperation);
#endif
	CPPUNIT_TEST(testGenSolveTrivialUnsat);
	CPPUNIT_TEST(testInterruptBeforeGenSolve);
	CPPUNIT_TEST(testGenSolveWithLimit);
	CPPUNIT_TEST(testCancelGenSolve);
	CPPUNIT_TEST(testGenDtorCancelsSolve);
	CPPUNIT_TEST(testGenStopFromHandler);
#if CLASP_HAS_THREADS
	CPPUNIT_TEST(testGenSolveMt);
#endif
	CPPUNIT_TEST(testUserConfigurator);
	CPPUNIT_TEST(testUserHeuristic);
	CPPUNIT_TEST_SUITE_END();
public:
	typedef ClaspFacade::Result Result;
	void addProgram(Clasp::Asp::LogicProgram& prg) {
		lpAdd(prg, "a :- not b. b :- not a.");
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

	void testPrepareSolvedProgram() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		addProgram(asp);
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 2);
		CPPUNIT_ASSERT(libclasp.summary().step == 0);

		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 2);
		CPPUNIT_ASSERT(libclasp.summary().step == 1);
	}
	void testSolveSolvedProgram() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		addProgram(asp);
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());

		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 2);
		CPPUNIT_ASSERT(libclasp.summary().step == 1);
	}
	void testSolveAfterStopConflict() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		addProgram(asp);
		struct PP : public PostPropagator {
			uint32 priority() const { return priority_reserved_msg; }
			bool propagateFixpoint(Solver& s, PostPropagator*) {
				s.setStopConflict();
				return false;
			}
		} pp;
		libclasp.ctx.master()->addPost(&pp);
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().unknown());
		libclasp.ctx.master()->removePost(&pp);
		libclasp.update();
		CPPUNIT_ASSERT(libclasp.solve().sat());
	}
	void testRestartAfterPrepare() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		libclasp.startAsp(config);
		libclasp.prepare();
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config);
		CPPUNIT_ASSERT(!asp.frozen());
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
		CPPUNIT_ASSERT(libclasp.interrupt(1) == false);
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve(LitVec(), &fh).interrupted());
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
		CPPUNIT_ASSERT(libclasp.interrupt(1) == false);
		CPPUNIT_ASSERT(!libclasp.solved());
		CPPUNIT_ASSERT(libclasp.solve(LitVec(), &fh).interrupted());
		CPPUNIT_ASSERT(libclasp.solved());
		CPPUNIT_ASSERT(fh.finished == 1);
	}

	void testInterruptAfterSolveInterruptsNext() {
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
		CPPUNIT_ASSERT(!libclasp.solve(LitVec(), &fh).interrupted());
		CPPUNIT_ASSERT(fh.finished == 1);
		CPPUNIT_ASSERT(libclasp.solved());
		CPPUNIT_ASSERT(!libclasp.interrupted());
		CPPUNIT_ASSERT(libclasp.interrupt(1) == false);
		CPPUNIT_ASSERT(libclasp.solve(LitVec(), &fh).interrupted());
		CPPUNIT_ASSERT(fh.finished == 2);
	}
	void testInterruptBeforeUpdateInterruptsNext() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		addProgram(asp);
		libclasp.prepare();
		libclasp.interrupt(1);
		libclasp.update(false);
		CPPUNIT_ASSERT(!libclasp.interrupted());
		CPPUNIT_ASSERT(libclasp.solve().interrupted());
	}
	void testUpdateCanIgnoreQueuedSignals() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		addProgram(asp);
		libclasp.prepare();
		libclasp.interrupt(1);
		libclasp.update(false, SIG_IGN);
		CPPUNIT_ASSERT(!libclasp.solve().interrupted());
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
		libclasp.solve(assume, &mh1);
		CPPUNIT_ASSERT(mh1.models == 1);
		libclasp.update();
		asp.freeze(ext, value_false);
		assume.assign(1, asp.getLiteral(2));
		mh2.exp.push_back(~asp.getLiteral(1));
		mh2.exp.push_back(asp.getLiteral(2));
		mh2.exp.push_back(~asp.getLiteral(ext));
		libclasp.solve(assume, &mh2);
		CPPUNIT_ASSERT(mh2.models == 1);
		libclasp.update();
		libclasp.solve();
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 2);
	}

	void testPrepareTooStrongBound() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		config.solve.optBound.assign(1, 0);
		lpAdd(libclasp.startAsp(config, true),
			"a :-not b.\n"
			"b :-not a.\n"
			"c.\n"
			"#minimize{c, a, b}.");

		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().unsat());
	}

	void testComputeBraveViaOutput() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		config.solve.enumMode  = EnumOptions::enum_brave;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp,
			"x1 :- not x2.\n"
			"x2 :- not x1.\n"
			"x3 :- not x1.\n"
			"#output a : x1.\n"
			"#output b : x2.\n");
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		const Model& m = *libclasp.summary().model();
		CPPUNIT_ASSERT(m.isDef(asp.getLiteral(1)));
		CPPUNIT_ASSERT(m.isDef(asp.getLiteral(2)));
	}
	void testComputeQuery() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		config.solve.enumMode = EnumOptions::enum_query;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp,
			"{a,b}."
			"c :- a.\n"
			"c :- b.\n"
			"c :- not a, not b.\n"
			"#output a : a.\n"
			"#output b : b.\n"
			"#output c : c.\n");
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		const Model& m = *libclasp.summary().model();
		CPPUNIT_ASSERT(m.isDef(asp.getLiteral(3)));
		CPPUNIT_ASSERT(!m.isDef(asp.getLiteral(1)));
		CPPUNIT_ASSERT(!m.isDef(asp.getLiteral(2)));
	}
	void testComputeBraveViaProject() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		config.solve.enumMode  = EnumOptions::enum_brave;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp,
			"x1 :- not x2.\n"
			"x2 :- not x1.\n"
			"x3 :- not x1.\n"
			"#project {x1,x2,x3}.");
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		const Model& m = *libclasp.summary().model();
		CPPUNIT_ASSERT(m.isDef(asp.getLiteral(1)));
		CPPUNIT_ASSERT(m.isDef(asp.getLiteral(2)));
	}
	void testOptN() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		config.solve.optMode   = MinimizeMode_t::enumOpt;
		lpAdd(libclasp.startAsp(config, false),
			"{x1;x2;x3}.\n"
			":- not x1, not x2, not x3.\n"
			":- x2, not x1.\n"
			":- x3, not x1.\n"
			"#minimize{not x1}@0.\n"
			"#minimize{x1}@1.");
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT_EQUAL(uint64(4), libclasp.summary().optimal());
	}
	void testOptNGenerator() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		config.solve.optMode   = MinimizeMode_t::enumOpt;
		lpAdd(libclasp.startAsp(config, false),
			"{x1;x2;x3}.\n"
			":- not x1, not x2, not x3.\n"
			":- x2, not x1.\n"
			":- x3, not x1.\n"
			"#minimize{not x1}@0.\n"
			"#minimize{x1}@1.");
		libclasp.prepare();
		unsigned num = 0, opt = 0;
		for (Clasp::ClaspFacade::SolveHandle it = libclasp.solve(SolveMode_t::Yield); it.next();) {
			++num;
			opt += it.model()->opt;
		}
		CPPUNIT_ASSERT(num > opt && opt == 4);
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
				lpAdd(asp,
				"x1 :- x2.\n"
				"x2 :- x1.\n"
				"x1 :- x3.\n"
				":- not x1.\n"
				"#external x3.");
				break;
			case 1:
				lpAdd(asp,
					"x3 :- x4.\n"
					"x4 :- x3.\n"
					"x4 :- x5.\n"
					"#external x5.");
				break;
			case 2:
				lpAdd(asp,
					"x5 :- x6, x7.\n"
					"x6 :- not x3.\n"
					"x7 :- not x1, not x2.\n"
					"{x5}.");
				break;
			case 3:
				lpAdd(asp, "{x8}.");
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
		lpAdd(asp, "{x1}.");
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 2);
		CPPUNIT_ASSERT(libclasp.update().ok());
		lpAdd(asp, "{x2}.");
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 4);
	}
	void testIncrementalCons() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		config.solve.enumMode  = EnumOptions::enum_cautious;
		lpAdd(libclasp.startAsp(config, true),
			"{x1;x2;x3}.\n"
			"#output a : x1.\n"
			"#output b : x2.\n"
			"#output c : x3.\n");
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
		lpAdd(libclasp.startAsp(config, true),
			"{x1;x2;x3}.\n"
			"#minimize{x1, x2, x3}.\n");
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum < 8u);
		libclasp.update().ctx()->removeMinimize();
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 8);
	}
	void testIncrementalMinIgnore() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.optMode = MinimizeMode_t::ignore;
		config.solve.numModels = 0;
		lpAdd(libclasp.startAsp(config, true),
			"{x1;x2}.\n"
			"#minimize{x1, x2}.\n");
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 4u);
		config.solve.optMode = MinimizeMode_t::optimize;
		libclasp.update(true);
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 1u);
	}
	void testIncrementalMinAdd() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		config.solve.enumMode  = EnumOptions::enum_auto;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp,
			"{x1;x2}.\n"
			"#minimize{not x1}.\n");
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().model()->isTrue(asp.getLiteral(1)));
		libclasp.update();
		lpAdd(asp, "#minimize{not x2}.");
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().model()->isTrue(asp.getLiteral(1)));
		CPPUNIT_ASSERT(libclasp.summary().model()->isTrue(asp.getLiteral(2)));
	}
	void testUpdateConfig() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		config.solve.enumMode  = EnumOptions::enum_auto;
		config.addSolver(0).heuId  = Heuristic_t::Berkmin;
		lpAdd(libclasp.startAsp(config, true), "{x1;x2;x3}.");
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		config.addSolver(0).heuId = Heuristic_t::Vsids;
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
		lpAdd(asp, "{x1;x2}. #output b : x2.");
		libclasp.prepare();
		CPPUNIT_ASSERT(static_cast<const ModelEnumerator*>(libclasp.enumerator())->project(asp.getLiteral(2).var()));
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 2);
		config.solve.project = 0;
		libclasp.update(true);
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 4);
		config.solve.project = 1;
		libclasp.update(true);
		lpAdd(asp, "{x3;x4}. #output y : x4.");
		libclasp.prepare();
		CPPUNIT_ASSERT(static_cast<const ModelEnumerator*>(libclasp.enumerator())->project(asp.getLiteral(2).var()));
		CPPUNIT_ASSERT(static_cast<const ModelEnumerator*>(libclasp.enumerator())->project(asp.getLiteral(4).var()));
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT_EQUAL(uint64(4), libclasp.summary().numEnum);
	}
	void testIncrementalDomRecUpdate() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		config.solve.enumMode  = EnumOptions::enum_dom_record;
		config.addSolver(0).heuId  = Heuristic_t::Domain;
		config.addSolver(0).heuristic.domMod  = HeuParams::mod_false;
		config.addSolver(0).heuristic.domPref = HeuParams::pref_show;
		lpAdd(libclasp.startAsp(config, true),
			"{x1;x2}.\n"
			":- not x1, not x2.\n"
			"#output b : x2.\n"
			"#output a : x1.\n");
		CPPUNIT_ASSERT(libclasp.solve().sat());
		// {a} ; {b}
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 2);

		config.addSolver(0).heuristic.domMod = HeuParams::mod_true;
		libclasp.update(true);
		CPPUNIT_ASSERT(libclasp.solve().sat());
		// {a,b}
		CPPUNIT_ASSERT(libclasp.summary().numEnum == 1);
	}
	void testIncrementalConfigUpdateBug() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.asp.erMode = Asp::LogicProgram::mode_transform;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp, "{x1;x2}.");
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.ctx.ok());
		CPPUNIT_ASSERT(asp.stats.auxAtoms == 2);
		config.asp.erMode = Asp::LogicProgram::mode_native;
		libclasp.update(true);
		lpAdd(asp, "{x3;x4}.");
		libclasp.prepare();
		CPPUNIT_ASSERT(asp.stats.auxAtoms == 0);
	}

	void testIncrementalLookaheadAddHeuristic() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.addSolver(0).lookType = Var_t::Atom;
		lpAdd(libclasp.startAsp(config, true), "{x1;x2}.");
		libclasp.prepare();
		PostPropagator* look = libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look);
		CPPUNIT_ASSERT(look && look->next == 0);
		config.addSolver(0).heuId = Heuristic_t::Unit;
		libclasp.update(true);
		libclasp.prepare();
		look = libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look);
		CPPUNIT_ASSERT(look && look->next == 0);
	}
	void testIncrementalDisableLookahead() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.addSolver(0).lookType = Var_t::Atom;
		lpAdd(libclasp.startAsp(config, true), "{x1;x2}.");
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look));
		config.addSolver(0).lookType = 0;
		libclasp.update(true);
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look) == 0);
	}
	void testIncrementalChangeLookahead() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.addSolver(0).lookType = Var_t::Atom;
		lpAdd(libclasp.startAsp(config, true), "{x1;x2}.");
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look));
		config.addSolver(0).lookType = Var_t::Body;
		libclasp.update(true);
		libclasp.prepare();
		Lookahead* look = static_cast<Lookahead*>(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look));
		CPPUNIT_ASSERT(look && look->score.types == Var_t::Body );
	}
	void testIncrementalExtendLookahead() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.addSolver(0).lookType = Var_t::Atom;
		config.addSolver(0).lookOps  = 3;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp, "{x1;x2}.");
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look));
		config.addSolver(0).lookOps  = 0;
		libclasp.update(true);
		lpAdd(asp, "{x3;x4}.");
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
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp, "{x1;x2}.");
		libclasp.prepare();
		CPPUNIT_ASSERT(!isSentinel(libclasp.ctx.stepLiteral()));
#if CLASP_HAS_THREADS
		config.solve.setSolvers(2);
		libclasp.update(true);
		lpAdd(asp, "{x3;x4}.");
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.ctx.concurrency() == 2 && libclasp.ctx.hasSolver(1));
#endif
	}

	void testIncrementalRemoveSolver() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.solve.numModels = 0;
		config.solve.setSolvers(4);
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp,
			"{x1;x2;x4;x3}.\n"
			":- 3 {x1, x2, x3, x4}.\n");
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat());
		CPPUNIT_ASSERT_EQUAL(uint64(11), libclasp.summary().numEnum);

		config.solve.setSolvers(1);
		libclasp.update(true);
		lpAdd(asp, ":- x1, x2.\n");
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat() && libclasp.summary().numEnum == 10);

		config.solve.setSolvers(2);
		libclasp.update(true);
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().sat() && libclasp.summary().numEnum == 10);
	}

	void testClingoStats() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.stats = 2;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp, "{x1;x2;x3}. #minimize{x1, x2}.");
		libclasp.prepare();
		libclasp.solve();
		Potassco::AbstractStatistics* stats = libclasp.getStats();
		typedef Potassco::AbstractStatistics::Key_t Key_t;
		Key_t r = stats->root();
		CPPUNIT_ASSERT(stats->type(r) == Potassco::Statistics_t::Map);
		Key_t lp = stats->get(r, "problem.lp");
		Key_t s = stats->get(r, "solving");
		Key_t m = stats->get(r, "summary.models");
		CPPUNIT_ASSERT(stats->type(lp) == Potassco::Statistics_t::Map);
		CPPUNIT_ASSERT(stats->value(stats->get(lp, "rules")) == double(asp.stats.rules[0].sum()));
		CPPUNIT_ASSERT(stats->value(stats->get(m, "enumerated")) == double(libclasp.summary().numEnum));
		Key_t solvers = stats->get(s, "solvers");
		CPPUNIT_ASSERT(stats->value(stats->get(solvers, "choices")) == double(libclasp.ctx.master()->stats.choices));
		Key_t costs = stats->get(r, "summary.costs");
		CPPUNIT_ASSERT(stats->type(costs) == Potassco::Statistics_t::Array);
		CPPUNIT_ASSERT(stats->value(stats->at(costs, 0)) == double(libclasp.summary().costs()->at(0)));
		Key_t solver = stats->get(s, "solver");
		CPPUNIT_ASSERT(stats->type(solver) == Potassco::Statistics_t::Array);
		Key_t s0 = stats->at(solver, 0);
		CPPUNIT_ASSERT(stats->type(s0) == Potassco::Statistics_t::Map);
		CPPUNIT_ASSERT(stats->value(stats->get(s0, "choices")) == double(libclasp.ctx.master()->stats.choices));
		std::vector<std::string> keys;
		getKeys(*stats, r, keys, "");
		CPPUNIT_ASSERT(!keys.empty());
		for (std::vector<std::string>::const_iterator it = keys.begin(), end = keys.end(); it != end; ++it) {
			CPPUNIT_ASSERT(stats->type(stats->get(r, it->c_str())) == Potassco::Statistics_t::Value);
		}
		CPPUNIT_ASSERT_MESSAGE("unexpected number of statistics", keys.size() == 236);
	}
	void testClingoStatsKeyIntegrity() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.stats = 2;
		config.addTesterConfig()->stats = 2;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp, "{x1;x2;x3}. #minimize{x1, x2}.");
		libclasp.prepare();
		libclasp.solve();
		typedef Potassco::AbstractStatistics::Key_t Key_t;
		Potassco::AbstractStatistics* stats = libclasp.getStats();
		Key_t lp = stats->get(stats->root(), "problem.lp");
		Key_t sccs = stats->get(lp, "sccs");
		Key_t m0 = stats->get(stats->root(), "summary.costs.0");
		CPPUNIT_ASSERT_THROW(stats->get(stats->root(), "hcc"), std::logic_error);
		CPPUNIT_ASSERT(stats->value(m0) == (double)libclasp.summary().costs()->at(0));
		libclasp.update();
		lpAdd(asp,
			"x4 | x5 :- x6, not x1."
			"x6 :- x4, x5, not x2."
			"x6 :- not x1."
		);
		libclasp.prepare();
		libclasp.solve();
		CPPUNIT_ASSERT(asp.stats.sccs == 1);
		CPPUNIT_ASSERT(asp.stats.nonHcfs == 1);
		CPPUNIT_ASSERT(lp == stats->get(stats->root(), "problem.lp"));
		CPPUNIT_ASSERT(sccs == stats->get(lp, "sccs"));
		CPPUNIT_ASSERT(m0 == stats->get(stats->root(), "summary.costs.0"));
		CPPUNIT_ASSERT(stats->value(sccs) == asp.stats.sccs);
		CPPUNIT_ASSERT(stats->value(m0) == (double)libclasp.summary().costs()->at(0));
		Key_t hcc0 = stats->get(stats->root(), "problem.hcc.0");
		Key_t hcc0Vars = stats->get(hcc0, "vars");
		CPPUNIT_ASSERT(stats->value(hcc0Vars) != 0.0);
		libclasp.update();
		libclasp.ctx.removeMinimize();
		lpAdd(asp,
			"x7 | x8 :- x9, not x1."
			"x9 :- x7, x8, not x2."
			"x9 :- not x1."
		);
		libclasp.prepare();
		libclasp.solve();
		CPPUNIT_ASSERT(libclasp.summary().lpStats()->sccs == 2);
		CPPUNIT_ASSERT(libclasp.summary().lpStats()->nonHcfs == 2);
		CPPUNIT_ASSERT(lp == stats->get(stats->root(), "problem.lp"));
		CPPUNIT_ASSERT(sccs == stats->get(lp, "sccs"));
		CPPUNIT_ASSERT_THROW(stats->value(m0), std::logic_error);
		CPPUNIT_ASSERT(stats->value(hcc0Vars) != 0.0);
		CPPUNIT_ASSERT(stats->value(stats->get(stats->root(), "problem.hcc.1.vars")) != 0.0);
	}
	void testClingoStatsWithoutStats() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp,
			"{x1,x2,x3}."
			"x3 | x4 :- x5, not x1."
			"x5 :- x4, x3, not x2."
			"x5 :- not x1."
		);
		libclasp.solve();
		typedef Potassco::AbstractStatistics::Key_t Key_t;
		Potassco::AbstractStatistics* stats = libclasp.getStats();
		Key_t root = stats->root();
		CPPUNIT_ASSERT(stats->size(root) == 3);
		CPPUNIT_ASSERT(stats->get(root, "solving") != root);
		CPPUNIT_ASSERT(stats->get(root, "problem") != root);
		CPPUNIT_ASSERT(stats->get(root, "summary") != root);
		CPPUNIT_ASSERT_THROW_MESSAGE("accu requires stats", stats->get(root, "solving.accu"), std::out_of_range);
	}
	void getKeys(const Potassco::AbstractStatistics& stats, Potassco::AbstractStatistics::Key_t k, std::vector<std::string>& out, const std::string& p) {
		if (stats.type(k) == Potassco::Statistics_t::Map) {
			for (uint32 i = 0, end = stats.size(k); i != end; ++i) {
				const char* sk = stats.key(k, i);
				getKeys(stats, stats.get(k, sk), out, p.empty() ? sk : std::string(p).append(".").append(sk));
			}
		}
		else if (stats.type(k) == Potassco::Statistics_t::Array) {
			char buf[12];
			for (uint32 i = 0, end = stats.size(k); i != end; ++i) {
				getKeys(stats, stats.at(k, i), out, std::string(p).append(".").append(clasp_format(buf, 12, "%d", i)));
			}
		}
		else {
			out.push_back(p);
		}
	}
#if CLASP_HAS_THREADS
	void testClingoSolverStatsRemainValid() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.stats = 2;
		config.solve.algorithm.threads = 2;
		config.solve.numModels = 0;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp, "{x1,x2,x3}.");
		libclasp.prepare();
		libclasp.solve();
		typedef Potassco::AbstractStatistics::Key_t Key_t;
		Potassco::AbstractStatistics* stats = libclasp.getStats();
		Key_t s = stats->get(stats->root(), "solving.solver");
		Key_t s1 = stats->at(s, 1);
		Key_t s1c = stats->get(stats->at(s, 1), "choices");
		Key_t s0c = stats->get(stats->at(s, 0), "choices");
		CPPUNIT_ASSERT(stats->size(s) == 2);
		CPPUNIT_ASSERT(stats->value(s1c) + stats->value(s0c) == stats->value(stats->get(stats->root(), "solving.solvers.choices")));
		config.solve.algorithm.threads = 1;
		libclasp.update(true);
		libclasp.solve();
		CPPUNIT_ASSERT_MESSAGE("solver stats are not removed", stats->size(s) == 2);
		CPPUNIT_ASSERT_MESSAGE("solver stats remain valid", stats->at(s, 1) == s1);
		CPPUNIT_ASSERT(stats->value(s1c) == 0.0);
		CPPUNIT_ASSERT(stats->value(s0c) == stats->value(stats->get(stats->root(), "solving.solvers.choices")));
		config.solve.algorithm.threads = 2;
		libclasp.update(true);
		libclasp.solve();
		CPPUNIT_ASSERT(stats->value(s1c) + stats->value(s0c) == stats->value(stats->get(stats->root(), "solving.solvers.choices")));
	}
	void testShareModeRegression() {
		Clasp::ClaspFacade libclasp;
		Clasp::ClaspConfig config;
		config.shareMode = ContextParams::share_auto;
		config.solve.algorithm.threads = 2;
		libclasp.startSat(config).prepareProblem(2);
		libclasp.prepare();
		CPPUNIT_ASSERT_EQUAL(true, libclasp.ctx.physicalShare(Constraint_t::Static));
		CPPUNIT_ASSERT_EQUAL(true, libclasp.ctx.physicalShare(Constraint_t::Conflict));
	}
	typedef ClaspFacade::SolveHandle AsyncResult;
	void testAsyncSolveTrivialUnsat() {
		ClaspConfig config;
		ClaspFacade libclasp;
		config.solve.numModels = 0;
		lpAdd(libclasp.startAsp(config, true), "x1 :- not x1.");
		libclasp.prepare();
		AsyncResult it = libclasp.solve(SolveMode_t::Async|SolveMode_t::Yield);
		CPPUNIT_ASSERT(it.get().unsat());
	}
	void testInterruptBeforeSolve() {
		ClaspConfig config;
		ClaspFacade libclasp;
		config.solve.numModels = 0;
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		libclasp.prepare();
		libclasp.interrupt(2);
		AsyncResult it = libclasp.solve(SolveMode_t::AsyncYield);
		CPPUNIT_ASSERT(it.get().interrupted());
	}
	void testCancelAsyncOperation() {
		ClaspConfig config;
		ClaspFacade libclasp;
		config.solve.numModels = 0;
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		libclasp.prepare();
		AsyncResult it = libclasp.solve(SolveMode_t::AsyncYield);
		while (it.model()) {
			it.cancel();
		}
		CPPUNIT_ASSERT_EQUAL(uint64(1), libclasp.summary().numEnum);
		CPPUNIT_ASSERT(!libclasp.solving() && it.interrupted());
		libclasp.update();
		libclasp.prepare();
		it = libclasp.solve(SolveMode_t::AsyncYield);
		int mod = 0;
		while (it.model()) { ++mod; it.resume(); }
		CPPUNIT_ASSERT(!libclasp.solving() && mod == 2);
	}
	void testAsyncResultDtorCancelsOp() {
		ClaspConfig config;
		ClaspFacade libclasp;
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		libclasp.prepare();
		{ AsyncResult it = libclasp.solve(SolveMode_t::AsyncYield); }
		CPPUNIT_ASSERT(!libclasp.solving() && libclasp.result().interrupted());
	}
	void testDestroyAsyncResultNoFacade() {
		{
			ClaspConfig  config;
			ClaspFacade* libclasp = new ClaspFacade();
			lpAdd(libclasp->startAsp(config, true), "{x1}.");
			libclasp->prepare();
			AsyncResult res( libclasp->solve(SolveMode_t::AsyncYield) );
			delete libclasp;
			CPPUNIT_ASSERT(res.interrupted());
		}
	}
	void testDestroyDanglingAsyncResult() {
		ClaspConfig  config;
		ClaspFacade  libclasp;
		AsyncResult* handle = 0;
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		libclasp.prepare();
		handle = new AsyncResult( libclasp.solve(SolveMode_t::Async) );
		handle->wait();
		libclasp.update();
		libclasp.prepare();
		AsyncResult* it = new AsyncResult(libclasp.solve(SolveMode_t::AsyncYield));
		delete handle;
		CPPUNIT_ASSERT(!it->interrupted() && libclasp.solving());
		CPPUNIT_ASSERT_NO_THROW(delete it);
		CPPUNIT_ASSERT(!libclasp.solving());
	}
	void testCancelDanglingAsyncOperation() {
		ClaspConfig config;
		ClaspFacade libclasp;

		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		libclasp.prepare();
		AsyncResult step0 = libclasp.solve(SolveMode_t::Async);
		step0.wait();
		libclasp.update();
		libclasp.prepare();
		AsyncResult step1 = libclasp.solve(SolveMode_t::AsyncYield);

		step0.cancel();
		CPPUNIT_ASSERT(libclasp.solving());
		step1.cancel();
		CPPUNIT_ASSERT(!libclasp.solving());
	}
#endif
	void testGenSolveTrivialUnsat() {
		ClaspConfig config;
		ClaspFacade libclasp;
		config.solve.numModels = 0;
		lpAdd(libclasp.startAsp(config, true), "x1 :- not x1.");
		libclasp.prepare();
		ClaspFacade::SolveHandle it = libclasp.solve(SolveMode_t::Yield);
		CPPUNIT_ASSERT(it.get().exhausted());
		CPPUNIT_ASSERT(!it.model());
	}
	void testInterruptBeforeGenSolve() {
		ClaspConfig config;
		ClaspFacade libclasp;
		config.solve.numModels = 0;
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		libclasp.prepare();
		libclasp.interrupt(2);
		ClaspFacade::SolveHandle it = libclasp.solve(SolveMode_t::Yield);
		CPPUNIT_ASSERT(it.get().interrupted());
		CPPUNIT_ASSERT(!it.model());
	}
	void testGenSolveWithLimit() {
		ClaspConfig config;
		ClaspFacade libclasp;
		lpAdd(libclasp.startAsp(config, true), "{x1;x2;x3}.");
		libclasp.prepare();
		for (int i = 1; i != 9; ++i) {
			unsigned got = 0, exp = i;
			config.solve.numModels = i % 8;
			libclasp.update(true);
			for (ClaspFacade::SolveHandle it = libclasp.solve(SolveMode_t::Yield); it.next(); ) {
				CPPUNIT_ASSERT(got != exp);
				++got;
			}
			CPPUNIT_ASSERT_EQUAL(exp, got);
		}
	}

	void testCancelGenSolve() {
		ClaspConfig config;
		ClaspFacade libclasp;
		config.solve.numModels = 0;
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		libclasp.prepare();
		unsigned mod = 0;
		ClaspFacade::SolveHandle it = libclasp.solve(SolveMode_t::Yield);
		for (; it.next();) {
			CPPUNIT_ASSERT(it.model()->num == ++mod);
			it.cancel();
			break;
		}
		CPPUNIT_ASSERT(!libclasp.solving() && !it.get().exhausted() && mod == 1);
		libclasp.update();
		libclasp.prepare();
		mod = 0;
		for (ClaspFacade::SolveHandle j = libclasp.solve(SolveMode_t::Yield); j.next(); ++mod) {
			;
		}
		CPPUNIT_ASSERT(!libclasp.solving() && mod == 2);
	}
	void testGenDtorCancelsSolve() {
		ClaspConfig config;
		ClaspFacade libclasp;
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		libclasp.prepare();
		{ libclasp.solve(SolveMode_t::Yield); }
		CPPUNIT_ASSERT(!libclasp.solving() && !libclasp.result().exhausted());
	}
	void testGenStopFromHandler() {
		ClaspConfig config;
		ClaspFacade libclasp;
		config.solve.numModels = 0;
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		libclasp.prepare();
		struct Handler : EventHandler {
			virtual bool onModel(const Solver&, const Model&) {
				return false;
			}
		} h;
		libclasp.ctx.setEventHandler(&h);
		int mod = 0;
		for (ClaspFacade::SolveHandle g = libclasp.solve(SolveMode_t::Yield); g.next(); ++mod) {
			;
		}
		CPPUNIT_ASSERT(mod == 1);
	}
#if CLASP_HAS_THREADS
	void testGenSolveMt() {
		ClaspConfig config;
		ClaspFacade libclasp;
		config.solve.numModels = 0;
		config.solve.algorithm.threads = 2;
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		libclasp.prepare();
		int mod = 0;
		for (ClaspFacade::SolveHandle it = libclasp.solve(SolveMode_t::Yield); it.next(); ++mod) {
			;
		}
		CPPUNIT_ASSERT(!libclasp.solving() && mod == 2);
	}
#endif
	void testUserConfigurator() {
		ClaspConfig config;
		struct MyAddPost : public ClaspConfig::Configurator {
			MyAddPost() : called(false) {}
			virtual bool addPost(Solver&) { return called = true; }
			bool called;
		} myAddPost;
		config.addConfigurator(&myAddPost);
		ClaspFacade libclasp;
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		libclasp.prepare();
		CPPUNIT_ASSERT_EQUAL(true, myAddPost.called);
	}
	void testUserHeuristic() {
		struct MyHeu {
			static DecisionHeuristic* creator(Heuristic_t::Type, const HeuParams&) { throw MyHeu(); }
		};
		ClaspConfig config;
		config.setHeuristicCreator(&MyHeu::creator);
		ClaspFacade libclasp;
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		CPPUNIT_ASSERT_THROW(libclasp.prepare(), MyHeu);
	}
};
CPPUNIT_TEST_SUITE_REGISTRATION(FacadeTest);

class MyProp : public Potassco::AbstractPropagator {
public:
	MyProp() : fire(lit_false()), clProp(Potassco::Clause_t::Learnt) {}
	virtual void propagate(Potassco::AbstractSolver& s, const ChangeList& changes) {
		map(changes);
		addClause(s);
	}
	virtual void undo(const Potassco::AbstractSolver&, const ChangeList& changes) {
		map(changes);
	}
	virtual void check(Potassco::AbstractSolver& s) {
		const Potassco::AbstractAssignment& assign = s.assignment();
		for (Potassco::LitVec::const_iterator it = clause.begin(), end = clause.end(); it != end; ++it) {
			if (assign.isTrue(*it)) { return; }
		}
		if (!clause.empty()) { s.addClause(Potassco::toSpan(clause)); }
	}
	void map(const ChangeList& changes) {
		change.clear();
		for (const Potassco::Lit_t* x = Potassco::begin(changes); x != Potassco::end(changes); ++x) {
			change.push_back(decodeLit(*x));
		}
	}
	bool addClause(Potassco::AbstractSolver& s) {
		if (!s.assignment().isTrue(encodeLit(fire))) {
			return true;
		}
		return s.addClause(Potassco::toSpan(clause), clProp) && s.propagate();
	}
	void addToClause(Literal x) {
		clause.push_back(encodeLit(x));
	}
	Literal  fire;
	LitVec change;
	Potassco::LitVec   clause;
	Potassco::Clause_t clProp;
};
class ClingoPropagatorTest : public CppUnit::TestFixture {
	CPPUNIT_TEST_SUITE(ClingoPropagatorTest);
	CPPUNIT_TEST(testAssignment);
	CPPUNIT_TEST(testPropagateChange);
	CPPUNIT_TEST(testAddClause);
	CPPUNIT_TEST(testAddUnitClause);
	CPPUNIT_TEST(testAddUnitClauseWithUndo);
	CPPUNIT_TEST(testAddUnsatClause);
	CPPUNIT_TEST(testAddEmptyClause);
	CPPUNIT_TEST(testAttachToSolver);
	CPPUNIT_TEST(testAddClauseOnModel);
	CPPUNIT_TEST(testAddConflictOnModel);
	CPPUNIT_TEST(testAddStatic);
	CPPUNIT_TEST(testAddVolatile);
	CPPUNIT_TEST(testAddVolatileStatic);
	CPPUNIT_TEST(testPushVariable);
	CPPUNIT_TEST(testAuxVarMakesClauseVolatile);
	CPPUNIT_TEST(testRootLevelBug);
	CPPUNIT_TEST(testLookaheadBug);
	CPPUNIT_TEST_SUITE_END();
public:
	void setUp() {
		tp = new Clasp::ClingoPropagatorInit(prop);
	}
	void tearDown() {
		delete tp;
	}
	void testAssignment() {
		class Prop : public Potassco::AbstractPropagator {
		public:
			Prop() {}
			virtual void propagate(Potassco::AbstractSolver&, const ChangeList&)  {}
			virtual void undo(const Potassco::AbstractSolver&, const ChangeList&) {}
			virtual void check(Potassco::AbstractSolver& s) {
				const Potassco::AbstractAssignment& a = s.assignment();
				CPPUNIT_ASSERT(!a.hasConflict());
				CPPUNIT_ASSERT(a.level() == 2);
				CPPUNIT_ASSERT(a.value(v1) == Potassco::Value_t::True);
				CPPUNIT_ASSERT(a.value(v2) == Potassco::Value_t::False);
				CPPUNIT_ASSERT(a.isTrue(v1));
				CPPUNIT_ASSERT(a.isFalse(v2));
				CPPUNIT_ASSERT(a.isTrue(Potassco::neg(v2)));
				CPPUNIT_ASSERT(a.level(v1) == 1);
				CPPUNIT_ASSERT(a.level(v2) == 2);
				CPPUNIT_ASSERT(!a.hasLit(v2+1));
				CPPUNIT_ASSERT(a.decision(0) == encodeLit(lit_true()));
				CPPUNIT_ASSERT(a.decision(1) == v1);
				CPPUNIT_ASSERT(a.decision(2) == Potassco::neg(v2));
			}
			Potassco::Lit_t v1, v2;
		} prop;
		addVars(2);
		prop.v1 = encodeLit(posLit(v[1]));
		prop.v2 = encodeLit(posLit(v[2]));
		MyInit pp(prop);
		pp.addPost(*ctx.master());
		ctx.endInit();
		ctx.master()->assume(posLit(v[1])) && ctx.master()->propagate();
		ctx.master()->assume(negLit(v[2])) && ctx.master()->propagate();
		ctx.master()->search(0, 0);
	}

	void testPropagateChange() {
		addVars(5);
		tp->addWatch(posLit(v[1]));
		tp->addWatch(posLit(v[1])); // ignore duplicates
		tp->addWatch(posLit(v[2]));
		tp->addWatch(posLit(v[3]));
		tp->addWatch(negLit(v[3]));
		tp->addWatch(negLit(v[4]));
		tp->addPost(*ctx.master());
		ctx.endInit();
		Solver& s = *ctx.master();
		s.assume(posLit(v[1])) && s.propagate();
		CPPUNIT_ASSERT(prop.change.size() == 1 && prop.change[0] == posLit(v[1]));

		s.assume(negLit(v[4])) && s.force(posLit(v[2]), 0) && s.propagate();
		CPPUNIT_ASSERT(prop.change.size() == 2 && prop.change[0] == negLit(v[4]) && prop.change[1] == posLit(v[2]));
		prop.change.clear();
		s.undoUntil(s.decisionLevel()-1);
		CPPUNIT_ASSERT(prop.change.size() == 2 && prop.change[0] == negLit(v[4]) && prop.change[1] == posLit(v[2]));
		s.undoUntil(s.decisionLevel()-1);
		CPPUNIT_ASSERT(prop.change.size() == 1 && prop.change[0] == posLit(v[1]));
		prop.change.clear();
		s.assume(negLit(v[2])) && s.propagate();
		CPPUNIT_ASSERT(prop.change.empty());
	}
	void testAddClause() {
		addVars(3);
		tp->addWatch(prop.fire = negLit(v[3]));
		prop.addToClause(posLit(v[1]));
		prop.addToClause(posLit(v[2]));
		tp->addPost(*ctx.master());
		ctx.endInit();
		Solver& s = *ctx.master();
		s.assume(negLit(v[3])) && s.propagate();
		CPPUNIT_ASSERT(ctx.numLearntShort() == 1);
	}
	void testAddUnitClause() {
		addVars(3);
		tp->addWatch(prop.fire = negLit(v[3]));
		prop.addToClause(posLit(v[1]));
		prop.addToClause(posLit(v[2]));
		tp->addPost(*ctx.master());
		ctx.endInit();
		Solver& s = *ctx.master();
		s.assume(negLit(v[2])) && s.propagate();
		s.assume(negLit(v[3])) && s.propagate();
		CPPUNIT_ASSERT(ctx.numLearntShort() == 1);
		CPPUNIT_ASSERT(s.isTrue(posLit(v[1])));
		CPPUNIT_ASSERT(prop.change.size() == 1 && prop.change[0] == negLit(v[3]));
	}
	void testAddUnitClauseWithUndo() {
		addVars(5);
		prop.fire = posLit(v[5]);
		tp->addWatch(posLit(v[3]));
		tp->addWatch(posLit(v[5]));
		prop.addToClause(posLit(v[1]));
		prop.addToClause(posLit(v[2]));
		prop.addToClause(posLit(v[3]));
		tp->addPost(*ctx.master());
		ctx.endInit();
		Solver& s = *ctx.master();
		s.assume(negLit(v[1])) && s.propagate();
		s.assume(posLit(v[4])) && s.propagate();
		s.assume(negLit(v[2])) && s.propagate();
		s.assume(posLit(v[5])) && s.propagate();
		CPPUNIT_ASSERT(ctx.numLearntShort() == 1);
		CPPUNIT_ASSERT(s.decisionLevel() == 3);
		s.undoUntil(2);
		CPPUNIT_ASSERT(std::find(prop.change.begin(), prop.change.end(), posLit(v[3])) != prop.change.end());
	}
	void testAddUnsatClause() {
		addVars(3);
		tp->addWatch(prop.fire = negLit(v[3]));
		prop.addToClause(posLit(v[1]));
		prop.addToClause(posLit(v[2]));
		tp->addPost(*ctx.master());
		ctx.endInit();
		Solver& s = *ctx.master();
		s.assume(negLit(v[2])) && s.propagate();
		s.assume(negLit(v[1])) && s.propagate();
		s.assume(negLit(v[3]));
		s.pushRootLevel(2);
		CPPUNIT_ASSERT_EQUAL(false, s.propagate());
		CPPUNIT_ASSERT_MESSAGE("do not add conflicting constraint", ctx.numLearntShort() == 0);
		s.popRootLevel(1);
		CPPUNIT_ASSERT(s.decisionLevel() == 1);
		prop.clause.clear();
		prop.addToClause(negLit(v[2]));
		prop.addToClause(posLit(v[3]));
		s.assume(negLit(v[3]));
		CPPUNIT_ASSERT_EQUAL(true, s.propagate());
		CPPUNIT_ASSERT_MESSAGE("do not add sat constraint", ctx.numLearntShort() == 0);
	}
	void testAddEmptyClause() {
		addVars(1);
		tp->addWatch(prop.fire = negLit(v[1]));
		prop.addToClause(negLit(0));
		tp->addPost(*ctx.master());
		ctx.endInit();
		Solver& s = *ctx.master();
		s.assume(negLit(v[1]));
		CPPUNIT_ASSERT_EQUAL(false, s.propagate());
	}
	void testAttachToSolver() {
		ClaspConfig config;
		ClaspFacade libclasp;
		config.addConfigurator(tp);
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp, "{x1;x2}.");
		asp.endProgram();
		for (Var v = 1; v <= libclasp.ctx.numVars(); ++v) {
			tp->addWatch(posLit(v));
			tp->addWatch(negLit(v));
		}
		CPPUNIT_ASSERT(prop.change.empty());
		libclasp.prepare();
		libclasp.solve();
		CPPUNIT_ASSERT(!prop.change.empty());
#if CLASP_HAS_THREADS
		config.solve.setSolvers(2);
		libclasp.update(true);
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.ctx.concurrency() == 2 && libclasp.ctx.hasSolver(1));
		libclasp.solve();
		CPPUNIT_ASSERT(libclasp.ctx.solver(1)->getPost(PostPropagator::priority_class_general) != 0);
		config.solve.setSolvers(1);
		libclasp.update(true);
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.ctx.concurrency() == 1);
		config.solve.setSolvers(2);
		libclasp.update(true);
		libclasp.solve();
		CPPUNIT_ASSERT(libclasp.ctx.solver(1)->getPost(PostPropagator::priority_class_general) != 0);
#endif
	}
	void testAddClauseOnModel() {
		addVars(3);
		prop.addToClause(posLit(v[1]));
		prop.addToClause(posLit(v[3]));
		tp->addPost(*ctx.master());
		ctx.endInit();
		Solver& s = *ctx.master();
		ValueRep v = s.search(-1, -1);
		CPPUNIT_ASSERT(v == value_true && s.numFreeVars() == 0);
		CPPUNIT_ASSERT(ctx.shortImplications().numLearnt() == 1);
	}
	void testAddConflictOnModel() {
		addVars(3);
		prop.addToClause(negLit(v[1]));
		prop.addToClause(negLit(v[2]));
		tp->addPost(*ctx.master());
		ctx.endInit();
		Solver& s = *ctx.master();
		s.assume(posLit(v[1]));
		s.force(posLit(v[2]), posLit(v[1]));
		s.propagate();
		s.assume(posLit(v[3])) && s.propagate();
		CPPUNIT_ASSERT(!s.hasConflict() && s.numFreeVars() == 0);
		CPPUNIT_ASSERT(!s.getPost(PostPropagator::priority_class_general)->isModel(s));
		CPPUNIT_ASSERT(s.hasConflict());
		CPPUNIT_ASSERT(s.decisionLevel() == 1 && s.resolveConflict());
	}

	void testAddStatic() {
		addVars(2);
		prop.addToClause(posLit(v[1]));
		prop.addToClause(posLit(v[2]));
		prop.fire   = lit_true();
		prop.clProp = Potassco::Clause_t::Static;
		tp->addWatch(negLit(v[1]));
		tp->addPost(*ctx.master());
		ctx.endInit();

		Solver& s = *ctx.master();
		CPPUNIT_ASSERT(s.numWatches(negLit(v[2])) == 0);
		s.assume(negLit(v[1])) && s.propagate();
		CPPUNIT_ASSERT(s.numWatches(negLit(v[2])) == 1);
		s.reduceLearnts(1.0);
		CPPUNIT_ASSERT(s.numWatches(negLit(v[2])) == 1);
	}

	void testAddVolatile() {
		ClaspConfig config;
		ClaspFacade libclasp;
		config.addConfigurator(tp);
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp, "{x1;x2}.");
		asp.endProgram();
		tp->addWatch(negLit(1));
		prop.addToClause(posLit(1));
		prop.addToClause(posLit(2));
		libclasp.prepare();
		prop.fire = libclasp.ctx.stepLiteral();
		prop.clProp = Potassco::Clause_t::Volatile;
		libclasp.solve();
		CPPUNIT_ASSERT(libclasp.ctx.numLearntShort() == 1);
		libclasp.update();
		CPPUNIT_ASSERT(libclasp.ctx.numLearntShort() == 0);
	}
	void testAddVolatileStatic() {
		ClaspConfig config;
		ClaspFacade libclasp;
		config.addConfigurator(tp);
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp, "{x1;x2}.");
		asp.endProgram();
		tp->addWatch(negLit(1));
		prop.addToClause(posLit(1));
		prop.addToClause(posLit(2));
		libclasp.prepare();
		prop.fire = libclasp.ctx.stepLiteral();
		prop.clProp = Potassco::Clause_t::VolatileStatic;
		libclasp.solve();
		CPPUNIT_ASSERT(libclasp.ctx.master()->numWatches(negLit(2)) == 1);
		libclasp.update();
		CPPUNIT_ASSERT(libclasp.ctx.master()->numWatches(negLit(2)) == 0);
	}
	void testPushVariable() {
		class AddVar : public Potassco::AbstractPropagator {
		public:
			typedef Potassco::Lit_t Lit_t;
			explicit AddVar(uint32 nAux) : aux_(nAux), next_(1) {}
			virtual void propagate(Potassco::AbstractSolver& s, const ChangeList&) {
				if (aux_) {
					const Potassco::AbstractAssignment& as = s.assignment();
					while (as.hasLit(next_)) { ++next_; }
					Lit_t x = s.addVariable();
					CPPUNIT_ASSERT(x == next_);
					CPPUNIT_ASSERT(!s.hasWatch(x) && !s.hasWatch(-x));
					s.addWatch(x);
					CPPUNIT_ASSERT(s.hasWatch(x) && !s.hasWatch(-x));
					s.addWatch(-x);
					CPPUNIT_ASSERT(s.hasWatch(x) && s.hasWatch(-x));
					s.removeWatch(x);
					CPPUNIT_ASSERT(!s.hasWatch(x) && s.hasWatch(-x));
					s.removeWatch(-x);
					CPPUNIT_ASSERT(!s.hasWatch(x) && !s.hasWatch(-x));
					s.addWatch(x); s.addWatch(-x);
					--aux_;
				}
			}
			virtual void undo(const Potassco::AbstractSolver&, const ChangeList&) {}
			virtual void check(Potassco::AbstractSolver&) {}
			uint32 aux_;
			Lit_t  next_;
		} prop(2);
		MyInit pp(prop);
		ClaspConfig config;
		ClaspFacade libclasp;
		config.addConfigurator(&pp);
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp, "{x1;x2}.");
		asp.endProgram();
		pp.addWatch(posLit(1));
		pp.addWatch(negLit(1));
		pp.addWatch(posLit(2));
		pp.addWatch(negLit(2));
		libclasp.prepare();
		uint32 nv = libclasp.ctx.numVars();
		uint32 sv = libclasp.ctx.master()->numVars();
		libclasp.solve();
		CPPUNIT_ASSERT(nv == libclasp.ctx.numVars());
		CPPUNIT_ASSERT(sv == libclasp.ctx.master()->numVars());
	}
	void testAuxVarMakesClauseVolatile() {
		class AddAuxClause : public Potassco::AbstractPropagator {
		public:
			typedef Potassco::Lit_t Lit_t;
			explicit AddAuxClause() { aux = 0;  nextStep = false; }
			virtual void propagate(Potassco::AbstractSolver& s, const ChangeList&) {
				if (!aux) {
					aux = s.addVariable();
					Potassco::LitVec clause;
					for (Lit_t i = 1; i < aux; ++i) {
						if (s.hasWatch(i)) {
							clause.push_back(-i);
						}
					}
					clause.push_back(-aux);
					s.addClause(Potassco::toSpan(clause), Potassco::Clause_t::Static);
				}
				CPPUNIT_ASSERT(!nextStep || !s.assignment().hasLit(aux));
			}
			virtual void undo(const Potassco::AbstractSolver&, const ChangeList&) {}
			virtual void check(Potassco::AbstractSolver&) {}
			Lit_t aux;
			bool  nextStep;
		} prop;
		MyInit pp(prop);
		ClaspConfig config;
		ClaspFacade libclasp;
		config.addConfigurator(&pp);
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp, "{x1;x2}.");
		asp.endProgram();
		pp.addWatch(posLit(1));
		pp.addWatch(posLit(2));
		LitVec assume;
		libclasp.prepare();
		assume.push_back(posLit(1));
		assume.push_back(posLit(2));
		libclasp.solve(assume);
		libclasp.update();
		prop.nextStep = true;
		libclasp.solve(assume);
	}

	void testRootLevelBug() {
		class Prop : public Potassco::AbstractPropagator {
		public:
			Prop() {}
			virtual void propagate(Potassco::AbstractSolver& s, const ChangeList&) {
				CPPUNIT_ASSERT(s.assignment().level() != 0);
				for (Potassco::Atom_t a = 2; a != 4; ++a) {
					Potassco::Lit_t pos = a;
					Potassco::Lit_t neg = -pos;
					if (!s.addClause(Potassco::toSpan(&pos, 1))) { return; }
					if (!s.addClause(Potassco::toSpan(&neg, 1))) { return; }
				}
			}
			virtual void undo(const Potassco::AbstractSolver&, const ChangeList&) {}
			virtual void check(Potassco::AbstractSolver&) {}
		} prop;
		MyInit pp(prop);
		ClaspConfig config;
		ClaspFacade libclasp;
		config.addConfigurator(&pp);
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp, "{x1;x2}.");
		asp.endProgram();
		pp.addWatch(posLit(1));
		pp.addWatch(negLit(1));
		pp.addWatch(posLit(2));
		pp.addWatch(negLit(2));
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.solve().unsat());
	}
	void testLookaheadBug() {
		ClaspConfig config;
		ClaspFacade libclasp;
		config.addConfigurator(tp);
		config.addSolver(0).lookType = Var_t::Atom;
		SatBuilder& sat = libclasp.startSat(config);
		sat.prepareProblem(2);
		LitVec clause;
		clause.push_back(negLit(1));
		clause.push_back(negLit(2));
		sat.addClause(clause);
		clause.pop_back();
		clause.push_back(posLit(2));
		sat.addClause(clause);
		tp->addWatch(negLit(1));
		libclasp.prepare();
		CPPUNIT_ASSERT(libclasp.ctx.master()->isTrue(negLit(1)));
		CPPUNIT_ASSERT(prop.change.size() == 1);
		CPPUNIT_ASSERT(prop.change[0] == negLit(1));
	}
private:
	void addVars(int num) {
		v.resize(num + 1);
		v[0] = 0;
		for (int i = 1; i <= num; ++i) {
			v[i] = ctx.addVar(Var_t::Atom);
		}
		ctx.startAddConstraints();
	}
	typedef ClingoPropagatorInit MyInit;
	SharedContext ctx;
	MyProp        prop;
	MyInit*       tp;
	VarVec v;
};
CPPUNIT_TEST_SUITE_REGISTRATION(ClingoPropagatorTest);
} }
