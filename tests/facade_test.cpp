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
#include <clasp/solver.h>
#include <clasp/clause.h>
#include <clasp/clasp_facade.h>
#include <clasp/minimize_constraint.h>
#include <clasp/heuristics.h>
#include <clasp/lookahead.h>
#include <clasp/clingo.h>
#include <clasp/model_enumerators.h>
#include <potassco/string_convert.h>
#if CLASP_HAS_THREADS
#include <clasp/mt/mutex.h>
#endif
#include "lpcompare.h"
#include <signal.h>
#include "catch.hpp"
namespace Clasp { namespace Test {
using namespace Clasp::mt;

TEST_CASE("Facade", "[facade]") {
	Clasp::ClaspFacade libclasp;
	Clasp::ClaspConfig config;
	SECTION("with trivial program") {
		config.solve.numModels = 0;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp, "a :- not b. b :- not a.");
		SECTION("testPrepareIsIdempotent") {
			libclasp.prepare();
			libclasp.prepare();
			REQUIRE(libclasp.solve().sat());
			REQUIRE(libclasp.summary().numEnum == 2);
			REQUIRE(libclasp.summary().step == 0);
		}
		SECTION("testPrepareIsImplicit") {
			REQUIRE(libclasp.solve().sat());
			REQUIRE(libclasp.summary().numEnum == 2);
			REQUIRE(libclasp.summary().step == 0);
		}
		SECTION("testPrepareSolvedProgram") {
			libclasp.prepare();
			REQUIRE(libclasp.solve().sat());
			REQUIRE(libclasp.summary().numEnum == 2);
			REQUIRE(libclasp.summary().step == 0);

			libclasp.prepare();
			REQUIRE(libclasp.solve().sat());
			REQUIRE(libclasp.summary().numEnum == 2);
			REQUIRE(libclasp.summary().step == 1);
		}
		SECTION("testSolveSolvedProgram") {
			libclasp.prepare();
			REQUIRE(libclasp.solve().sat());

			REQUIRE(libclasp.solve().sat());
			REQUIRE(libclasp.summary().numEnum == 2);
			REQUIRE(libclasp.summary().step == 1);
		}
		SECTION("testSolveAfterStopConflict") {
			struct PP : public PostPropagator {
				uint32 priority() const { return priority_reserved_msg; }
				bool propagateFixpoint(Solver& s, PostPropagator*) {
					s.setStopConflict();
					return false;
				}
			} pp;
			libclasp.ctx.master()->addPost(&pp);
			libclasp.prepare();
			REQUIRE(libclasp.solve().unknown());
			libclasp.ctx.master()->removePost(&pp);
			libclasp.update();
			REQUIRE(libclasp.solve().sat());
		}
		SECTION("testUpdateWithoutPrepareDoesNotIncStep") {
			REQUIRE(libclasp.update().ok());
			REQUIRE(libclasp.update().ok());
			libclasp.prepare();
			REQUIRE(libclasp.solve().sat());
			REQUIRE(libclasp.summary().numEnum == 2);
			REQUIRE(libclasp.summary().step == 0);
		}
		SECTION("testUpdateWithoutSolveDoesNotIncStep") {
			libclasp.prepare();
			REQUIRE(libclasp.update().ok());
			libclasp.prepare();

			REQUIRE(libclasp.solve().sat());
			REQUIRE(libclasp.summary().numEnum == 2);
			REQUIRE(libclasp.summary().step == 0);
		}
		SECTION("test interrupt") {
			struct FH : EventHandler {
				FH() : finished(0) {}
				virtual void onEvent(const Event& ev) {
					finished += event_cast<ClaspFacade::StepReady>(ev) != 0;
				}
				int finished;
			} fh;
			SECTION("interruptBeforePrepareInterruptsNext") {
				REQUIRE(libclasp.interrupt(1) == false);
				libclasp.prepare();
				REQUIRE(libclasp.solve(LitVec(), &fh).interrupted());
				REQUIRE(libclasp.solved());
				REQUIRE(fh.finished == 1);
			}
			SECTION("interruptBeforeSolveInterruptsNext") {
				libclasp.prepare();
				REQUIRE(libclasp.interrupt(1) == false);
				REQUIRE(!libclasp.solved());
				REQUIRE(libclasp.solve(LitVec(), &fh).interrupted());
				REQUIRE(libclasp.solved());
				REQUIRE(fh.finished == 1);
			}
			SECTION("interruptAfterSolveInterruptsNext") {
				libclasp.prepare();
				REQUIRE(!libclasp.solve(LitVec(), &fh).interrupted());
				REQUIRE(fh.finished == 1);
				REQUIRE(libclasp.solved());
				REQUIRE(!libclasp.interrupted());
				REQUIRE(libclasp.interrupt(1) == false);
				REQUIRE(libclasp.solve(LitVec(), &fh).interrupted());
				REQUIRE(fh.finished == 2);
			}
			SECTION("interruptBeforeUpdateInterruptsNext") {
				libclasp.prepare();
				libclasp.interrupt(1);
				libclasp.update(false);
				REQUIRE(!libclasp.interrupted());
				REQUIRE(libclasp.solve().interrupted());
			}
		}
		SECTION("testUpdateCanIgnoreQueuedSignals") {
			libclasp.prepare();
			libclasp.interrupt(1);
			libclasp.update(false, SIG_IGN);
			REQUIRE(!libclasp.solve().interrupted());
		}
		SECTION("testShutdownStopsStep") {
			libclasp.prepare();
			libclasp.shutdown();
			REQUIRE(libclasp.solved());
		}
		SECTION("testSolveUnderAssumptions") {
			Var ext = asp.newAtom();
			asp.freeze(ext, value_true);
			libclasp.prepare();
			LitVec assume(1, asp.getLiteral(1));
			struct MH : public Clasp::EventHandler {
				MH() : models(0) {}
				bool onModel(const Clasp::Solver&, const Clasp::Model& m) {
					for (LitVec::const_iterator it = exp.begin(), end = exp.end(); it != end; ++it) {
						REQUIRE(m.isTrue(*it));
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
			REQUIRE(mh1.models == 1);
			libclasp.update();
			asp.freeze(ext, value_false);
			assume.assign(1, asp.getLiteral(2));
			mh2.exp.push_back(~asp.getLiteral(1));
			mh2.exp.push_back(asp.getLiteral(2));
			mh2.exp.push_back(~asp.getLiteral(ext));
			libclasp.solve(assume, &mh2);
			REQUIRE(mh2.models == 1);
			libclasp.update();
			libclasp.solve();
			REQUIRE(libclasp.summary().numEnum == 2);
		}
	}
	SECTION("testRestartAfterPrepare") {
		libclasp.startAsp(config);
		libclasp.prepare();
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config);
		REQUIRE(!asp.frozen());
	}

	SECTION("testPrepareTooStrongBound") {
		config.solve.numModels = 0;
		config.solve.optBound.assign(1, 0);
		lpAdd(libclasp.startAsp(config, true),
			"a :-not b.\n"
			"b :-not a.\n"
			"c.\n"
			"#minimize{c, a, b}.");

		libclasp.prepare();
		REQUIRE(libclasp.solve().unsat());
	}
	SECTION("testComputeBrave") {
		config.solve.numModels = 0;
		config.solve.enumMode = EnumOptions::enum_brave;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		std::string prg(
			"x1 :- not x2.\n"
			"x2 :- not x1.\n"
			"x3 :- not x1.\n");
		SECTION("via output") {
			prg.append("#output a : x1.\n #output b : x2.\n");
		}
		SECTION("via project") {
			prg.append("#project{x1, x2, x3}.");
		}
		lpAdd(asp, prg.c_str());
		libclasp.prepare();
		REQUIRE(libclasp.solve().sat());
		const Model& m = *libclasp.summary().model();
		REQUIRE(m.isDef(asp.getLiteral(1)));
		REQUIRE(m.isDef(asp.getLiteral(2)));
	}
	SECTION("testComputeQuery") {
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
		REQUIRE(libclasp.solve().sat());
		const Model& m = *libclasp.summary().model();
		REQUIRE(m.isDef(asp.getLiteral(3)));
		REQUIRE(!m.isDef(asp.getLiteral(1)));
		REQUIRE(!m.isDef(asp.getLiteral(2)));
	}
	SECTION("test opt enumerate") {
		config.solve.numModels = 0;
		config.solve.optMode = MinimizeMode_t::enumOpt;
		lpAdd(libclasp.startAsp(config, false),
			"{x1;x2;x3}.\n"
			":- not x1, not x2, not x3.\n"
			":- x2, not x1.\n"
			":- x3, not x1.\n"
			"#minimize{not x1}@0.\n"
			"#minimize{x1}@1.");
		libclasp.prepare();
		SECTION("with basic solve") {
			REQUIRE(libclasp.solve().sat());
			REQUIRE(uint64(4) == libclasp.summary().optimal());
		}
		SECTION("with generator") {
			unsigned num = 0, opt = 0;
			for (Clasp::ClaspFacade::SolveHandle it = libclasp.solve(SolveMode_t::Yield); it.next();) {
				++num;
				opt += it.model()->opt;
			}
			REQUIRE((num > opt && opt == 4));
		}
	}

	SECTION("testIncrementalEnum") {
		config.solve.numModels = 0;
		config.solve.enumMode  = EnumOptions::enum_record;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp, "{x1}.");
		libclasp.prepare();
		REQUIRE(libclasp.solve().sat());
		REQUIRE(libclasp.summary().numEnum == 2);
		REQUIRE(libclasp.update().ok());
		lpAdd(asp, "{x2}.");
		libclasp.prepare();
		REQUIRE(libclasp.solve().sat());
		REQUIRE(libclasp.summary().numEnum == 4);
	}
	SECTION("testIncrementalCons") {
		config.solve.numModels = 0;
		config.solve.enumMode  = EnumOptions::enum_cautious;
		lpAdd(libclasp.startAsp(config, true),
			"{x1;x2;x3}.\n"
			"#output a : x1.\n"
			"#output b : x2.\n"
			"#output c : x3.\n");
		libclasp.prepare();
		REQUIRE(libclasp.solve().sat());
		config.solve.enumMode = EnumOptions::enum_brave;
		libclasp.update(true);
		libclasp.prepare();
		REQUIRE(libclasp.solve().sat());
		REQUIRE(libclasp.summary().numEnum > 1);
	}
	SECTION("testIncrementalMin") {
		config.solve.numModels = 0;
		config.solve.enumMode  = EnumOptions::enum_auto;
		lpAdd(libclasp.startAsp(config, true),
			"{x1;x2;x3}.\n"
			"#minimize{x1, x2, x3}.\n");
		libclasp.prepare();
		REQUIRE(libclasp.solve().sat());
		REQUIRE(libclasp.summary().numEnum < 8u);
		libclasp.update().ctx()->removeMinimize();
		libclasp.prepare();
		REQUIRE(libclasp.solve().sat());
		REQUIRE(libclasp.summary().numEnum == 8);
	}
	SECTION("testIncrementalMinIgnore") {
		config.solve.optMode = MinimizeMode_t::ignore;
		config.solve.numModels = 0;
		lpAdd(libclasp.startAsp(config, true),
			"{x1;x2}.\n"
			"#minimize{x1, x2}.\n");
		libclasp.prepare();
		REQUIRE(libclasp.solve().sat());
		REQUIRE(libclasp.summary().numEnum == 4u);
		config.solve.optMode = MinimizeMode_t::optimize;
		libclasp.update(true);
		libclasp.prepare();
		REQUIRE(libclasp.solve().sat());
		REQUIRE(libclasp.summary().numEnum == 1u);
	}
	SECTION("testIncrementalMinAdd") {
		config.solve.numModels = 0;
		config.solve.enumMode  = EnumOptions::enum_auto;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp,
			"{x1;x2}.\n"
			"#minimize{not x1}.\n");
		libclasp.prepare();
		REQUIRE(libclasp.solve().sat());
		REQUIRE(libclasp.summary().model()->isTrue(asp.getLiteral(1)));
		libclasp.update();
		lpAdd(asp, "#minimize{not x2}.");
		libclasp.prepare();
		REQUIRE(libclasp.solve().sat());
		REQUIRE(libclasp.summary().model()->isTrue(asp.getLiteral(1)));
		REQUIRE(libclasp.summary().model()->isTrue(asp.getLiteral(2)));
	}
	SECTION("testUncoreUndoerAssumptions") {
		config.solve.numModels = 0;
		config.solve.optMode   = MinimizeMode_t::enumOpt;
		config.addSolver(0).heuId = Heuristic_t::Domain;
		SECTION("test oll") {
			config.addSolver(0).opt.type = OptParams::type_usc;
			config.addSolver(0).opt.algo = OptParams::usc_oll;
		}
		SECTION("test one") {
			config.addSolver(0).opt.type = OptParams::type_usc;
			config.addSolver(0).opt.algo = OptParams::usc_one;
		}
		SECTION("test k") {
			config.addSolver(0).opt.type = OptParams::type_usc;
			config.addSolver(0).opt.algo = OptParams::usc_k;
		}
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp,
			"{x1;x2;x3;x4;x5}.\n"
			":- x1, x2, x3.\n"
			":- x4, x5.\n"
			":- x4, not x5.\n"
			"x5 :- not x4.\n"
			"#minimize{not x1, not x2}.\n"
			"#heuristic x4. [1,true]"
			"#assume{x3}.\n");
		libclasp.prepare();
		REQUIRE(libclasp.solve().sat());
		REQUIRE(libclasp.summary().numOptimal == 2);
		libclasp.update();
		libclasp.ctx.addUnary(~asp.getLiteral(3));
		libclasp.ctx.addUnary(asp.getLiteral(5));
		libclasp.prepare();
		REQUIRE(libclasp.solve().sat());
		REQUIRE(libclasp.summary().costs()->at(0) == 0);
		REQUIRE(libclasp.summary().numOptimal == 1);
	}

	SECTION("testUpdateConfig") {
		config.solve.numModels = 0;
		config.solve.enumMode  = EnumOptions::enum_auto;
		config.addSolver(0).heuId  = Heuristic_t::Berkmin;
		lpAdd(libclasp.startAsp(config, true), "{x1;x2;x3}.");
		libclasp.prepare();
		REQUIRE(libclasp.solve().sat());
		config.addSolver(0).heuId = Heuristic_t::Vsids;
		libclasp.update(true);
		libclasp.prepare();
		REQUIRE(libclasp.solve().sat());
		REQUIRE(dynamic_cast<ClaspVsids*>(libclasp.ctx.master()->heuristic()));
	}
	SECTION("testIncrementalProjectUpdate") {
		config.solve.numModels = 0;
		config.solve.enumMode  = EnumOptions::enum_auto;
		config.solve.project   = 1;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp, "{x1;x2}. #output b : x2.");
		libclasp.prepare();
		REQUIRE(static_cast<const ModelEnumerator*>(libclasp.enumerator())->project(asp.getLiteral(2).var()));
		REQUIRE(libclasp.solve().sat());
		REQUIRE(libclasp.summary().numEnum == 2);
		config.solve.project = 0;
		libclasp.update(true);
		libclasp.prepare();
		REQUIRE(libclasp.solve().sat());
		REQUIRE(libclasp.summary().numEnum == 4);
		config.solve.project = 1;
		libclasp.update(true);
		lpAdd(asp, "{x3;x4}. #output y : x4.");
		libclasp.prepare();
		REQUIRE(static_cast<const ModelEnumerator*>(libclasp.enumerator())->project(asp.getLiteral(2).var()));
		REQUIRE(static_cast<const ModelEnumerator*>(libclasp.enumerator())->project(asp.getLiteral(4).var()));
		REQUIRE(libclasp.solve().sat());
		REQUIRE(uint64(4) == libclasp.summary().numEnum);
	}
	SECTION("testIncrementalDomRecUpdate") {
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
		REQUIRE(libclasp.solve().sat());
		// {a} ; {b}
		REQUIRE(libclasp.summary().numEnum == 2);

		config.addSolver(0).heuristic.domMod = HeuParams::mod_true;
		libclasp.update(true);
		REQUIRE(libclasp.solve().sat());
		// {a,b}
		REQUIRE(libclasp.summary().numEnum == 1);
	}
	SECTION("testIncrementalConfigUpdateBug") {
		config.asp.erMode = Asp::LogicProgram::mode_transform;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp, "{x1;x2}.");
		libclasp.prepare();
		REQUIRE(libclasp.ctx.ok());
		REQUIRE(asp.stats.auxAtoms == 2);
		config.asp.erMode = Asp::LogicProgram::mode_native;
		libclasp.update(true);
		lpAdd(asp, "{x3;x4}.");
		libclasp.prepare();
		REQUIRE(asp.stats.auxAtoms == 0);
	}
	SECTION("with lookahead") {
		config.addSolver(0).lookType = Var_t::Atom;
		lpAdd(libclasp.startAsp(config, true), "{x1;x2}.");
		libclasp.prepare();
		REQUIRE(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look));
		SECTION("incrementalLookaheadAddHeuristic") {
			PostPropagator* look = libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look);
			config.addSolver(0).heuId = Heuristic_t::Unit;
			libclasp.update(true);
			libclasp.prepare();
			look = libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look);
			REQUIRE((look && look->next == 0));
		}
		SECTION("incrementalDisableLookahead") {
			config.addSolver(0).lookType = 0;
			libclasp.update(true);
			libclasp.prepare();
			REQUIRE(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look) == 0);
		}
		SECTION("incrementalChangeLookahead") {
			config.addSolver(0).lookType = Var_t::Body;
			libclasp.update(true);
			libclasp.prepare();
			Lookahead* look = static_cast<Lookahead*>(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look));
			REQUIRE((look && look->score.types == Var_t::Body));
		}
	}
	SECTION("testIncrementalExtendLookahead") {
		config.addSolver(0).lookType = Var_t::Atom;
		config.addSolver(0).lookOps  = 3;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp, "{x1;x2}.");
		libclasp.prepare();
		REQUIRE(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look));
		config.addSolver(0).lookOps  = 0;
		libclasp.update(true);
		lpAdd(asp, "{x3;x4}.");
		libclasp.prepare();
		Lookahead* look = static_cast<Lookahead*>(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look));
		REQUIRE((look && look->next == 0));
		while (libclasp.ctx.master()->numFreeVars() != 0) {
			libclasp.ctx.master()->decideNextBranch();
			libclasp.ctx.master()->propagate();
			REQUIRE(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look) == look);
		}
	}

	SECTION("testIncrementalRemoveSolver") {
		config.solve.numModels = 0;
		config.solve.setSolvers(4);
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp,
			"{x1;x2;x4;x3}.\n"
			":- 3 {x1, x2, x3, x4}.\n");
		libclasp.prepare();
		REQUIRE(libclasp.solve().sat());
		REQUIRE(uint64(11) == libclasp.summary().numEnum);

		config.solve.setSolvers(1);
		libclasp.update(true);
		lpAdd(asp, ":- x1, x2.\n");
		libclasp.prepare();
		REQUIRE((libclasp.solve().sat() && libclasp.summary().numEnum == 10));

		config.solve.setSolvers(2);
		libclasp.update(true);
		libclasp.prepare();
		REQUIRE((libclasp.solve().sat() && libclasp.summary().numEnum == 10));
	}

	SECTION("testGenSolveTrivialUnsat") {
		config.solve.numModels = 0;
		lpAdd(libclasp.startAsp(config, true), "x1 :- not x1.");
		libclasp.prepare();
		ClaspFacade::SolveHandle it = libclasp.solve(SolveMode_t::Yield);
		REQUIRE(it.get().exhausted());
		REQUIRE(!it.model());
	}
	SECTION("testInterruptBeforeGenSolve") {
		config.solve.numModels = 0;
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		libclasp.prepare();
		libclasp.interrupt(2);
		ClaspFacade::SolveHandle it = libclasp.solve(SolveMode_t::Yield);
		REQUIRE(it.get().interrupted());
		REQUIRE(!it.model());
	}
	SECTION("testGenSolveWithLimit") {
		lpAdd(libclasp.startAsp(config, true), "{x1;x2;x3}.");
		libclasp.prepare();
		for (int i = 1; i != 9; ++i) {
			unsigned got = 0, exp = i;
			config.solve.numModels = i % 8;
			libclasp.update(true);
			for (ClaspFacade::SolveHandle it = libclasp.solve(SolveMode_t::Yield); it.next(); ) {
				REQUIRE(got != exp);
				++got;
			}
			REQUIRE(exp == got);
		}
	}

	SECTION("testCancelGenSolve") {
		config.solve.numModels = 0;
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		libclasp.prepare();
		unsigned mod = 0;
		ClaspFacade::SolveHandle it = libclasp.solve(SolveMode_t::Yield);
		for (; it.next();) {
			REQUIRE(it.model()->num == ++mod);
			it.cancel();
			break;
		}
		REQUIRE((!libclasp.solving() && !it.get().exhausted() && mod == 1));
		libclasp.update();
		libclasp.prepare();
		mod = 0;
		for (ClaspFacade::SolveHandle j = libclasp.solve(SolveMode_t::Yield); j.next(); ++mod) {
			;
		}
		REQUIRE((!libclasp.solving() && mod == 2));
	}
	SECTION("testGenDtorCancelsSolve") {
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		libclasp.prepare();
		{ libclasp.solve(SolveMode_t::Yield); }
		REQUIRE((!libclasp.solving() && !libclasp.result().exhausted()));
	}

	SECTION("with model handler") {
		struct Handler : EventHandler {
			Handler() : doThrow(false), doStop(false) {}
			bool doThrow, doStop;
			virtual bool onModel(const Solver&, const Model&) {
				if (doThrow) { throw std::runtime_error("Model"); }
				return doStop == false;
			}
		} h;
		config.solve.numModels = 0;
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		libclasp.prepare();
		SECTION("genStopFromHandler") {
			h.doStop = true;
			libclasp.ctx.setEventHandler(&h);
			int mod = 0;
			for (ClaspFacade::SolveHandle g = libclasp.solve(SolveMode_t::Yield); g.next(); ++mod) {
				;
			}
			REQUIRE(mod == 1);
		}
		SECTION("syncThrowOnModel") {
			h.doThrow = true;
			ClaspFacade::SolveHandle g = libclasp.solve(SolveMode_t::Yield, LitVec(), &h);
			REQUIRE_THROWS_AS(g.model(), std::runtime_error);
			REQUIRE(!g.running());
			REQUIRE(!libclasp.solving());
			REQUIRE_THROWS_AS(g.get(), std::runtime_error);
		}
	}
	SECTION("testUserConfigurator") {
		struct MyAddPost : public ClaspConfig::Configurator {
			MyAddPost() : called(false) {}
			virtual bool addPost(Solver&) { return called = true; }
			bool called;
		} myAddPost;
		config.addConfigurator(&myAddPost);
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		libclasp.prepare();
		REQUIRE(myAddPost.called);
	}
	SECTION("testUserHeuristic") {
		struct MyHeu {
			static DecisionHeuristic* creator(Heuristic_t::Type, const HeuParams&) { throw MyHeu(); }
		};
		config.setHeuristicCreator(&MyHeu::creator);
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		REQUIRE_THROWS_AS(libclasp.prepare(), MyHeu);
	}
};

TEST_CASE("Incremental solving", "[facade]") {
	Clasp::ClaspFacade libclasp;
	Clasp::ClaspConfig config;
	typedef ClaspFacade::Result Result;
	Result::Base stop, done;
	int maxS = -1, minS = -1, expS = 0;
	libclasp.ctx.enableStats(2);
	config.asp.noEq();
	Asp::LogicProgram& asp = libclasp.startAsp(config, true);
	const char* prg[] = {
		// step 0
		"x1 :- x2.\n"
		"x2 :- x1.\n"
		"x1 :- x3.\n"
		":- not x1.\n"
		"#external x3."
		, // step 1
		"x3 :- x4.\n"
		"x4 :- x3.\n"
		"x4 :- x5.\n"
		"#external x5."
		, // step 2
		"x5 :- x6, x7.\n"
		"x6 :- not x3.\n"
		"x7 :- not x1, not x2.\n"
		"{x5}."
		, // step 3
		"{x8}."
	};
	SECTION("test stop on sat - no limit") {
		stop = done = Result::SAT;
		expS = 2;
	}
	SECTION("test stop on unsat - no limit") {
		stop = done = Result::UNSAT;
	}
	SECTION("test stop on sat - with max step") {
		stop = Result::SAT;
		done = Result::UNSAT;
		maxS = 2;
		expS = 1;
	}
	SECTION("test stop on sat - with min step") {
		stop = Result::SAT;
		done = Result::SAT;
		minS = 4;
		expS = 3;
	}
	Result::Base res = Result::UNKNOWN;
	do {
		libclasp.update();
		REQUIRE(std::size_t(libclasp.step()) < (sizeof(prg)/sizeof(const char*)));
		lpAdd(asp, prg[libclasp.step()]);
		libclasp.prepare();
		res = libclasp.solve();
	} while (--maxS && ((minS > 0 && --minS) || res != stop));
	REQUIRE(done == (Result::Base)libclasp.result());
	REQUIRE(expS == libclasp.step());
}

#if CLASP_HAS_THREADS

TEST_CASE("Facade mt", "[facade][mt]") {
	Clasp::ClaspFacade libclasp;
	Clasp::ClaspConfig config;
	typedef ClaspFacade::SolveHandle AsyncResult;
	SECTION("testIncrementalAddSolver") {
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp, "{x1;x2}.");
		libclasp.prepare();
		REQUIRE(!isSentinel(libclasp.ctx.stepLiteral()));
		config.solve.setSolvers(2);
		libclasp.update(true);
		lpAdd(asp, "{x3;x4}.");
		libclasp.prepare();
		REQUIRE((libclasp.ctx.concurrency() == 2 && libclasp.ctx.hasSolver(1)));
	}
	SECTION("testClingoSolverStatsRemainValid") {
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
		REQUIRE(stats->size(s) == 2);
		REQUIRE(stats->value(s1c) + stats->value(s0c) == stats->value(stats->get(stats->root(), "solving.solvers.choices")));
		config.solve.algorithm.threads = 1;
		libclasp.update(true);
		libclasp.solve();
		INFO("solver stats are not removed");
		REQUIRE(stats->size(s) == 2);
		INFO("solver stats remain valid");
		REQUIRE(stats->at(s, 1) == s1);
		REQUIRE(stats->value(s1c) == 0.0);
		REQUIRE(stats->value(s0c) == stats->value(stats->get(stats->root(), "solving.solvers.choices")));
		config.solve.algorithm.threads = 2;
		libclasp.update(true);
		libclasp.solve();
		REQUIRE(stats->value(s1c) + stats->value(s0c) == stats->value(stats->get(stats->root(), "solving.solvers.choices")));
	}
	SECTION("testShareModeRegression") {
		config.shareMode = ContextParams::share_auto;
		config.solve.algorithm.threads = 2;
		libclasp.startSat(config).prepareProblem(2);
		libclasp.prepare();
		REQUIRE(libclasp.ctx.physicalShare(Constraint_t::Static));
		REQUIRE(libclasp.ctx.physicalShare(Constraint_t::Conflict));
	}
	SECTION("testAsyncSolveTrivialUnsat") {
		config.solve.numModels = 0;
		lpAdd(libclasp.startAsp(config, true), "x1 :- not x1.");
		libclasp.prepare();
		AsyncResult it = libclasp.solve(SolveMode_t::Async|SolveMode_t::Yield);
		REQUIRE(it.get().unsat());
	}
	SECTION("testInterruptBeforeSolve") {
		config.solve.numModels = 0;
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		libclasp.prepare();
		libclasp.interrupt(2);
		AsyncResult it = libclasp.solve(SolveMode_t::AsyncYield);
		REQUIRE(it.get().interrupted());
	}
	SECTION("testCancelAsyncOperation") {
		config.solve.numModels = 0;
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		libclasp.prepare();
		AsyncResult it = libclasp.solve(SolveMode_t::AsyncYield);
		while (it.model()) {
			it.cancel();
		}
		REQUIRE(uint64(1) == libclasp.summary().numEnum);
		REQUIRE((!libclasp.solving() && it.interrupted()));
		libclasp.update();
		libclasp.prepare();
		it = libclasp.solve(SolveMode_t::AsyncYield);
		int mod = 0;
		while (it.model()) { ++mod; it.resume(); }
		REQUIRE((!libclasp.solving() && mod == 2));
	}
	SECTION("testAsyncResultDtorCancelsOp") {
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		libclasp.prepare();
		{ AsyncResult it = libclasp.solve(SolveMode_t::AsyncYield); }
		REQUIRE((!libclasp.solving() && libclasp.result().interrupted()));
	}

	SECTION("testDestroyAsyncResultNoFacade") {
		{
			ClaspFacade* localLib = new ClaspFacade();
			lpAdd(localLib->startAsp(config, true), "{x1}.");
			localLib->prepare();
			AsyncResult res(localLib->solve(SolveMode_t::AsyncYield));
			delete localLib;
			REQUIRE(res.interrupted());
		}
	}
	SECTION("testDestroyDanglingAsyncResult") {
		AsyncResult* handle = 0;
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		libclasp.prepare();
		handle = new AsyncResult(libclasp.solve(SolveMode_t::Async));
		handle->wait();
		libclasp.update();
		libclasp.prepare();
		AsyncResult* it = new AsyncResult(libclasp.solve(SolveMode_t::AsyncYield));
		delete handle;
		REQUIRE((!it->interrupted() && libclasp.solving()));
		REQUIRE_NOTHROW(delete it);
		REQUIRE(!libclasp.solving());
	}
	SECTION("testCancelDanglingAsyncOperation") {
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		libclasp.prepare();
		AsyncResult step0 = libclasp.solve(SolveMode_t::Async);
		step0.wait();
		libclasp.update();
		libclasp.prepare();
		AsyncResult step1 = libclasp.solve(SolveMode_t::AsyncYield);

		step0.cancel();
		REQUIRE(libclasp.solving());
		step1.cancel();
		REQUIRE(!libclasp.solving());
	}
	SECTION("testGenSolveMt") {
		config.solve.numModels = 0;
		config.solve.algorithm.threads = 2;
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		libclasp.prepare();
		int mod = 0;
		for (ClaspFacade::SolveHandle it = libclasp.solve(SolveMode_t::Yield); it.next(); ++mod) {
			;
		}
		REQUIRE((!libclasp.solving() && mod == 2));
	}
	SECTION("test async throw") {
		struct Handler : EventHandler {
			Handler() : throwModel(false), throwFinish(false) {}
			bool throwModel, throwFinish;
			virtual bool onModel(const Solver&, const Model&) {
				if (throwModel) { throw std::runtime_error("Model"); }
				return true;
			}
			virtual void onEvent(const Event& ev) {
				if (event_cast<ClaspFacade::StepReady>(ev) && throwFinish) {
					throw std::runtime_error("Finish");
				}
			}
		} h;
		lpAdd(libclasp.startAsp(config, true), "{x1}.");
		libclasp.prepare();
		SECTION("on model") {
			h.throwModel = true;
			AsyncResult step0 = libclasp.solve(SolveMode_t::Async, LitVec(), &h);
			step0.wait();
			REQUIRE(step0.error());
			REQUIRE_THROWS_AS(step0.get(), std::runtime_error);
		}
		SECTION("on finish") {
			h.throwFinish = true;
			AsyncResult step0 = libclasp.solve(SolveMode_t::Async, LitVec(), &h);
			step0.wait();
			REQUIRE(step0.error());
			REQUIRE_THROWS_AS(step0.get(), std::runtime_error);
		}
	}
	SECTION("test mt exception handling") {
		struct EventVar {
			EventVar() : fired(false) {}
			void fire() {
				{
					Clasp::mt::unique_lock<Clasp::mt::mutex> lock(mutex);
					fired = true;
				}
				cond.notify_one();
			}
			void wait() {
				for (Clasp::mt::unique_lock<Clasp::mt::mutex> lock(mutex); !fired;) {
					cond.wait(lock);
				}
			}
			Clasp::mt::mutex mutex;
			Clasp::mt::condition_variable cond;
			bool fired;
		} ev;
		config.solve.numModels = 0;
		config.solve.setSolvers(2);
		lpAdd(libclasp.startAsp(config, true), "{x1;x2}.");
		libclasp.prepare();
		SECTION("throwOnModel") {
			struct Blocker : public PostPropagator {
				explicit Blocker(EventVar& e) : ev(&e) {}
				uint32 priority() const { return PostPropagator::priority_reserved_ufs + 10; }
				bool   propagateFixpoint(Solver& s, Clasp::PostPropagator* ctx) {
					if (!ctx && s.numFreeVars() == 0) {
						ev->wait();
					}
					return true;
				}
				EventVar* ev;
			};
			libclasp.ctx.master()->addPost(new Blocker(ev));
			struct Handler : EventHandler {
				virtual bool onModel(const Solver& s, const Model&) {
					if (&s != s.sharedContext()->master()) {
						ev->fire();
						throw std::runtime_error("Model from thread");
					}
					return false;
				}
				EventVar* ev;
			} h; h.ev = &ev;
			REQUIRE_THROWS_AS(libclasp.solve(SolveMode_t::Default, LitVec(), &h), std::runtime_error);
		}
		SECTION("throw on propagate") {
			struct Blocker : public PostPropagator {
				enum ET { none, alloc, logic };
				explicit Blocker(EventVar& e, ET t) : ev(&e), et(t) {}
				uint32 priority() const { return PostPropagator::priority_reserved_ufs + 10; }
				bool   propagateFixpoint(Solver& s, Clasp::PostPropagator*) {
					if (et == none) {
						ev->wait();
						s.removePost(this);
						delete this;
					}
					else {
						ev->fire();
						if (et == alloc) { throw std::bad_alloc(); }
						else             { throw std::logic_error("Something happend"); }
					}
					return true;
				}
				EventVar* ev;
				ET        et;
			};
			libclasp.ctx.master()->addPost(new Blocker(ev, Blocker::none));
			SECTION("allocFailContinue") {
				libclasp.ctx.solver(1)->addPost(new Blocker(ev, Blocker::alloc));
				REQUIRE_NOTHROW(libclasp.solve());
				REQUIRE(libclasp.summary().numEnum == 4);
			}
			SECTION("logicFailStop") {
				libclasp.ctx.solver(1)->addPost(new Blocker(ev, Blocker::logic));
				REQUIRE_THROWS_AS(libclasp.solve(), std::logic_error);
			}
		}
	}
}

#endif

static void getStatsKeys(const Potassco::AbstractStatistics& stats, Potassco::AbstractStatistics::Key_t k, std::vector<std::string>& out, const std::string& p) {
	if (stats.type(k) == Potassco::Statistics_t::Map) {
		for (uint32 i = 0, end = stats.size(k); i != end; ++i) {
			const char* sk = stats.key(k, i);
			getStatsKeys(stats, stats.get(k, sk), out, p.empty() ? sk : std::string(p).append(".").append(sk));
		}
	}
	else if (stats.type(k) == Potassco::Statistics_t::Array) {
		for (uint32 i = 0, end = stats.size(k); i != end; ++i) {
			getStatsKeys(stats, stats.at(k, i), out, std::string(p).append(".").append(Potassco::StringBuilder().appendFormat("%d", i).c_str()));
		}
	}
	else {
		out.push_back(p);
	}
}

static void addExternalStats(Potassco::AbstractStatistics* us, void*) {
	typedef Potassco::AbstractStatistics::Key_t Key_t;

	Key_t rootkey = us->root();
	Key_t general = us->add(rootkey, "deathCounter", Potassco::Statistics_t::Map);
	REQUIRE(us->get(rootkey, "deathCounter") == general);
	REQUIRE(us->type(general) == Potassco::Statistics_t::Map);
	Key_t value   = us->add(general, "total", Potassco::Statistics_t::Value);
	us->set(value, 42.0);
	value = us->add(general, "chickens", Potassco::Statistics_t::Value);
	us->set(value, 712.0);

	Key_t array = us->add(general, "thread", Potassco::Statistics_t::Array);
	REQUIRE(us->get(general, "thread") == array);
	REQUIRE(us->type(array) == Potassco::Statistics_t::Array);
	REQUIRE(us->size(array) == 0);
	for (size_t t = 0; t != 4; ++t) {
		Key_t a = us->push(array, Potassco::Statistics_t::Map);
		value   = us->add(a, "total", Potassco::Statistics_t::Value);
		us->set(value, 20*(t+1));
		Key_t m = us->add(a, "Animals", Potassco::Statistics_t::Map);
		value   = us->add(m, "chicken", Potassco::Statistics_t::Value);
		us->set(value, 2*(t+1));
		value   = us->add(m, "cows", Potassco::Statistics_t::Value);
		us->set(value, 5*(t+1));
		value   = us->add(a, "feeding cost", Potassco::Statistics_t::Value);
		us->set(value, t+1);
	}
	REQUIRE(us->add(rootkey, "deathCounter", Potassco::Statistics_t::Map) == general);
}

TEST_CASE("Facade statistics", "[facade]") {
	Clasp::ClaspFacade libclasp;
	Clasp::ClaspConfig config;
	config.stats = 2;
	SECTION("testClingoStats") {
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp, "{x1;x2;x3}. #minimize{x1, x2}.");
		libclasp.prepare();
		libclasp.solve();
		Potassco::AbstractStatistics* stats = libclasp.getStats();
		typedef Potassco::AbstractStatistics::Key_t Key_t;
		Key_t r = stats->root();
		REQUIRE(stats->type(r) == Potassco::Statistics_t::Map);
		REQUIRE(stats->writable(r) == true);
		Key_t lp = stats->get(r, "problem.lp");
		REQUIRE(stats->writable(lp) == false);

		Key_t s = stats->get(r, "solving");
		Key_t m = stats->get(r, "summary.models");
		REQUIRE(stats->type(lp) == Potassco::Statistics_t::Map);
		REQUIRE(stats->value(stats->get(lp, "rules")) == double(asp.stats.rules[0].sum()));
		REQUIRE(stats->value(stats->get(m, "enumerated")) == double(libclasp.summary().numEnum));
		Key_t solvers = stats->get(s, "solvers");
		REQUIRE(stats->value(stats->get(solvers, "choices")) == double(libclasp.ctx.master()->stats.choices));
		Key_t costs = stats->get(r, "summary.costs");
		REQUIRE(stats->type(costs) == Potassco::Statistics_t::Array);
		REQUIRE(stats->value(stats->at(costs, 0)) == double(libclasp.summary().costs()->at(0)));
		Key_t solver = stats->get(s, "solver");
		REQUIRE(stats->type(solver) == Potassco::Statistics_t::Array);
		Key_t s0 = stats->at(solver, 0);
		REQUIRE(stats->type(s0) == Potassco::Statistics_t::Map);
		REQUIRE(stats->value(stats->get(s0, "choices")) == double(libclasp.ctx.master()->stats.choices));
		std::vector<std::string> keys;
		getStatsKeys(*stats, r, keys, "");
		REQUIRE(!keys.empty());
		for (std::vector<std::string>::const_iterator it = keys.begin(), end = keys.end(); it != end; ++it) {
			Key_t result;
			REQUIRE(stats->find(r, it->c_str(), &result));
			REQUIRE(result == stats->get(r, it->c_str()));
			REQUIRE(stats->type(result) == Potassco::Statistics_t::Value);
		}
		REQUIRE(keys.size() == 237);

		Key_t result;
		REQUIRE(stats->find(r, "problem.lp", &result));
		REQUIRE(result == lp);
		REQUIRE(!stats->find(lp, "foo", 0));
		REQUIRE(stats->find(lp, "rules", &result));
	}
	SECTION("testClingoStatsKeyIntegrity") {
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
		REQUIRE_THROWS_AS(stats->get(stats->root(), "hcc"), std::logic_error);
		REQUIRE(stats->value(m0) == (double)libclasp.summary().costs()->at(0));
		libclasp.update();
		lpAdd(asp,
			"x4 | x5 :- x6, not x1."
			"x6 :- x4, x5, not x2."
			"x6 :- not x1."
			);
		libclasp.prepare();
		libclasp.solve();
		REQUIRE(asp.stats.sccs == 1);
		REQUIRE(asp.stats.nonHcfs == 1);
		REQUIRE(lp == stats->get(stats->root(), "problem.lp"));
		REQUIRE(sccs == stats->get(lp, "sccs"));
		REQUIRE(m0 == stats->get(stats->root(), "summary.costs.0"));
		REQUIRE(stats->value(sccs) == asp.stats.sccs);
		REQUIRE(stats->value(m0) == (double)libclasp.summary().costs()->at(0));
		Key_t hcc0 = stats->get(stats->root(), "problem.hcc.0");
		Key_t hcc0Vars = stats->get(hcc0, "vars");
		REQUIRE(stats->value(hcc0Vars) != 0.0);
		libclasp.update();
		libclasp.ctx.removeMinimize();
		lpAdd(asp,
			"x7 | x8 :- x9, not x1."
			"x9 :- x7, x8, not x2."
			"x9 :- not x1."
			);
		libclasp.prepare();
		libclasp.solve();
		REQUIRE(libclasp.summary().lpStats()->sccs == 2);
		REQUIRE(libclasp.summary().lpStats()->nonHcfs == 2);
		REQUIRE(lp == stats->get(stats->root(), "problem.lp"));
		REQUIRE(sccs == stats->get(lp, "sccs"));
		REQUIRE_THROWS_AS(stats->value(m0), std::logic_error);
		REQUIRE(stats->value(hcc0Vars) != 0.0);
		REQUIRE(stats->value(stats->get(stats->root(), "problem.hcc.1.vars")) != 0.0);
	}
	SECTION("testClingoStatsWithoutStats") {
		config.stats = 0;
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
		REQUIRE(stats->size(root) == 3);
		REQUIRE(stats->get(root, "solving") != root);
		REQUIRE(stats->get(root, "problem") != root);
		REQUIRE(stats->get(root, "summary") != root);
		REQUIRE_THROWS_AS(stats->get(root, "solving.accu"), std::out_of_range);
		Key_t solving = stats->get(root, "solving");
		REQUIRE(stats->find(solving, "accu", 0) == false);
	}
	SECTION("testClingoStatsBug") {
		config.stats = 0;
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp, "{x2,x3}. #minimize{not x1,x2}.");
		libclasp.solve();
		Potassco::AbstractStatistics* stats = libclasp.getStats();
		typedef Potassco::AbstractStatistics::Key_t Key_t;
		Key_t root = stats->root();
		Key_t costs, minVal;
		REQUIRE(stats->size(root) == 3);
		REQUIRE((costs = stats->get(root, "summary.costs")) != root);
		REQUIRE(stats->type(costs) == Potassco::Statistics_t::Array);
		REQUIRE(stats->size(costs) == 1);
		REQUIRE((minVal = stats->get(root, "summary.costs.0")) != root);
		REQUIRE(stats->type(minVal) == Potassco::Statistics_t::Value);
		config.solve.numModels = -1;
		libclasp.update(true);
		lpAdd(asp, ":- not x1.");
		libclasp.solve();
		REQUIRE(stats->type(costs) == Potassco::Statistics_t::Array);
		REQUIRE(stats->size(costs) == 0);
		REQUIRE_THROWS_AS(stats->value(minVal), std::logic_error);
	}
	SECTION("testWritableStats") {
		ClaspStatistics stats;
		typedef ClaspStatistics::Key_t Key_t;
		StatsMap* rootMap = stats.makeRoot();
		double v1 = 2.0;
		rootMap->add("fixed", StatisticObject::value(&v1));

		Key_t root = stats.root();
		REQUIRE(stats.writable(root));
		REQUIRE(stats.writable(stats.get(root, "fixed")) == false);

		Key_t v2 = stats.add(root, "mutable", Potassco::Statistics_t::Value);
		REQUIRE(stats.writable(v2));
		stats.set(v2, 22.0);
		REQUIRE(stats.value(v2) == 22.0);
		Key_t found;
		REQUIRE(stats.find(root, "mutable", &found));
		REQUIRE(found == v2);

		Key_t arr = stats.add(root, "array", Potassco::Statistics_t::Array);
		REQUIRE(stats.type(arr) == Potassco::Statistics_t::Array);
		REQUIRE(stats.writable(arr));
		REQUIRE(stats.size(arr) == 0);

		Key_t mapAtArr0 = stats.push(arr, Potassco::Statistics_t::Map);
		REQUIRE(stats.type(mapAtArr0) == Potassco::Statistics_t::Map);
		REQUIRE(stats.size(arr) == 1);
	}
	SECTION("testClingoUserStats") {
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp, "{x1;x2;x3}. #minimize{x1, x2}.");
		libclasp.addStatisticsCallback(addExternalStats, 0);
		libclasp.prepare();
		libclasp.solve();
		Potassco::AbstractStatistics* stats = libclasp.getStats();
		typedef Potassco::AbstractStatistics::Key_t Key_t;
		Key_t r = stats->root();
		REQUIRE(stats->type(r) == Potassco::Statistics_t::Map);
		Key_t u = stats->get(r, "user_defined");
		REQUIRE(stats->type(u) == Potassco::Statistics_t::Map);
		Key_t user = stats->get(u, "deathCounter");
		REQUIRE(stats->type(user) == Potassco::Statistics_t::Map);
		REQUIRE(stats->value(stats->get(user, "total")) == double(42));
		REQUIRE(stats->value(stats->get(user, "chickens")) == double(712));
		Key_t array = stats->get(user, "thread");
		REQUIRE(stats->type(array) == Potassco::Statistics_t::Array);
		REQUIRE(stats->size(array) == 4);
		for (size_t t = 0; t != 4; ++t) {
			Key_t m1 = stats->at(array, t);
			REQUIRE(stats->type(m1) == Potassco::Statistics_t::Map);
			Key_t value = stats->get(m1, "total");
			REQUIRE(stats->type(value) == Potassco::Statistics_t::Value);
			REQUIRE(stats->value(value) == double(20*(t+1)));
			Key_t m2 = stats->get(m1, "Animals");
			REQUIRE(stats->type(m2) == Potassco::Statistics_t::Map);
			value = stats->get(m2, "chicken");
			REQUIRE(stats->value(value) == double(2*(t+1)));
			value = stats->get(m2, "cows");
			REQUIRE(stats->value(value) == double(5*(t+1)));
			value = stats->get(m1, "feeding cost");
			REQUIRE(stats->value(value) == double(t+1));
		}
		Key_t total;
		REQUIRE(stats->find(r, "user_defined.deathCounter.thread.1.total", &total));
		REQUIRE(stats->type(total) == Potassco::Statistics_t::Value);
		REQUIRE(stats->value(total) == 40.0);
		REQUIRE(!stats->find(r, "user_defined.deathCounter.thread.5.total", 0));

		std::vector<std::string> keys;
		getStatsKeys(*stats, r, keys, "");
		REQUIRE(!keys.empty());
		for (std::vector<std::string>::const_iterator it = keys.begin(), end = keys.end(); it != end; ++it) {
			REQUIRE(stats->find(r, it->c_str(), 0));
			REQUIRE(stats->type(stats->get(r, it->c_str())) == Potassco::Statistics_t::Value);
		}
		REQUIRE(keys.size() == 255);
	}
}
namespace {
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

struct PropagatorTest {
	void addVars(int num) {
		v.resize(num + 1);
		v[0] = 0;
		for (int i = 1; i <= num; ++i) {
			v[i] = ctx.addVar(Var_t::Atom);
		}
		ctx.startAddConstraints();
	}
	SharedContext ctx;
	VarVec v;
};
}
TEST_CASE("Clingo propagator", "[facade][propagator]") {
	typedef ClingoPropagatorInit MyInit;
	PropagatorTest test;
	SharedContext& ctx = test.ctx;
	VarVec&        v = test.v;
	MyProp         prop;
	MyInit         tp(prop);

	SECTION("testAssignment") {
		class Prop : public Potassco::AbstractPropagator {
		public:
			Prop() {}
			virtual void propagate(Potassco::AbstractSolver&, const ChangeList&)  {}
			virtual void undo(const Potassco::AbstractSolver&, const ChangeList&) {}
			virtual void check(Potassco::AbstractSolver& s) {
				const Potassco::AbstractAssignment& a = s.assignment();
				REQUIRE(!a.hasConflict());
				REQUIRE(a.level() == 2);
				REQUIRE(a.value(v1) == Potassco::Value_t::True);
				REQUIRE(a.value(v2) == Potassco::Value_t::False);
				REQUIRE(a.isTrue(v1));
				REQUIRE(a.isFalse(v2));
				REQUIRE(a.isTrue(Potassco::neg(v2)));
				REQUIRE(a.level(v1) == 1);
				REQUIRE(a.level(v2) == 2);
				REQUIRE(!a.hasLit(v2+1));
				REQUIRE(a.decision(0) == encodeLit(lit_true()));
				REQUIRE(a.decision(1) == v1);
				REQUIRE(a.decision(2) == Potassco::neg(v2));
			}
			Potassco::Lit_t v1, v2;
		} prop;
		test.addVars(2);
		prop.v1 = encodeLit(posLit(v[1]));
		prop.v2 = encodeLit(posLit(v[2]));
		MyInit pp(prop);
		pp.addPost(*ctx.master());
		ctx.endInit();
		ctx.master()->assume(posLit(v[1])) && ctx.master()->propagate();
		ctx.master()->assume(negLit(v[2])) && ctx.master()->propagate();
		ctx.master()->search(0, 0);
	}

	SECTION("testPropagateChange") {
		test.addVars(5);
		tp.addWatch(posLit(v[1]));
		tp.addWatch(posLit(v[1])); // ignore duplicates
		tp.addWatch(posLit(v[2]));
		tp.addWatch(posLit(v[3]));
		tp.addWatch(negLit(v[3]));
		tp.addWatch(negLit(v[4]));
		tp.addPost(*ctx.master());
		ctx.endInit();
		Solver& s = *ctx.master();
		s.assume(posLit(v[1])) && s.propagate();
		REQUIRE((prop.change.size() == 1 && prop.change[0] == posLit(v[1])));

		s.assume(negLit(v[4])) && s.force(posLit(v[2]), 0) && s.propagate();
		REQUIRE((prop.change.size() == 2 && prop.change[0] == negLit(v[4]) && prop.change[1] == posLit(v[2])));
		prop.change.clear();
		s.undoUntil(s.decisionLevel()-1);
		REQUIRE((prop.change.size() == 2 && prop.change[0] == negLit(v[4]) && prop.change[1] == posLit(v[2])));
		s.undoUntil(s.decisionLevel()-1);
		REQUIRE((prop.change.size() == 1 && prop.change[0] == posLit(v[1])));
		prop.change.clear();
		s.assume(negLit(v[2])) && s.propagate();
		REQUIRE(prop.change.empty());
	}
	SECTION("testAddClause") {
		test.addVars(3);
		tp.addWatch(prop.fire = negLit(v[3]));
		prop.addToClause(posLit(v[1]));
		prop.addToClause(posLit(v[2]));
		tp.addPost(*ctx.master());
		ctx.endInit();
		Solver& s = *ctx.master();
		s.assume(negLit(v[3])) && s.propagate();
		REQUIRE(ctx.numLearntShort() == 1);
	}
	SECTION("testAddUnitClause") {
		test.addVars(3);
		tp.addWatch(prop.fire = negLit(v[3]));
		prop.addToClause(posLit(v[1]));
		prop.addToClause(posLit(v[2]));
		tp.addPost(*ctx.master());
		ctx.endInit();
		Solver& s = *ctx.master();
		s.assume(negLit(v[2])) && s.propagate();
		s.assume(negLit(v[3])) && s.propagate();
		REQUIRE(ctx.numLearntShort() == 1);
		REQUIRE(s.isTrue(posLit(v[1])));
		REQUIRE((prop.change.size() == 1 && prop.change[0] == negLit(v[3])));
	}
	SECTION("testAddUnitClauseWithUndo") {
		test.addVars(5);
		prop.fire = posLit(v[5]);
		tp.addWatch(posLit(v[3]));
		tp.addWatch(posLit(v[5]));
		prop.addToClause(posLit(v[1]));
		prop.addToClause(posLit(v[2]));
		prop.addToClause(posLit(v[3]));
		tp.addPost(*ctx.master());
		ctx.endInit();
		Solver& s = *ctx.master();
		s.assume(negLit(v[1])) && s.propagate();
		s.assume(posLit(v[4])) && s.propagate();
		s.assume(negLit(v[2])) && s.propagate();
		s.assume(posLit(v[5])) && s.propagate();
		REQUIRE(ctx.numLearntShort() == 1);
		REQUIRE(s.decisionLevel() == 3);
		s.undoUntil(2);
		REQUIRE(std::find(prop.change.begin(), prop.change.end(), posLit(v[3])) != prop.change.end());
	}
	SECTION("testAddUnsatClause") {
		test.addVars(3);
		tp.addWatch(prop.fire = negLit(v[3]));
		prop.addToClause(posLit(v[1]));
		prop.addToClause(posLit(v[2]));
		tp.addPost(*ctx.master());
		ctx.endInit();
		Solver& s = *ctx.master();
		s.assume(negLit(v[2])) && s.propagate();
		s.assume(negLit(v[1])) && s.propagate();
		s.assume(negLit(v[3]));
		s.pushRootLevel(2);
		REQUIRE_FALSE(s.propagate());
		INFO("do not add conflicting constraint");
		REQUIRE(ctx.numLearntShort() == 0);
		s.popRootLevel(1);
		REQUIRE(s.decisionLevel() == 1);
		prop.clause.clear();
		prop.addToClause(negLit(v[2]));
		prop.addToClause(posLit(v[3]));
		s.assume(negLit(v[3]));
		REQUIRE(s.propagate());
		INFO("do not add sat constraint");
		REQUIRE(ctx.numLearntShort() == 0);
	}
	SECTION("testAddEmptyClause") {
		test.addVars(1);
		tp.addWatch(prop.fire = negLit(v[1]));
		prop.addToClause(negLit(0));
		tp.addPost(*ctx.master());
		ctx.endInit();
		Solver& s = *ctx.master();
		s.assume(negLit(v[1]));
		REQUIRE_FALSE(s.propagate());
	}
	SECTION("testAddSatClause") {
		test.addVars(3);
		tp.addWatch(prop.fire = negLit(v[3]));
		prop.addToClause(posLit(v[1]));
		prop.addToClause(posLit(v[2]));
		tp.addPost(*ctx.master());
		ctx.endInit();
		Solver& s = *ctx.master();
		s.assume(posLit(v[1])) && s.force(negLit(v[2]), posLit(v[1])) && s.propagate();
		s.assume(negLit(v[3]));
		REQUIRE((s.decisionLevel() == 2 && !s.hasConflict()));
		REQUIRE(s.propagate());
		REQUIRE(uint32(2) == s.decisionLevel());
	}
	SECTION("testAddClauseOnModel") {
		test.addVars(3);
		prop.addToClause(posLit(v[1]));
		prop.addToClause(posLit(v[3]));
		tp.addPost(*ctx.master());
		ctx.endInit();
		Solver& s = *ctx.master();
		ValueRep v = s.search(-1, -1);
		REQUIRE((v == value_true && s.numFreeVars() == 0));
		REQUIRE(ctx.shortImplications().numLearnt() == 1);
	}
	SECTION("testAddConflictOnModel") {
		test.addVars(3);
		prop.addToClause(negLit(v[1]));
		prop.addToClause(negLit(v[2]));
		tp.addPost(*ctx.master());
		ctx.endInit();
		Solver& s = *ctx.master();
		s.assume(posLit(v[1]));
		s.force(posLit(v[2]), posLit(v[1]));
		s.propagate();
		s.assume(posLit(v[3])) && s.propagate();
		REQUIRE((!s.hasConflict() && s.numFreeVars() == 0));
		REQUIRE(!s.getPost(PostPropagator::priority_class_general)->isModel(s));
		REQUIRE(s.hasConflict());
		REQUIRE((s.decisionLevel() == 1 && s.resolveConflict()));
	}

	SECTION("testAddStatic") {
		test.addVars(2);
		prop.addToClause(posLit(v[1]));
		prop.addToClause(posLit(v[2]));
		prop.fire = lit_true();
		prop.clProp = Potassco::Clause_t::Static;
		tp.addWatch(negLit(v[1]));
		tp.addPost(*ctx.master());
		ctx.endInit();

		Solver& s = *ctx.master();
		REQUIRE(s.numWatches(negLit(v[2])) == 0);
		s.assume(negLit(v[1])) && s.propagate();
		REQUIRE(s.numWatches(negLit(v[2])) == 1);
		s.reduceLearnts(1.0);
		REQUIRE(s.numWatches(negLit(v[2])) == 1);
	}
	SECTION("with facade") {
		ClaspConfig config;
		ClaspFacade libclasp;
		config.addConfigurator(&tp);
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
		lpAdd(asp, "{x1;x2}.");
		asp.endProgram();
		SECTION("testAttachToSolver") {
			for (Var v = 1; v <= libclasp.ctx.numVars(); ++v) {
				tp.addWatch(posLit(v));
				tp.addWatch(negLit(v));
			}
			REQUIRE(prop.change.empty());
			libclasp.prepare();
			libclasp.solve();
			REQUIRE(!prop.change.empty());
#if CLASP_HAS_THREADS
			config.solve.setSolvers(2);
			libclasp.update(true);
			libclasp.prepare();
			REQUIRE((libclasp.ctx.concurrency() == 2 && libclasp.ctx.hasSolver(1)));
			libclasp.solve();
			REQUIRE(libclasp.ctx.solver(1)->getPost(PostPropagator::priority_class_general) != 0);
			config.solve.setSolvers(1);
			libclasp.update(true);
			libclasp.prepare();
			REQUIRE(libclasp.ctx.concurrency() == 1);
			config.solve.setSolvers(2);
			libclasp.update(true);
			libclasp.solve();
			REQUIRE(libclasp.ctx.solver(1)->getPost(PostPropagator::priority_class_general) != 0);
#endif
		}
		SECTION("testAddVolatile") {
			tp.addWatch(negLit(1));
			prop.addToClause(posLit(1));
			prop.addToClause(posLit(2));
			libclasp.prepare();
			prop.fire = libclasp.ctx.stepLiteral();
			prop.clProp = Potassco::Clause_t::Volatile;
			libclasp.solve();
			REQUIRE(libclasp.ctx.numLearntShort() == 1);
			libclasp.update();
			REQUIRE(libclasp.ctx.numLearntShort() == 0);
		}
		SECTION("testAddVolatileStatic") {
			tp.addWatch(negLit(1));
			prop.addToClause(posLit(1));
			prop.addToClause(posLit(2));
			libclasp.prepare();
			prop.fire = libclasp.ctx.stepLiteral();
			prop.clProp = Potassco::Clause_t::VolatileStatic;
			libclasp.solve();
			REQUIRE(libclasp.ctx.master()->numWatches(negLit(2)) == 1);
			libclasp.update();
			REQUIRE(libclasp.ctx.master()->numWatches(negLit(2)) == 0);
		}
		SECTION("testLookaheadBug") {
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
			tp.addWatch(negLit(1));
			libclasp.prepare();
			REQUIRE(libclasp.ctx.master()->isTrue(negLit(1)));
			REQUIRE(prop.change.size() == 1);
			REQUIRE(prop.change[0] == negLit(1));
		}
	}
	SECTION("with special propagator") {
		ClaspConfig config;
		ClaspFacade libclasp;
		SECTION("testPushVariable") {
			class AddVar : public Potassco::AbstractPropagator {
			public:
				typedef Potassco::Lit_t Lit_t;
				explicit AddVar(uint32 nAux) : aux_(nAux), next_(1) {}
				virtual void propagate(Potassco::AbstractSolver& s, const ChangeList&) {
					if (aux_) {
						const Potassco::AbstractAssignment& as = s.assignment();
						while (as.hasLit(next_)) { ++next_; }
						Lit_t x = s.addVariable();
						REQUIRE(x == next_);
						REQUIRE((!s.hasWatch(x) && !s.hasWatch(-x)));
						s.addWatch(x);
						REQUIRE((s.hasWatch(x) && !s.hasWatch(-x)));
						s.addWatch(-x);
						REQUIRE((s.hasWatch(x) && s.hasWatch(-x)));
						s.removeWatch(x);
						REQUIRE((!s.hasWatch(x) && s.hasWatch(-x)));
						s.removeWatch(-x);
						REQUIRE((!s.hasWatch(x) && !s.hasWatch(-x)));
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
			REQUIRE(nv == libclasp.ctx.numVars());
			REQUIRE(sv == libclasp.ctx.master()->numVars());
		}
		SECTION("testAuxVarMakesClauseVolatile") {
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
					REQUIRE((!nextStep || !s.assignment().hasLit(aux)));
				}
				virtual void undo(const Potassco::AbstractSolver&, const ChangeList&) {}
				virtual void check(Potassco::AbstractSolver&) {}
				Lit_t aux;
				bool  nextStep;
			} prop;
			MyInit pp(prop);
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

		SECTION("testRootLevelBug") {
			class Prop : public Potassco::AbstractPropagator {
			public:
				Prop() {}
				virtual void propagate(Potassco::AbstractSolver& s, const ChangeList&) {
					REQUIRE(s.assignment().level() != 0);
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
			config.addConfigurator(&pp);
			Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
			lpAdd(asp, "{x1;x2}.");
			asp.endProgram();
			pp.addWatch(posLit(1));
			pp.addWatch(negLit(1));
			pp.addWatch(posLit(2));
			pp.addWatch(negLit(2));
			libclasp.prepare();
			REQUIRE(libclasp.solve().unsat());
		}

		SECTION("testRelocationBug") {
			class Prop : public Potassco::AbstractPropagator {
			public:
				Prop() {}
				virtual void propagate(Potassco::AbstractSolver& s, const ChangeList& changes) {
					Potassco::LitVec cmp(begin(changes), end(changes));
					Potassco::LitVec clause;
					clause.assign(1, 0);
					for (uint32 i = 1; i <= s.assignment().level(); ++i) {
						clause.push_back(-s.assignment().decision(i));
					}
					for (Potassco::Lit_t lit = 1; s.assignment().hasLit(lit); ++lit) {
						if (s.assignment().value(lit) == Potassco::Value_t::Free) {
							clause[0] = lit;
							s.addClause(Potassco::toSpan(clause));
							s.propagate();
						}
					}
					REQUIRE(std::memcmp(&cmp[0], changes.first, changes.size * sizeof(Potassco::Lit_t)) == 0);
				}
				virtual void undo(const Potassco::AbstractSolver&, const ChangeList&) {}
				virtual void check(Potassco::AbstractSolver&) {}
			} prop;
			MyInit pp(prop);
			config.addConfigurator(&pp);
			Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config, true);
			lpAdd(asp, "{x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15;x16}.");
			asp.endProgram();
			for (Var v = 1; v <= libclasp.ctx.numVars(); ++v) {
				pp.addWatch(posLit(v));
				pp.addWatch(negLit(v));
			}
			libclasp.prepare();
			REQUIRE(libclasp.solve().sat());
		}
	}
	SECTION("test check mode") {
		ClaspConfig config;
		ClaspFacade libclasp;
		class Prop : public Potassco::AbstractPropagator {
		public:
			Prop() : last(0), checks(0), props(0), totals(0), fire(false) {}
			virtual void propagate(Potassco::AbstractSolver& s, const ChangeList& c) {
				const Potassco::AbstractAssignment& a = s.assignment();
				++props;
				if (*Potassco::begin(c) == last) { return; }
				for (int x = *Potassco::begin(c) + 1; a.hasLit(x); ++x) {
					if (a.value(x) == Potassco::Value_t::Free) {
						last = x;
						s.addClause(Potassco::toSpan(&x, 1));
						break;
					}
				}
			}
			virtual void undo(const Potassco::AbstractSolver&, const ChangeList&) {}
			virtual void check(Potassco::AbstractSolver& s) {
				const Potassco::AbstractAssignment& a = s.assignment();
				++checks;
				totals += a.isTotal();
				if (fire) {
					for (int x = 1; a.hasLit(x); ++x) {
						if (a.value(x) == Potassco::Value_t::Free) {
							s.addClause(Potassco::toSpan(&x, 1));
							return;
						}
					}
					REQUIRE(a.isTotal());
					REQUIRE(a.level() == 0);
				}
			}
			int last;
			int checks;
			int props;
			int totals;
			bool fire;
		} prop;
		MyInit pp(prop);
		config.addConfigurator(&pp);
		Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config);
		lpAdd(asp, "{x1;x2;x3;x4;x5}.");
		asp.endProgram();
		SECTION("test check and propagate") {
			prop.fire = true;
			pp.addWatch(posLit(1));
			pp.addWatch(posLit(2));
			pp.addWatch(posLit(3));
			pp.addWatch(posLit(4));
			pp.addWatch(posLit(5));
			pp.enableClingoPropagatorCheck(ClingoPropagatorCheck_t::Fixpoint);
			libclasp.prepare();
			REQUIRE(libclasp.ctx.master()->numFreeVars() == 0);
		}
		SECTION("test check is called only once per fixpoint") {
			pp.enableClingoPropagatorCheck(ClingoPropagatorCheck_t::Fixpoint);
			libclasp.prepare();
			REQUIRE(prop.checks == 1u);
			libclasp.ctx.master()->propagate();
			REQUIRE(prop.checks == 1u);
			libclasp.ctx.master()->pushRoot(posLit(1));
			REQUIRE(prop.checks == 2u);
			libclasp.ctx.master()->assume(posLit(2)) && libclasp.ctx.master()->propagate();
			REQUIRE(prop.checks == 3u);
			libclasp.ctx.master()->propagate();
			REQUIRE(prop.checks == 3u);
			libclasp.ctx.master()->restart();
			libclasp.ctx.master()->propagate();
			INFO("Restart introduces new fix point");
			REQUIRE(prop.checks == 4u);
		}
		SECTION("with mode total check is called once on total") {
			pp.enableClingoPropagatorCheck(ClingoPropagatorCheck_t::Total);
			libclasp.solve();
			REQUIRE(prop.checks == 1u);
			REQUIRE(prop.totals == 1u);
		}
		SECTION("with mode fixpoint check is called once on total") {
			pp.enableClingoPropagatorCheck(ClingoPropagatorCheck_t::Fixpoint);
			libclasp.solve();
			REQUIRE(prop.checks > 1u);
			REQUIRE(prop.totals == 1u);
		}
	}
}
} }
