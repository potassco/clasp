//
// Copyright (c) 2006-present Benjamin Kaufmann
//
// This file is part of Clasp. See https://potassco.org/clasp/
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
#include "lpcompare.h"
#include <clasp/clasp_facade.h>

#include <clasp/clingo.h>
#include <clasp/heuristics.h>
#include <clasp/lookahead.h>
#include <clasp/minimize_constraint.h>
#include <clasp/model_enumerators.h>
#include <clasp/solver.h>
#if CLASP_HAS_THREADS
#include <clasp/mt/thread.h>
#endif

#include <catch2/catch_test_macros.hpp>

#include <csignal>

namespace Clasp::Test {
#if CLASP_HAS_THREADS
using namespace Clasp::mt;
#endif
using StatsType = Potassco::StatisticsType;

static ClaspConfig& update(ClaspConfig& c) {
    c.prepared = false;
    return c;
}

void addExternalStats(Potassco::AbstractStatistics* us, Potassco::AbstractStatistics::Key_t userRoot) {
    auto general = us->add(userRoot, "deathCounter", StatsType::map);
    REQUIRE(us->get(userRoot, "deathCounter") == general);
    REQUIRE(us->type(general) == StatsType::map);
    auto value = us->add(general, "total", StatsType::value);
    us->set(value, 42.0);
    value = us->add(general, "chickens", StatsType::value);
    us->set(value, 712.0);

    auto array = us->add(general, "thread", StatsType::array);
    REQUIRE(us->get(general, "thread") == array);
    REQUIRE(us->type(array) == StatsType::array);
    REQUIRE(us->size(array) == 0);
    for (auto t : irange(4u)) {
        auto a = us->push(array, StatsType::map);
        value  = us->add(a, "total", StatsType::value);
        us->set(value, 20 * static_cast<double>(t + 1));
        auto m = us->add(a, "Animals", StatsType::map);
        value  = us->add(m, "chicken", StatsType::value);
        us->set(value, 2 * static_cast<double>(t + 1));
        value = us->add(m, "cows", StatsType::value);
        us->set(value, 5 * static_cast<double>(t + 1));
        value = us->add(a, "feeding cost", StatsType::value);
        us->set(value, static_cast<double>(t + 1));
    }
    REQUIRE(us->add(userRoot, "deathCounter", StatsType::map) == general);
}
auto addExternalStats(Potassco::AbstractStatistics* us,
                      std::string_view              userRoot) -> Potassco::AbstractStatistics::Key_t {
    auto r = us->root();
    auto u = us->add(r, userRoot, StatsType::map);
    addExternalStats(us, u);
    return u;
}

TEST_CASE("Facade", "[facade]") {
    ClaspConfig config;
    ClaspFacade libclasp;
    SECTION("clasp config") {
        struct TestConfigurator : ClaspConfig::Configurator {
            bool addPropagators(Solver&) override { return propCalled = true; }
            void setHeuristic(Solver&) override { heuCalled = true; }
            bool propCalled = false;
            bool heuCalled  = false;
        } configurator;
        config.setConfigurator(&configurator, false);
        SharedContext     ctx;
        Asp::LogicProgram prg;
        ctx.setConfiguration(&config);
        lpAdd(prg.start(ctx), "{x2}. x1 :- 1 {x1, x2}.");
        REQUIRE(prg.endProgram());
        REQUIRE(ctx.endInit());
        REQUIRE(ctx.sccGraph);
        REQUIRE(configurator.propCalled);
        REQUIRE(configurator.heuCalled);
        REQUIRE(ctx.master()->getPost(PostPropagator::priority_reserved_ufs));
    }
    SECTION("clasp config lifecycle") {
        struct TestConfigurator : ClaspConfig::Configurator {
            ~TestConfigurator() override {
                if (config) {
                    config->setConfigurator(nullptr, false);
                }
            }
            bool addPropagators(Solver&) override { return true; }
            void setHeuristic(Solver&) override {}
            void detach(const ClaspConfig& c) override {
                if (&c == config) {
                    config = nullptr;
                }
            }
            ClaspConfig* config{nullptr};
        } configurator;
        auto c              = std::make_unique<ClaspConfig>();
        configurator.config = c.get();
        SECTION("config notifies configurator on destruction") {
            c->setConfigurator(&configurator, true);
            c.reset();
            REQUIRE(configurator.config == nullptr);
        }
        SECTION("config does not notify configuration if not requested") {
            c->setConfigurator(&configurator, false);
            c.reset();
            auto cfg = std::exchange(configurator.config, nullptr);
            REQUIRE(cfg != nullptr);
        }
        SECTION("notification can be disabled afterwards") {
            c->setConfigurator(&configurator, true);
            c->setConfigurator(&configurator, false);
            CHECK(configurator.config == c.get());
            c.reset();
            auto cfg = std::exchange(configurator.config, nullptr);
            REQUIRE(cfg != nullptr);
        }
    }
    SECTION("with trivial program") {
        config.solve.numModels = 0;
        auto& asp              = libclasp.startAsp(config, true);
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
            struct PostProp : PostPropagator {
                [[nodiscard]] uint32_t priority() const override { return priority_reserved_msg; }
                bool                   propagateFixpoint(Solver& s, PostPropagator*) override {
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
            REQUIRE(libclasp.update());
            REQUIRE(libclasp.update());
            libclasp.prepare();
            REQUIRE(libclasp.solve().sat());
            REQUIRE(libclasp.summary().numEnum == 2);
            REQUIRE(libclasp.summary().step == 0);
        }
        SECTION("testUpdateWithoutSolveDoesNotIncStep") {
            libclasp.prepare();
            REQUIRE(libclasp.update());
            libclasp.prepare();

            REQUIRE(libclasp.solve().sat());
            REQUIRE(libclasp.summary().numEnum == 2);
            REQUIRE(libclasp.summary().step == 0);
        }
        SECTION("test interrupt") {
            struct FinishHandler : EventHandler {
                FinishHandler() = default;
                void onEvent(const Event& ev) override {
                    finished += event_cast<ClaspFacade::StepReady>(ev) != nullptr;
                }
                int finished{0};
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
                REQUIRE_FALSE(libclasp.solved());
                REQUIRE(libclasp.solve(LitVec(), &fh).interrupted());
                REQUIRE(libclasp.solved());
                REQUIRE(fh.finished == 1);
            }
            SECTION("interruptAfterSolveInterruptsNext") {
                libclasp.prepare();
                REQUIRE_FALSE(libclasp.solve(LitVec(), &fh).interrupted());
                REQUIRE(fh.finished == 1);
                REQUIRE(libclasp.solved());
                REQUIRE_FALSE(libclasp.interrupted());
                REQUIRE(libclasp.interrupt(1) == false);
                REQUIRE(libclasp.solve(LitVec(), &fh).interrupted());
                REQUIRE(fh.finished == 2);
            }
            SECTION("interruptBeforeUpdateInterruptsNext") {
                libclasp.prepare();
                libclasp.interrupt(1);
                libclasp.update();
                REQUIRE_FALSE(libclasp.interrupted());
                REQUIRE(libclasp.solve().interrupted());
            }
        }
        SECTION("testUpdateCanIgnoreQueuedSignals") {
            libclasp.prepare();
            libclasp.interrupt(1);
            libclasp.update(SIG_IGN);
            REQUIRE_FALSE(libclasp.solve().interrupted());
        }
        SECTION("testShutdownStopsStep") {
            libclasp.prepare();
            libclasp.shutdown();
            REQUIRE(libclasp.solved());
        }
        SECTION("testSolveUnderAssumptions") {
            auto ext = asp.newAtom();
            asp.freeze(ext, value_true);
            libclasp.prepare();
            LitVec assume(1, asp.getLiteral(1));
            struct ModelHandler : EventHandler {
                ModelHandler() = default;
                bool onModel(const Solver&, const Model& m) override {
                    for (auto lit : exp) { REQUIRE(m.isTrue(lit)); }
                    ++models;
                    return true;
                }
                LitVec exp;
                int    models{0};
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
        auto& asp = libclasp.startAsp(config);
        REQUIRE_FALSE(asp.frozen());
    }

    SECTION("testUpdateChecks") {
        lpAdd(libclasp.startAsp(config), "a :- not b. b :- not a.");

        SECTION("cannotSolveAgainInSingleSolveMode") {
            REQUIRE(libclasp.solve().sat());
            REQUIRE_THROWS_AS(libclasp.prepare(), std::logic_error);
            REQUIRE_THROWS_AS(libclasp.solve(), std::logic_error);
        }

        SECTION("maySolveAgainInMultiSolveMode") {
            libclasp.ctx.setSolveMode(Clasp::SharedContext::solve_multi);
            REQUIRE(libclasp.solve().sat());
            REQUIRE_NOTHROW(libclasp.prepare());
            REQUIRE_FALSE(libclasp.solved());
            REQUIRE(libclasp.solve().sat());
        }

        SECTION("cannotUpdateInSingleShotMode") {
            auto& asp = libclasp.startAsp(config);
            libclasp.keepProgram();
            lpAdd(asp, "a :- not b. b :- not a.");
            REQUIRE(libclasp.solve().sat());
            REQUIRE_THROWS_AS(libclasp.update(), std::logic_error);
            REQUIRE_THROWS_AS(libclasp.prepare(), std::logic_error);
        }
    }

    SECTION("testPrepareTooStrongBound") {
        config.solve.numModels = 0;
        config.solve.optBound.assign(1, 0);
        lpAdd(libclasp.startAsp(config, true), "a :-not b.\n"
                                               "b :-not a.\n"
                                               "c.\n"
                                               "#minimize{c, a, b}.");

        libclasp.prepare();
        REQUIRE(libclasp.solve().unsat());
    }

    SECTION("testUnsatCore") {
        config.solve.numModels = 0;
        auto&       asp        = libclasp.startAsp(config, true);
        int         expect     = 0;
        std::string prg;
        SECTION("AssumeFalse") {
            prg    = "a.\n#assume{not a}.";
            expect = -1;
        }
        SECTION("AssumeTrue") {
            prg    = "a :- b.\nb :- a.\n#assume{a}.";
            expect = 1;
        }
        INFO(prg);
        lpAdd(asp, prg.c_str());
        libclasp.prepare();
        REQUIRE(libclasp.solve().unsat());
        auto core = libclasp.summary().unsatCore();
        CHECK(core.size() == 1);
        Potassco::LitVec out;
        CHECK(asp.translateCore(core, out));
        CHECK(out.size() == 1);
        CHECK(out[0] == expect);
    }

    SECTION("testIssue81") {
        config.solve.numModels = 0;
        auto& asp              = libclasp.startAsp(config, true);
        lpAdd(asp, "{x}.\n"
                   "a :- x.\n"
                   "b :- not x.\n"
                   "#assume{a,b}.");
        libclasp.prepare();
        REQUIRE(libclasp.solve().unsat());
        auto core = libclasp.summary().unsatCore();
        CHECK(core.size() == 2);
        Potassco::LitVec out;
        CHECK(asp.translateCore(core, out));
        CHECK(out.size() == 2);
        CHECK(out[0] == 1);
        CHECK(out[1] == 2);
    }

    SECTION("testIssue84") {
        config.solve.numModels = 0;
        auto& asp              = libclasp.startAsp(config, false);
        lpAdd(asp, "d:-b.\n"
                   "t|f :-c, d.\n"
                   "d :-t.\n"
                   "a :-c, d.\n"
                   "{b;c }.\n");
        libclasp.prepare();
        REQUIRE(libclasp.ctx.numBinary() + libclasp.ctx.numTernary() == 16);
        REQUIRE(libclasp.solve().sat());
        REQUIRE(libclasp.ctx.numBinary() + libclasp.ctx.numTernary() == 0);
        REQUIRE(libclasp.summary().numEnum == 5);
    }

    SECTION("testIssue101 - preserve heuristic") {
        REQUIRE_FALSE(libclasp.ctx.preserveHeuristic());
        REQUIRE(static_cast<uint32_t>(libclasp.ctx.defaultDomPref()) > 32u);
        SECTION("preserve heuristic") {
            SECTION("if incremental") {
                libclasp.startAsp(config, true);
                libclasp.prepare();
                REQUIRE(libclasp.ctx.preserveHeuristic());
            }
            SECTION("if domain heuristic is used") {
                config.addSolver(0).heuId = +HeuristicType::domain;
                auto& asp                 = libclasp.startAsp(config, false);
                lpAdd(asp, "{a;b;c;d}. #heuristic a. [1@1,true] #output b : b.");
                libclasp.prepare();
                REQUIRE(libclasp.ctx.preserveHeuristic());
                config.addSolver(0).heuristic.domMod  = HeuParams::mod_level;
                config.addSolver(0).heuristic.domPref = HeuParams::pref_show | HeuParams::pref_min;
                REQUIRE(libclasp.ctx.defaultDomPref() == uint32_t(HeuParams::pref_show | HeuParams::pref_min));
                REQUIRE_FALSE(libclasp.ctx.varInfo(1).frozen());
                REQUIRE_FALSE(libclasp.ctx.varInfo(2).frozen());
            }
            SECTION("if explicitly set") {
                libclasp.startAsp(config, false);
                libclasp.ctx.setPreserveHeuristic(true);
                REQUIRE(libclasp.ctx.preserveHeuristic());
            }
        }
        SECTION("freeze vars") {
            config.satPre.type        = SatPreParams::sat_pre_full;
            config.addSolver(0).heuId = +HeuristicType::domain;
            auto& asp                 = libclasp.startAsp(config, false);
            lpAdd(asp, "{a;b;c;d}. #heuristic a. [1@1,true] #output b : b.");
            SECTION("with explicit heuristic mod") {
                libclasp.prepare();
                REQUIRE(libclasp.ctx.varInfo(1).frozen());
                REQUIRE_FALSE(libclasp.ctx.varInfo(2).frozen());
            }
            SECTION("with implicit heuristic mod") {
                config.addSolver(0).heuristic.domMod  = HeuParams::mod_level;
                config.addSolver(0).heuristic.domPref = HeuParams::pref_show;
                libclasp.prepare();
                REQUIRE(libclasp.ctx.varInfo(1).frozen());
                REQUIRE(libclasp.ctx.varInfo(2).frozen());
                REQUIRE_FALSE(libclasp.ctx.varInfo(3).frozen());
            }
        }
    }

    SECTION("testComputeBrave22") {
        config.solve.numModels = 0;
        config.solve.enumMode  = EnumOptions::enum_brave;
        auto& asp              = libclasp.startAsp(config, true);

        lpAdd(asp, "a. {b; c}. {d}. :- d, b. :- d, c. :- b, c. :- not b, not c. #output a:a. #output b:b. #output c:c. "
                   "#output d:d.");
        libclasp.prepare();
        auto a     = asp.getLiteral(1);
        auto b     = asp.getLiteral(2);
        auto c     = asp.getLiteral(3);
        auto d     = asp.getLiteral(4);
        bool first = true;
        for (auto it = libclasp.solve(SolveMode::yield); it.next();) {
            const auto& m = it.model();
            REQUIRE(m->isCons(a) == value_true);
            REQUIRE(Asp::isConsequence(asp, 1, *m) == value_true);
            REQUIRE(Asp::isConsequence(asp, -1, *m) == value_false);
            REQUIRE(m->isCons(d) == value_free);
            REQUIRE(Asp::isConsequence(asp, 4, *m) == value_free);
            REQUIRE(m->isCons(c) == value_true);
            REQUIRE(Asp::isConsequence(asp, 3, *m) == value_true);
            if (std::exchange(first, false)) {
                REQUIRE(m->isCons(b) == value_free);
                REQUIRE(m->numConsequences(libclasp.ctx) == std::pair{2u, 2u});
            }
            else {
                REQUIRE(m->isCons(b) == value_true);
                REQUIRE(m->numConsequences(libclasp.ctx) == std::pair{3u, 1u});
            }
        }
        const auto& m = libclasp.summary().model();
        REQUIRE(m->def);
        REQUIRE(m->isCons(d) == value_false);
        REQUIRE(Asp::isConsequence(asp, 4, *m) == value_false);
        REQUIRE(m->numConsequences(libclasp.ctx) == std::pair{3u, 0u});
        libclasp.ctx.output.setProjectMode(ProjectMode::project);
        REQUIRE(Asp::isConsequence(asp, 1, *m) == value_false);
        libclasp.ctx.output.setProjectMode(ProjectMode::output);
        REQUIRE(Asp::isConsequence(asp, 1, *m) == value_true);
    }
    SECTION("testComputeBrave") {
        config.solve.numModels = 0;
        config.solve.enumMode  = EnumOptions::enum_brave;
        Asp::LogicProgram::OutputState expectedState;

        auto&       asp = libclasp.startAsp(config, true);
        std::string prg("x1 :- not x2.\n"
                        "x2 :- not x1.\n"
                        "x3 :- not x1.\n");

        SECTION("via output") {
            prg.append("#output a : x1.\n #output b : x2.\n");
            expectedState = Asp::LogicProgram::out_shown;
        }
        SECTION("via project") {
            prg.append("#project{x1, x2, x3}.");
            expectedState = Asp::LogicProgram::out_projected;
        }
#if CLASP_HAS_THREADS
        SECTION("with mt") {
            update(config).solve.algorithm.threads = 4;
            libclasp.update();
            prg.append("#output a : x1.\n #output b : x2.\n");
            expectedState = Asp::LogicProgram::out_shown;
        }
#endif
        lpAdd(asp, prg.c_str());
        libclasp.prepare();
        REQUIRE(asp.getOutputState(1) == expectedState);
        REQUIRE(asp.getOutputState(2) == expectedState);
        REQUIRE(libclasp.solve().sat());
        const Model& m = *libclasp.summary().model();
        REQUIRE(m.isDef(asp.getLiteral(1)));
        REQUIRE(m.isDef(asp.getLiteral(2)));
        REQUIRE(Asp::isConsequence(asp, 1, m) == value_true);
        REQUIRE(Asp::isConsequence(asp, 2, m) == value_true);
    }
    SECTION("testComputeQuery") {
        config.solve.numModels = 0;
        config.solve.enumMode  = EnumOptions::enum_query;
        auto& asp              = libclasp.startAsp(config, true);
        lpAdd(asp, "{a,b}."
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
        REQUIRE_FALSE(m.isDef(asp.getLiteral(1)));
        REQUIRE_FALSE(m.isDef(asp.getLiteral(2)));
    }
    SECTION("test opt enumerate") {
        config.solve.numModels = 0;
        config.solve.optMode   = MinimizeMode::enum_opt;
        lpAdd(libclasp.startAsp(config, false), "{x1;x2;x3}.\n"
                                                ":- not x1, not x2, not x3.\n"
                                                ":- x2, not x1.\n"
                                                ":- x3, not x1.\n"
                                                "#minimize{not x1}@0.\n"
                                                "#minimize{x1}@1.");
        libclasp.prepare();
        SECTION("with basic solve") {
            REQUIRE(libclasp.solve().sat());
            REQUIRE(uint64_t(4) == libclasp.summary().optimal());
        }
        SECTION("with generator") {
            unsigned num = 0, opt = 0;
            for (auto it = libclasp.solve(SolveMode::yield); it.next();) {
                ++num;
                opt += it.model()->opt;
            }
            REQUIRE((num > opt && opt == 4));
        }
    }

    SECTION("testProjectCautious") {
        int testId = 0;
        SECTION("show-def") { testId = 1; }
        SECTION("show-query") { testId = 2; }
        SECTION("project-def") { testId = 3; }
        SECTION("project-query") { testId = 4; }
        CHECK(testId != 0);
        bool        query          = (testId & 1) == 0;
        bool        project        = testId > 2;
        uint64_t    expectedModels = 2;
        auto        outState       = project ? Asp::LogicProgram::out_all : Asp::LogicProgram::out_shown;
        std::string testName       = std::string(project ? "project-" : "show-") + std::string(query ? "query" : "def");
        std::string prg            = "a. b. c.\n{d}.\ne :- not d.\n";
        for (const char* c = "abcde"; *c; ++c) {
            prg.append("#output ").append(1, *c).append(" : ").append(1, *c).append(".\n");
        }
        if (project) {
            prg.append("#project{a,b}.");
            expectedModels = 1;
        }
        CAPTURE(testName);
        config.solve.numModels = 0;
        config.solve.enumMode  = query ? EnumOptions::enum_query : EnumOptions::enum_cautious;
        auto& asp              = libclasp.startAsp(config, true);
        lpAdd(asp, prg.c_str());
        libclasp.prepare();
        CHECK(asp.getOutputState(1) == outState);
        CHECK(asp.getOutputState(2) == outState);
        CHECK(asp.getOutputState(3) == Asp::LogicProgram::out_shown);
        CHECK(asp.getOutputState(4) == Asp::LogicProgram::out_shown);
        CHECK(asp.getOutputState(5) == Asp::LogicProgram::out_shown);
        Literal  a = asp.getLiteral(1), b = asp.getLiteral(2), c = asp.getLiteral(3);
        Literal  d = asp.getLiteral(4), e = asp.getLiteral(5);
        uint64_t count = 0;
        for (auto it = libclasp.solve(SolveMode::yield); it.next();) {
            CAPTURE(count);
            const Model& m = *it.model();
            CHECK_FALSE(m.def);
            CHECK(m.isDef(a));
            CHECK(m.isDef(b));
            CHECK(m.isDef(c));
            CHECK(Asp::isConsequence(asp, 1, m) == value_true);
            CHECK(Asp::isConsequence(asp, 2, m) == value_true);
            if (libclasp.ctx.output.projectMode() == ProjectMode::output) {
                CHECK(Asp::isConsequence(asp, 3, m) == value_true);
            }
            else {
                CHECK(Asp::isConsequence(asp, 3, m) == value_false);
            }
            CHECK_FALSE(m.isDef(d));
            CHECK_FALSE(m.isDef(e));
            if (project) {
                CHECK_FALSE(m.isEst(d));
                CHECK_FALSE(m.isEst(e));
            }
            else {
                CHECK(m.isEst(d) == m.isTrue(d));
                CHECK(m.isEst(e) == m.isTrue(e));
            }
            ++count;
        }
        REQUIRE(expectedModels == count);
        REQUIRE(libclasp.summary().numEnum == count);
        const Model& m = *libclasp.summary().model();
        REQUIRE(m.def);
        REQUIRE(m.isDef(a));
        REQUIRE(m.isDef(b));
        REQUIRE(m.isDef(c));
        REQUIRE(m.isCons(c) == value_true);
        REQUIRE_FALSE(m.isDef(d));
        REQUIRE_FALSE(m.isDef(e));
        REQUIRE(m.isCons(d) == value_false);
        REQUIRE(m.isCons(e) == value_false);
    }

    SECTION("testIncrementalEnum") {
        config.solve.numModels = 0;
        config.solve.enumMode  = EnumOptions::enum_record;
        auto& asp              = libclasp.startAsp(config, true);
        lpAdd(asp, "{x1}.");
        libclasp.prepare();
        REQUIRE(libclasp.solve().sat());
        REQUIRE(libclasp.summary().numEnum == 2);
        REQUIRE(libclasp.update());
        lpAdd(asp, "{x2}.");
        libclasp.prepare();
        REQUIRE(libclasp.solve().sat());
        REQUIRE(libclasp.summary().numEnum == 4);
    }
    SECTION("testIncrementalCons") {
        config.solve.numModels = 0;
        config.solve.enumMode  = EnumOptions::enum_cautious;
        lpAdd(libclasp.startAsp(config, true), "{x1;x2;x3}.\n"
                                               "#output a : x1.\n"
                                               "#output b : x2.\n"
                                               "#output c : x3.\n");
        libclasp.prepare();
        REQUIRE(libclasp.solve().sat());
        update(config).solve.enumMode = EnumOptions::enum_brave;
        libclasp.update();
        libclasp.prepare();
        REQUIRE(libclasp.solve().sat());
        REQUIRE(libclasp.summary().numEnum > 1);
    }
    SECTION("testIncrementalMin") {
        config.solve.numModels = 0;
        config.solve.enumMode  = EnumOptions::enum_auto;
        lpAdd(libclasp.startAsp(config, true), "{x1;x2;x3}.\n"
                                               "#minimize{x1, x2, x3}.\n");
        libclasp.prepare();
        REQUIRE(libclasp.solve().sat());
        REQUIRE(libclasp.summary().numEnum < 8u);
        REQUIRE(libclasp.update());
        libclasp.ctx.removeMinimize();
        libclasp.prepare();
        REQUIRE(libclasp.solve().sat());
        REQUIRE(libclasp.summary().numEnum == 8);
    }
    SECTION("testIncrementalMinIgnore") {
        config.solve.optMode   = MinimizeMode::ignore;
        config.solve.numModels = 0;
        lpAdd(libclasp.startAsp(config, true), "{x1;x2}.\n"
                                               "#minimize{x1, x2}.\n");
        libclasp.prepare();
        REQUIRE(libclasp.solve().sat());
        REQUIRE(libclasp.summary().numEnum == 4u);
        update(config).solve.optMode = MinimizeMode::optimize;
        libclasp.update();
        libclasp.prepare();
        REQUIRE(libclasp.solve().sat());
        REQUIRE(libclasp.summary().numEnum == 1u);
    }
    SECTION("testIncrementalMinAdd") {
        config.solve.numModels = 0;
        config.solve.enumMode  = EnumOptions::enum_auto;
        auto& asp              = libclasp.startAsp(config, true);
        lpAdd(asp, "{x1;x2}.\n"
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
    SECTION("testUncoreUndoesAssumptions") {
        config.solve.numModels       = 0;
        config.solve.optMode         = MinimizeMode::enum_opt;
        config.addSolver(0).heuId    = +HeuristicType::domain;
        config.addSolver(0).opt.type = OptParams::type_usc;
        SECTION("test oll") { config.addSolver(0).opt.algo = OptParams::usc_oll; }
        SECTION("test one") { config.addSolver(0).opt.algo = OptParams::usc_one; }
        SECTION("test k") { config.addSolver(0).opt.algo = OptParams::usc_k; }
        auto& asp = libclasp.startAsp(config, true);
        lpAdd(asp, "{x1;x2;x3;x4;x5}.\n"
                   ":- x1, x2, x3.\n"
                   ":- x4, x5.\n"
                   ":- x4, not x5.\n"
                   "x5 :- not x4.\n"
                   "#minimize{not x1, not x2}.\n"
                   "#heuristic x4. [1,true]"
                   "#assume{x3}.\n");
        libclasp.prepare();
        struct EventObserver : EventHandler {
            EventObserver() : EventHandler(Event::verbosity_low) {}
            bool onModel(const Solver&, const Model&) override {
                ++models;
                return true;
            }
            bool onUnsat(const Solver&, const Model&) override {
                ++unsat;
                return true;
            }
            void onEvent(const Event& ev) override {
                if (event_cast<ClaspFacade::StepReady>(ev)) {
                    ++finished;
                }
                else {
                    ++other;
                }
            }
            unsigned models{0};
            unsigned unsat{0};
            unsigned finished{0};
            unsigned other{0};
        } solveHandler, contextHandler;
        CAPTURE(config.addSolver(0).opt.algo);
        libclasp.ctx.setEventHandler(&contextHandler);
        REQUIRE(libclasp.solve(&solveHandler).sat());
        REQUIRE(libclasp.summary().numOptimal == 2);
        CHECK(contextHandler.models == 3);
        CHECK(contextHandler.unsat == 1);
        CHECK(contextHandler.finished == 1);
        CHECK(contextHandler.other != 0);

        CHECK(solveHandler.models == 3);
        CHECK(solveHandler.unsat == 1);
        CHECK(solveHandler.finished == 1);
        CHECK(solveHandler.other == 0);
        libclasp.update();
        libclasp.ctx.addUnary(~asp.getLiteral(3));
        libclasp.ctx.addUnary(asp.getLiteral(5));
        libclasp.prepare();
        REQUIRE(libclasp.solve().sat());
        REQUIRE(libclasp.summary().hasCosts());
        REQUIRE(libclasp.summary().numOptimal == 1);
        REQUIRE(libclasp.summary().costs()[0] == 0);
    }

    SECTION("testUpdateConfig") {
        config.solve.numModels    = 0;
        config.solve.enumMode     = EnumOptions::enum_auto;
        config.addSolver(0).heuId = +HeuristicType::berkmin;
        lpAdd(libclasp.startAsp(config, true), "{x1;x2;x3}.");
        libclasp.prepare();
        REQUIRE(libclasp.solve().sat());
        update(config).addSolver(0).heuId = +HeuristicType::vsids;
        libclasp.update();
        libclasp.prepare();
        REQUIRE(libclasp.solve().sat());
        REQUIRE(dynamic_cast<ClaspVsids*>(libclasp.ctx.master()->heuristic()));
    }
    SECTION("testIncrementalProjectUpdate") {
        config.solve.numModels = 0;
        config.solve.enumMode  = EnumOptions::enum_auto;
        config.solve.project   = 1;
        auto& asp              = libclasp.startAsp(config, true);
        lpAdd(asp, "{x1;x2}. #output b : x2.");
        libclasp.prepare();
        const auto* modelEnum = static_cast<const ModelEnumerator*>(libclasp.enumerator());
        REQUIRE(modelEnum->project(asp.getLiteral(2).var()));
        REQUIRE(libclasp.solve().sat());
        REQUIRE(libclasp.summary().numEnum == 2);
        update(config).solve.project = 0;
        libclasp.update();
        libclasp.prepare();
        REQUIRE(libclasp.solve().sat());
        REQUIRE(libclasp.summary().numEnum == 4);
        update(config).solve.project = 1;
        libclasp.update();
        lpAdd(asp, "{x3;x4}. #output y : x4.");
        libclasp.prepare();
        modelEnum = static_cast<const ModelEnumerator*>(libclasp.enumerator());
        REQUIRE(modelEnum->project(asp.getLiteral(2).var()));
        REQUIRE(modelEnum->project(asp.getLiteral(4).var()));
        REQUIRE(libclasp.solve().sat());
        REQUIRE(uint64_t(4) == libclasp.summary().numEnum);
    }
    SECTION("testIncrementalDomRecUpdate") {
        config.solve.numModels                = 0;
        config.solve.enumMode                 = EnumOptions::enum_dom_record;
        config.addSolver(0).heuId             = +HeuristicType::domain;
        config.addSolver(0).heuristic.domMod  = HeuParams::mod_false;
        config.addSolver(0).heuristic.domPref = HeuParams::pref_show;
        lpAdd(libclasp.startAsp(config, true), "{x1;x2}.\n"
                                               ":- not x1, not x2.\n"
                                               "#output b : x2.\n"
                                               "#output a : x1.\n");
        REQUIRE(libclasp.solve().sat());
        // {a} ; {b}
        REQUIRE(libclasp.summary().numEnum == 2);

        update(config).addSolver(0).heuristic.domMod = HeuParams::mod_true;
        libclasp.update();
        REQUIRE(libclasp.solve().sat());
        // {a,b}
        REQUIRE(libclasp.summary().numEnum == 1);
    }
    SECTION("testIncrementalConfigUpdateBug") {
        config.asp.erMode = Asp::LogicProgram::mode_transform;
        auto& asp         = libclasp.startAsp(config, true);
        lpAdd(asp, "{x1;x2}.");
        libclasp.prepare();
        REQUIRE(libclasp.ctx.ok());
        REQUIRE(asp.stats.auxAtoms == 2);
        update(config).asp.erMode = Asp::LogicProgram::mode_native;
        libclasp.update();
        lpAdd(asp, "{x3;x4}.");
        libclasp.prepare();
        REQUIRE(asp.stats.auxAtoms == 0);
    }
    SECTION("with lookahead") {
        config.addSolver(0).lookType = +VarType::atom;
        lpAdd(libclasp.startAsp(config, true), "{x1;x2}.");
        libclasp.prepare();
        REQUIRE(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look));
        SECTION("incrementalLookaheadAddHeuristic") {
            auto* look                        = libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look);
            update(config).addSolver(0).heuId = +HeuristicType::unit;
            libclasp.update();
            libclasp.prepare();
            look = libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look);
            REQUIRE((look && look->next == nullptr));
        }
        SECTION("incrementalDisableLookahead") {
            update(config).addSolver(0).lookType = 0;
            libclasp.update();
            libclasp.prepare();
            REQUIRE(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look) == 0);
        }
        SECTION("incrementalChangeLookahead") {
            update(config).addSolver(0).lookType = +VarType::body;
            libclasp.update();
            libclasp.prepare();
            auto* look =
                static_cast<Lookahead*>(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look));
            REQUIRE((look && look->score.types == VarType::body));
        }
    }
    SECTION("testIncrementalExtendLookahead") {
        config.addSolver(0).lookType = +VarType::atom;
        config.addSolver(0).lookOps  = 3;
        auto& asp                    = libclasp.startAsp(config, true);
        lpAdd(asp, "{x1;x2}.");
        libclasp.prepare();
        REQUIRE(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look));
        update(config).addSolver(0).lookOps = 0;
        libclasp.update();
        lpAdd(asp, "{x3;x4}.");
        libclasp.prepare();
        auto* look = static_cast<Lookahead*>(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look));
        REQUIRE((look && look->next == nullptr));
        while (libclasp.ctx.master()->numFreeVars() != 0) {
            libclasp.ctx.master()->decideNextBranch();
            libclasp.ctx.master()->propagate();
            REQUIRE(libclasp.ctx.master()->getPost(PostPropagator::priority_reserved_look) == look);
        }
    }

    SECTION("testIncrementalRemoveSolver") {
        config.solve.numModels = 0;
        config.solve.setSolvers(4);
        auto& asp = libclasp.startAsp(config, true);
        lpAdd(asp, "{x1;x2;x4;x3}.\n"
                   ":- 3 {x1, x2, x3, x4}.\n");
        libclasp.prepare();
        REQUIRE(libclasp.solve().sat());
        REQUIRE(uint64_t(11) == libclasp.summary().numEnum);

        update(config).solve.setSolvers(1);
        libclasp.update();
        lpAdd(asp, ":- x1, x2.\n");
        libclasp.prepare();
        REQUIRE((libclasp.solve().sat() && libclasp.summary().numEnum == 10));

        update(config).solve.setSolvers(2);
        libclasp.update();
        libclasp.prepare();
        REQUIRE((libclasp.solve().sat() && libclasp.summary().numEnum == 10));
    }

    SECTION("testMinimizeTrivialUnsat") {
        config.solve.numModels = 0;
        lpAdd(libclasp.startAsp(config, true), "#minimize{x1}.\n"
                                               "{x1;x2}.\n"
                                               ":- x1, x2.\n"
                                               ":- x1, not x2.\n");
        libclasp.program()->endProgram();
        libclasp.ctx.addUnary(posLit(1));
        REQUIRE(libclasp.ctx.ok());
        REQUIRE(libclasp.ctx.hasMinimize());
        REQUIRE(libclasp.prepare());
        REQUIRE_FALSE(libclasp.ctx.ok());
        REQUIRE(libclasp.enumerator()->minimizer() == nullptr);
    }
    SECTION("testGenSolveTrivialUnsat") {
        config.solve.numModels = 0;
        lpAdd(libclasp.startAsp(config, true), "x1 :- not x1.");
        REQUIRE(libclasp.prepare());
        REQUIRE(libclasp.prepared());
        auto it = libclasp.solve(SolveMode::yield);
        REQUIRE(it.get().exhausted());
        REQUIRE_FALSE(it.model());
        REQUIRE(libclasp.step() == 0);

        it = libclasp.solve(SolveMode::yield);
        REQUIRE(it.get().exhausted());
        REQUIRE_FALSE(it.model());
        REQUIRE(libclasp.step() == 1);
    }

    SECTION("testProgramFrozenBug") {
        lpAdd(libclasp.startAsp(config, true), "{x1}.\n.");
        REQUIRE(libclasp.prepare());
        REQUIRE(libclasp.asp()->frozen());
        REQUIRE(libclasp.solve().sat());
        REQUIRE(libclasp.ctx.addUnary(posLit(1)));
        REQUIRE_FALSE(libclasp.ctx.addUnary(negLit(1)));
        REQUIRE(libclasp.ctx.frozen());
        libclasp.update();
        REQUIRE_FALSE(libclasp.ctx.frozen());
        REQUIRE(libclasp.asp()->frozen());

        libclasp.update();
        REQUIRE_FALSE(libclasp.ctx.frozen());
        REQUIRE(libclasp.asp()->frozen());
    }

    SECTION("testInterruptBeforeGenSolve") {
        config.solve.numModels = 0;
        lpAdd(libclasp.startAsp(config, true), "{x1}.");
        libclasp.prepare();
        libclasp.interrupt(2);
        auto it = libclasp.solve(SolveMode::yield);
        REQUIRE(it.get().interrupted());
        REQUIRE_FALSE(it.model());
    }
    SECTION("testGenSolveWithLimit") {
        lpAdd(libclasp.startAsp(config, true), "{x1;x2;x3}.");
        libclasp.prepare();
        for (auto i : irange(1, 9)) {
            auto got = 0, exp = i;
            update(config).solve.numModels = i % 8;
            libclasp.update();
            for (auto it = libclasp.solve(SolveMode::yield); it.next();) {
                REQUIRE(got != exp);
                ++got;
            }
            REQUIRE(exp == got);
        }
    }
    SECTION("testGenSolveStartUnsat") {
        lpAdd(libclasp.startAsp(config, true), "{x1, x2}.\n :- x1, x2.\n#assume{x1, x2}.");
        libclasp.prepare();
        auto it = libclasp.solve(SolveMode::yield);
        REQUIRE_FALSE(it.next());
    }

    SECTION("testCancelGenSolve") {
        config.solve.numModels = 0;
        lpAdd(libclasp.startAsp(config, true), "{x1}.");
        libclasp.prepare();
        unsigned mod = 0;
        auto     it  = libclasp.solve(SolveMode::yield);
        while (it.next()) {
            REQUIRE(it.model()->num == ++mod);
            it.cancel();
            break;
        }
        REQUIRE((not libclasp.solving() && not it.get().exhausted() && mod == 1));
        libclasp.update();
        libclasp.prepare();
        mod = 0;
        for (auto j = libclasp.solve(SolveMode::yield); j.next(); ++mod) { ; }
        REQUIRE((not libclasp.solving() && mod == 2));
    }
    SECTION("testGenDtorCancelsSolve") {
        lpAdd(libclasp.startAsp(config, true), "{x1}.");
        libclasp.prepare();
        { libclasp.solve(SolveMode::yield); }
        REQUIRE((not libclasp.solving() && not libclasp.result().exhausted()));
    }

    SECTION("with model handler") {
        std::string log;
        struct Handler : EventHandler {
            Handler(const char* n, std::string& l) : name(n), log(&l) {}
            std::string  name;
            std::string* log;
            bool         doThrow{false}, doStop{false};
            bool         onModel(const Solver&, const Model&) override {
                log->append(not log->empty(), ' ').append(name);
                if (doThrow) {
                    throw std::runtime_error("Model");
                }
                return doStop == false;
            }
        } h1("ctx", log), h2("solve", log);
        config.solve.numModels = 0;
        lpAdd(libclasp.startAsp(config, true), "{x1}.");
        libclasp.prepare();
        SECTION("simple") {
            h1.doStop = true;
            libclasp.ctx.setEventHandler(&h1);
            REQUIRE(libclasp.solve().sat());
            REQUIRE(log == "ctx");
        }
        SECTION("genStopFromHandler") {
            h1.doStop = true;
            libclasp.ctx.setEventHandler(&h1);
            int mod = 0;
            for (auto g = libclasp.solve(SolveMode::yield, LitVec(), &h2); g.next(); ++mod) { log.append(" yield"); }
            REQUIRE(mod == 1);
            REQUIRE(log == "solve ctx yield");
        }
        SECTION("syncThrowOnModel") {
            h2.doThrow = true;
            libclasp.ctx.setEventHandler(&h1);
            auto g = libclasp.solve(SolveMode::yield, LitVec(), &h2);
            REQUIRE_THROWS_AS(g.model(), std::runtime_error);
            REQUIRE_FALSE(g.running());
            REQUIRE_FALSE(libclasp.solving());
            REQUIRE_THROWS_AS(g.get(), std::runtime_error);
            REQUIRE(log == "solve");
        }
    }
    SECTION("testDisposeProgram") {
        config.solve.numModels = 0;
        auto& asp              = libclasp.startAsp(config, false);
        lpAdd(asp, "{x1;x2;x3}.\n"
                   "x4 :- 1 {x1, x2, x3}.\n"
                   "x5 :- x1, not x2, x3.\n");
        SECTION("removedByDefault") {
            libclasp.prepare();
            REQUIRE(libclasp.program() == 0);
            CHECK(not libclasp.incremental());
        }
        SECTION("kept") {
            SECTION("IfRequested") {
                libclasp.keepProgram();
                libclasp.prepare();
                CHECK(not libclasp.incremental());
            }
            SECTION("IfIncremental") {
                libclasp.enableProgramUpdates();
                libclasp.prepare();
                CHECK(libclasp.incremental());
            }
            REQUIRE(libclasp.asp() == &asp);
            CHECK(asp.getLiteral(1) == posLit(1));
            CHECK(asp.getLiteral(2) == posLit(2));
            CHECK(asp.getLiteral(3) == posLit(3));
            CHECK(asp.getLiteral(4).var() > posLit(3).var());
        }
        REQUIRE(libclasp.solve().sat());
        REQUIRE(libclasp.summary().numEnum == 8);
    }

    SECTION("testIssue104") {
        config.solve.numModels = 1;
        config.parse.enableAssume();
        config.satPre.type = SatPreParams::sat_pre_full;
        std::stringstream prg;
        prg << "p cnf 3 0\n";
        prg << "c assume 1 -2 3\n";
        SECTION("no clause") {
            libclasp.start(config, prg);
            CHECK(libclasp.read());
            CHECK(libclasp.solve().sat());
            CHECK(libclasp.summary().numEnum == 1);
        }
        SECTION("one clause") {
            prg << "1 2 3 0\n";
            libclasp.start(config, prg);
            CHECK(libclasp.read());
            CHECK(libclasp.solve().sat());
            CHECK(libclasp.summary().numEnum == 1);
        }
    }
}

TEST_CASE("Regressions", "[facade][regression]") {
    ClaspConfig config;
    ClaspFacade libclasp;

    SECTION("disjunctive shifting") {
        config.solve.numModels = 0;
        auto& asp              = libclasp.startAsp(config);
        lpAdd(asp, "x52 :- x2.\n"
                   "x2 :- x19.\n"
                   "x2 :- x16.\n"
                   "x6 :- x15.\n"
                   "x6 :- x14.\n"
                   "x6 :- x13.\n"
                   "x6 :- x12.\n"
                   "x19 :- x54.\n"
                   "x13 :- x60.\n"
                   "x12 :- x61.\n"
                   "x16 :- x52.\n"
                   "x12 | x13 | x14 | x15 | x16 | x19.\n"
                   "x54 :- x2.\n"
                   "x60 :- x6.\n"
                   "x61 :- x6.\n");
        libclasp.prepare();
        REQUIRE(libclasp.solve().sat());
        REQUIRE(libclasp.summary().numEnum == 2);
    }

    SECTION("issue 91 - 1") {
        config.solve.numModels = 0;
        auto& asp              = libclasp.startAsp(config);
        lpAdd(asp, "x1 | x2.\n"
                   "x3 | x4 | x5 | x6 | x7 :- x1.\n"
                   "x1 :- x6.\n"
                   "x1 :- x7.\n");
        libclasp.prepare();
        REQUIRE(libclasp.solve().sat());
        REQUIRE(libclasp.summary().numEnum == 6);
    }

    SECTION("issue 91 - 2") {
        config.solve.numModels = 0;
        auto& asp              = libclasp.startAsp(config);
        lpAdd(asp, "a :- b.\n"
                   "b :- a.\n"
                   "c :- d.\n"
                   "d :- c.\n"
                   "f :- g.\n"
                   "g :- f.\n"
                   "c | x.\n"
                   "a | b | f | g | c | d.\n");
        libclasp.prepare();
        REQUIRE(libclasp.solve().sat());
        REQUIRE(libclasp.summary().numEnum == 3);
    }

    SECTION("issue 91 - assertion") {
        config.solve.numModels = 0;
        auto& asp              = libclasp.startAsp(config);
        lpAdd(asp, "a :- b.\n"
                   "b :- a.\n"
                   "f :- g.\n"
                   "g :- f.\n"
                   "b | a | g | f | c | e.\n"
                   "b | c | d.\n"
                   "b | h | e | i :-c.\n"
                   "b | a | c | d :-e.\n"
                   ":- d, e.\n");
        libclasp.prepare();
        REQUIRE(libclasp.summary().lpStats()->gammas == 8);
        REQUIRE(libclasp.solve().sat());
        REQUIRE(libclasp.summary().numEnum == 5);
    }
}

TEST_CASE("WBO-Soft-Eq-Bug", "[facade]") {
    ClaspConfig       config;
    ClaspFacade       libclasp;
    std::stringstream prg;
    config.solve.numModels = 0;
    config.solve.optMode   = MinimizeMode::enum_opt;
    SECTION("one unsat constraint - eight solutions") {
        prg << "* #variable= 3 #constraint= 0 #soft= 1 mincost= 2 maxcost= 2 sumcost= 2\n"
               "soft: 3 ;\n"
               "[2] +1 x1 +1 x2 +1 x3 = 4 ;\n";
        libclasp.start(config, prg);
        REQUIRE(libclasp.read());
        REQUIRE(libclasp.solve().sat());
        REQUIRE(libclasp.summary().numOptimal == 8);
        REQUIRE(libclasp.summary().costs().front() == 2);
    }
    SECTION("one solution") {
        prg << "* #variable= 3 #constraint= 0 #soft= 1 mincost= 2 maxcost= 2 sumcost= 2\n"
               "soft: 3 ;\n"
               "[2] +1 x1 +1 x2 +1 x3 = 0;\n";
        libclasp.start(config, prg);
        REQUIRE(libclasp.read());
        REQUIRE(libclasp.solve().sat());
        REQUIRE(libclasp.summary().numOptimal == 1);
        REQUIRE(libclasp.summary().costs().front() == 0);
    }
    SECTION("one solution mixed") {
        prg << "* #variable= 3 #constraint= 0 #soft= 3 mincost= 2 maxcost= 3 sumcost= 8"
               "soft: 6 ;"
               "[2] +1 x1 +1 x2 +1 x3 = 1 ;"
               "[3] -1 x1 -1 x2 -1 x3 = 2 ;"
               "[3] +1 x1 +1 x2 +1 x3 = 0 ;";
        libclasp.start(config, prg);
        REQUIRE(libclasp.read());
        REQUIRE(libclasp.solve().sat());
        REQUIRE(libclasp.summary().numOptimal == 1);
        REQUIRE(libclasp.summary().costs().front() == 5);
    }
    SECTION("three solutions") {
        prg << "* #variable= 3 #constraint= 0 #soft= 1 mincost= 2 maxcost= 2 sumcost= 2"
               "soft: 3;"
               "[2] +1 x1 +1 x2 +1 x3 = 1 ;";
        libclasp.start(config, prg);
        REQUIRE(libclasp.read());
        REQUIRE(libclasp.solve().sat());
        REQUIRE(libclasp.summary().numOptimal == 3);
        REQUIRE(libclasp.summary().costs().front() == 0);
    }
    SECTION("two constraints - three solutions") {
        prg << "* #variable= 3 #constraint= 0 #soft= 2 mincost= 2 maxcost= 3 sumcost= 5"
               "soft: 4;"
               "[2] +1 x1 +1 x2 +1 x3 = 1 ;"
               "[3] +1 x1 +1 x2 +1 x3 = 2 ;";
        libclasp.start(config, prg);
        REQUIRE(libclasp.read());
        REQUIRE(libclasp.solve().sat());
        REQUIRE(libclasp.summary().numOptimal == 3);
        REQUIRE(libclasp.summary().costs().front() == 2);
    }
    SECTION("two constraints - seven solutions") {
        prg << "* #variable= 3 #constraint= 0 #soft= 2 mincost= 2 maxcost= 3 sumcost= 5"
               "soft: 4;"
               "[2] +1 x1 +1 x2 +1 x3 = 0;"
               "[3] +1 x1 +1 x2 +1 x3 >= 1 ;";
        libclasp.start(config, prg);
        REQUIRE(libclasp.read());
        REQUIRE(libclasp.solve().sat());
        REQUIRE(libclasp.summary().numOptimal == 7);
        REQUIRE(libclasp.summary().costs().front() == 2);
    }
}

TEST_CASE("Incremental solving", "[facade]") {
    ClaspConfig config;
    ClaspFacade libclasp;
    using Result = ClaspFacade::Result;
    Result::Res stop{}, done;
    int         maxS = -1, minS = -1, expS = 0;
    libclasp.ctx.enableStats(2);
    config.asp.noEq();
    Asp::LogicProgram& asp   = libclasp.startAsp(config, true);
    const char*        prg[] = {// step 0
                         "x1 :- x2.\n"
                                "x2 :- x1.\n"
                                "x1 :- x3.\n"
                                ":- not x1.\n"
                                "#external x3.", // step 1
                         "x3 :- x4.\n"
                                "x4 :- x3.\n"
                                "x4 :- x5.\n"
                                "#external x5.", // step 2
                         "x5 :- x6, x7.\n"
                                "x6 :- not x3.\n"
                                "x7 :- not x1, not x2.\n"
                                "{x5}.", // step 3
                         "{x8}."};
    SECTION("test stop on sat - no limit") {
        stop = done = Result::res_sat;
        expS        = 2;
    }
    SECTION("test stop on unsat - no limit") { stop = done = Result::res_unsat; }
    SECTION("test stop on sat - with max step") {
        stop = Result::res_sat;
        done = Result::res_unsat;
        maxS = 2;
        expS = 1;
    }
    SECTION("test stop on sat - with min step") {
        stop = Result::res_sat;
        done = Result::res_sat;
        minS = 4;
        expS = 3;
    }
    auto res = Result::res_unknown;
    do {
        libclasp.update();
        REQUIRE(std::size_t(libclasp.step()) < (sizeof(prg) / sizeof(const char*)));
        lpAdd(asp, prg[libclasp.step()]);
        libclasp.prepare();
        res = libclasp.solve();
        if (res == Result::res_unsat) {
            int              expCore = libclasp.step() == 0 ? -3 : -5;
            Potassco::LitVec prgCore;
            auto             core = libclasp.summary().unsatCore();
            CHECK(asp.translateCore(core, prgCore));
            CHECK(prgCore.size() == 1);
            CHECK(prgCore[0] == expCore);
        }
    } while (--maxS && ((minS > 0 && --minS) || res != stop));
    REQUIRE(done == libclasp.result());
    REQUIRE(expS == libclasp.step());
}

namespace {
class TestPropagator : public Potassco::AbstractPropagator {
public:
    using Assignment = Potassco::AbstractAssignment;
    using InitCb     = std::function<void(const Assignment&, Init&)>;
    using AttachCb   = std::function<void(const Assignment&, Control&)>;
    using PropCb     = std::function<void(const Assignment&, Control&, ChangeList)>;
    using CheckCb    = std::function<void(const Assignment&, Control&)>;
    using UndoCb     = std::function<void(const Assignment&, ChangeList)>;
    TestPropagator() = default;
    void init(const Assignment& assignment, Init& propInit) override {
        ++inits;
        if (onInit) {
            onInit(assignment, propInit);
        }
        for (auto lit : initWatches) { propInit.addWatch(encodeLit(lit)); }
        if (clearInitWatches) {
            initWatches.clear();
        }
    }
    void attach(const Assignment& assignment, Control& ctl) override {
        if (onAttach) {
            onAttach(assignment, ctl);
        }
    }
    void propagate(const Assignment& assignment, Control& ctl, ChangeList changes) override {
        if (onPropagate) {
            onPropagate(assignment, ctl, changes);
        }
        addClause(assignment, ctl);
    }
    void undo(const Assignment& assignment, ChangeList changes) override {
        ++undos;
        if (onUndo) {
            onUndo(assignment, changes);
        }
    }
    void check(const Assignment& assignment, Control& ctl) override {
        if (onCheck) {
            onCheck(assignment, ctl);
        }
        for (int lit : clause) {
            if (assignment.isTrue(lit)) {
                return;
            }
        }
        if (not clause.empty()) {
            std::ignore = ctl.addClause(clause);
        }
    }
    bool addClause(const Assignment& assignment, Control& ctl) {
        if (not assignment.isTrue(encodeLit(fire))) {
            return true;
        }
        return ctl.addClause(clause, clProp) && ctl.propagate();
    }
    void                 addToClause(Literal x) { clause.push_back(encodeLit(x)); }
    InitCb               onInit;
    AttachCb             onAttach;
    PropCb               onPropagate;
    CheckCb              onCheck;
    UndoCb               onUndo;
    LitVec               initWatches;
    Literal              fire{lit_false};
    Potassco::LitVec     clause;
    Potassco::ClauseType clProp{Potassco::ClauseType::learnt};
    bool                 clearInitWatches{false};
    uint32_t             undos{0};
    uint32_t             inits{0};
};
using PropagatorInit    = Potassco::AbstractPropagator::Init;
using PropagatorControl = Potassco::AbstractPropagator::Control;

struct PropagatorTest {
    void addVars(unsigned num) {
        vars.resize(num + 1);
        vars[0] = 0;
        for (auto& v : drop(vars, 1u)) { v = ctx.addVar(VarType::atom); }
        ctx.startAddConstraints();
    }
    [[nodiscard]] bool isFrozen(Var_t v) const { return ctx.varInfo(v).frozen(); }
    [[nodiscard]] bool isFrozen(Literal l) const { return isFrozen(l.var()); }
    SharedContext      ctx;
    VarVec             vars;
};

} // namespace

#if CLASP_HAS_THREADS

TEST_CASE("Facade mt", "[facade][mt]") {
    struct EventVar {
        EventVar() = default;
        void fire() {
            {
                Clasp::mt::unique_lock lock(mutex);
                fired = true;
            }
            cond.notify_all();
        }
        void wait() {
            for (Clasp::mt::unique_lock lock(mutex); not fired;) { cond.wait(lock); }
        }
        Clasp::mt::mutex              mutex;
        Clasp::mt::condition_variable cond;
        bool                          fired{false};
    };

    struct ModelHandler : EventHandler {
        ModelHandler(const char* n, std::string& l, bool r = true) : name(n), log(&l), ret(r) {}

        bool onModel(const Solver&, const Model&) override {
            log->append(not log->empty(), ' ').append(name);
            return ret;
        }
        void onEvent(const Event& ev) override {
            if (const auto* start = event_cast<ClaspFacade::StepStart>(ev); start) {
                REQUIRE(start->facade);
                REQUIRE(start->facade->solving());
                REQUIRE_FALSE(start->facade->solved());
            }
            else if (const auto* ready = event_cast<ClaspFacade::StepReady>(ev); ready) {
                REQUIRE(ready->summary);
                REQUIRE_FALSE(ready->summary->facade->solving());
                REQUIRE(ready->summary->facade->solved());
            }
        }
        std::string  name;
        std::string* log;
        bool         ret;
    };

    ClaspConfig config;
    ClaspFacade libclasp;
    using AsyncResult = ClaspFacade::SolveHandle;
    SECTION("testIncrementalAddSolver") {
        auto& asp = libclasp.startAsp(config, true);
        lpAdd(asp, "{x1;x2}.");
        libclasp.prepare();
        REQUIRE_FALSE(isSentinel(libclasp.ctx.stepLiteral()));
        update(config).solve.setSolvers(2);
        libclasp.update();
        lpAdd(asp, "{x3;x4}.");
        libclasp.prepare();
        REQUIRE((libclasp.ctx.concurrency() == 2 && libclasp.ctx.hasSolver(1)));
    }
    SECTION("testClingoSolverStatsRemainValid") {
        config.stats                   = 2;
        config.solve.algorithm.threads = 2;
        config.solve.numModels         = 0;
        auto& asp                      = libclasp.startAsp(config, true);
        lpAdd(asp, "{x1,x2,x3}.");
        libclasp.prepare();
        libclasp.solve();
        auto* stats     = libclasp.getStats();
        auto  s         = stats->get(stats->root(), "solving.solver");
        auto  s1        = stats->at(s, 1);
        auto  s1Choices = stats->get(stats->at(s, 1), "choices");
        auto  s0Choices = stats->get(stats->at(s, 0), "choices");
        REQUIRE(stats->size(s) == 2);
        REQUIRE(stats->value(s1Choices) + stats->value(s0Choices) ==
                stats->value(stats->get(stats->root(), "solving.solvers.choices")));
        update(config).solve.algorithm.threads = 1;
        libclasp.update();
        libclasp.solve();
        INFO("solver stats are not removed");
        REQUIRE(stats->size(s) == 2);
        INFO("solver stats remain valid");
        REQUIRE(stats->at(s, 1) == s1);
        REQUIRE(stats->value(s1Choices) == 0.0);
        REQUIRE(stats->value(s0Choices) == stats->value(stats->get(stats->root(), "solving.solvers.choices")));
        update(config).solve.algorithm.threads = 2;
        libclasp.update();
        libclasp.solve();
        REQUIRE(stats->value(s1Choices) + stats->value(s0Choices) ==
                stats->value(stats->get(stats->root(), "solving.solvers.choices")));
    }
    SECTION("testShareModeRegression") {
        config.shareMode               = ContextParams::share_auto;
        config.solve.algorithm.threads = 2;
        libclasp.startSat(config).prepareProblem(2);
        libclasp.prepare();
        REQUIRE(libclasp.ctx.physicalShare(ConstraintType::static_));
        REQUIRE(libclasp.ctx.physicalShare(ConstraintType::conflict));
    }
    SECTION("testAsyncSolveTrivialUnsat") {
        config.solve.numModels = 0;
        lpAdd(libclasp.startAsp(config, true), "x1 :- not x1.");
        libclasp.prepare();
        AsyncResult it = libclasp.solve(SolveMode::async | SolveMode::yield);
        REQUIRE(it.get().unsat());
    }
    SECTION("testSolveWinnerMt") {
        struct Blocker : PostPropagator {
            explicit Blocker(EventVar& ev) : eventVar(&ev) {}
            [[nodiscard]] uint32_t priority() const override { return priority_reserved_ufs; }
            bool                   propagateFixpoint(Solver&, PostPropagator*) override { return true; }
            bool                   isModel(Solver&) override {
                eventVar->wait();
                return true;
            }
            EventVar* eventVar;
        };
        struct Unblocker : EventHandler {
            explicit Unblocker(EventVar& ev) : eventVar(&ev) {}
            bool onModel(const Solver&, const Model&) override {
                eventVar->fire();
                return false;
            }
            EventVar* eventVar;
        };
        config.solve.numModels         = 0;
        config.solve.enumMode          = EnumOptions::enum_record;
        config.solve.algorithm.threads = 4;
        lpAdd(libclasp.startAsp(config, true), "{x1;x2;x3;x4}.");
        EventVar eventVar;
        libclasp.prepare();
        uint32_t expectedWinner = 0;
        SECTION("Solver 3") { expectedWinner = 3; }
        SECTION("Solver 1") { expectedWinner = 1; }
        SECTION("Solver 2") { expectedWinner = 2; }
        SECTION("Solver 0") { expectedWinner = 0; }
        for (auto i : irange(libclasp.ctx.concurrency())) {
            if (i != expectedWinner) {
                libclasp.ctx.solver(i)->addPost(new Blocker(eventVar));
            }
        }
        Unblocker   unblocker(eventVar);
        AsyncResult result = libclasp.solve(SolveMode::async, LitVec(), &unblocker);
        uint32_t    winner = result.waitFor(5.0) ? libclasp.ctx.winner() : (eventVar.fire(), result.wait(), 0xFEE1DEAD);
        REQUIRE(winner == expectedWinner);
    }
    SECTION("testInterruptBeforeSolve") {
        config.solve.numModels = 0;
        lpAdd(libclasp.startAsp(config, true), "{x1}.");
        libclasp.prepare();
        libclasp.interrupt(2);
        AsyncResult it = libclasp.solve(SolveMode::async_yield);
        REQUIRE(it.get().interrupted());
    }
    SECTION("testCancelAsyncOperation") {
        config.solve.numModels = 0;
        lpAdd(libclasp.startAsp(config, true), "{x1}.");
        libclasp.prepare();
        AsyncResult it = libclasp.solve(SolveMode::async_yield);
        while (it.model()) { it.cancel(); }
        REQUIRE(uint64_t(1) == libclasp.summary().numEnum);
        REQUIRE((not libclasp.solving() && it.interrupted()));
        libclasp.update();
        libclasp.prepare();

        std::string  log;
        ModelHandler eh1("ctx", log);
        ModelHandler eh2("solve", log);

        libclasp.ctx.setEventHandler(&eh1);
        it      = libclasp.solve(SolveMode::async_yield, {}, &eh2);
        int mod = 0;

        while (it.model()) {
            log.append(" yield");
            ++mod;
            it.resume();
        }
        REQUIRE((not libclasp.solving() && mod == 2));
        REQUIRE(log == "solve ctx yield solve ctx yield");
    }
    SECTION("testAsyncResultDtorCancelsOp") {
        lpAdd(libclasp.startAsp(config, true), "{x1}.");
        libclasp.prepare();
        { AsyncResult it = libclasp.solve(SolveMode::async_yield); }
        REQUIRE((not libclasp.solving() && libclasp.result().interrupted()));
    }

    SECTION("testDestroyAsyncResultNoFacade") {
        {
            auto* localLib = new ClaspFacade();
            lpAdd(localLib->startAsp(config, true), "{x1}.");
            localLib->prepare();
            AsyncResult res(localLib->solve(SolveMode::async_yield));
            delete localLib;
            REQUIRE(res.interrupted());
        }
    }
    SECTION("testDestroyDanglingAsyncResult") {
        AsyncResult* handle = nullptr;
        lpAdd(libclasp.startAsp(config, true), "{x1}.");
        libclasp.prepare();
        handle = new AsyncResult(libclasp.solve(SolveMode::async));
        handle->wait();
        libclasp.update();
        libclasp.prepare();
        auto* it = new AsyncResult(libclasp.solve(SolveMode::async_yield));
        delete handle;
        REQUIRE((not it->interrupted() && libclasp.solving()));
        REQUIRE_NOTHROW(delete it);
        REQUIRE_FALSE(libclasp.solving());
    }
    SECTION("testCancelDanglingAsyncOperation") {
        lpAdd(libclasp.startAsp(config, true), "{x1}.");
        libclasp.prepare();
        AsyncResult step0 = libclasp.solve(SolveMode::async);
        step0.wait();
        libclasp.update();
        libclasp.prepare();
        AsyncResult step1 = libclasp.solve(SolveMode::async_yield);

        step0.cancel();
        REQUIRE(libclasp.solving());
        step1.cancel();
        REQUIRE_FALSE(libclasp.solving());
    }
    SECTION("testGenSolveMt") {
        config.solve.numModels         = 0;
        config.solve.algorithm.threads = 2;
        lpAdd(libclasp.startAsp(config, true), "{x1}.");
        libclasp.prepare();
        int          mod = 0;
        std::string  log;
        ModelHandler eh1("ctx", log);
        ModelHandler eh2("solve", log);

        libclasp.ctx.setEventHandler(&eh1);
        for (auto it = libclasp.solve(SolveMode::yield, {}, &eh2); it.next(); ++mod) {
            log.append(" yield");
            REQUIRE(libclasp.solving());
            REQUIRE_FALSE(libclasp.solved());
        }
        REQUIRE((not libclasp.solving() && mod == 2));
        REQUIRE(libclasp.solved());
        REQUIRE(log == "solve ctx yield solve ctx yield");
    }
    SECTION("test async throw") {
        struct Handler : EventHandler {
            Handler() = default;
            bool throwModel{false}, throwFinish{false};
            bool onModel(const Solver&, const Model&) override {
                if (throwModel) {
                    throw std::runtime_error("Model");
                }
                return true;
            }
            void onEvent(const Event& ev) override {
                if (event_cast<ClaspFacade::StepReady>(ev) && throwFinish) {
                    throw std::runtime_error("Finish");
                }
            }
        } h;
        lpAdd(libclasp.startAsp(config, true), "{x1}.");
        libclasp.prepare();
        SECTION("on model") {
            h.throwModel      = true;
            AsyncResult step0 = libclasp.solve(SolveMode::async, LitVec(), &h);
            step0.wait();
            REQUIRE(step0.error());
            REQUIRE_THROWS_AS(step0.get(), std::runtime_error);
        }
        SECTION("on finish") {
            h.throwFinish     = true;
            AsyncResult step0 = libclasp.solve(SolveMode::async, LitVec(), &h);
            step0.wait();
            REQUIRE(step0.error());
            REQUIRE_THROWS_AS(step0.get(), std::runtime_error);
        }
    }
    SECTION("test mt exception handling") {
        EventVar ev;
        config.solve.numModels = 0;
        config.solve.setSolvers(2);
        lpAdd(libclasp.startAsp(config, true), "{x1;x2}.");
        libclasp.prepare();
        SECTION("throwOnModel") {
            struct Blocker : public PostPropagator {
                explicit Blocker(EventVar& e) : ev(&e) {}
                [[nodiscard]] uint32_t priority() const override { return priority_reserved_ufs + 10; }
                bool                   propagateFixpoint(Solver& s, PostPropagator* ctx) override {
                    if (not ctx && s.numFreeVars() == 0) {
                        ev->wait();
                    }
                    return true;
                }
                EventVar* ev;
            };
            libclasp.ctx.master()->addPost(new Blocker(ev));
            struct ModelError : std::exception {};
            struct Handler : EventHandler {
                bool onModel(const Solver& s, const Model&) override {
                    if (&s != s.sharedContext()->master()) {
                        ev->fire();
                        throw ModelError{};
                    }
                    return false;
                }
                EventVar* ev = nullptr;
            } h;
            h.ev = &ev;
            REQUIRE_THROWS_AS(libclasp.solve(SolveMode::def, LitVec(), &h), ModelError);
        }
        SECTION("throw on propagate") {
            struct Blocker : PostPropagator {
                enum ErrorType { none, alloc, logic };
                explicit Blocker(EventVar& e, ErrorType t) : ev(&e), et(t) {}
                [[nodiscard]] uint32_t priority() const override { return priority_reserved_ufs + 10; }
                bool                   propagateFixpoint(Solver& s, PostPropagator*) override {
                    if (et == none) {
                        ev->wait();
                        s.removePost(this);
                        delete this;
                    }
                    else {
                        ev->fire();
                        if (et == alloc) {
                            throw std::bad_alloc();
                        }
                        throw std::domain_error("Something happened");
                    }
                    return true;
                }
                EventVar* ev;
                ErrorType et;
            };
            libclasp.ctx.master()->addPost(new Blocker(ev, Blocker::none));
            SECTION("allocFailContinue") {
                libclasp.ctx.solver(1)->addPost(new Blocker(ev, Blocker::alloc));
                REQUIRE_NOTHROW(libclasp.solve());
                REQUIRE(libclasp.summary().numEnum == 4);
            }
            SECTION("logicFailStop") {
                libclasp.ctx.solver(1)->addPost(new Blocker(ev, Blocker::logic));
                REQUIRE_THROWS_AS(libclasp.solve(), std::domain_error);
            }
        }
    }
    SECTION("Parallel solve calls clingo total check twice if necessary") {
        TestPropagator prop;
        config.solve.numModels = 0;
        config.solve.enumMode  = EnumOptions::enum_record;
        config.solve.setSolvers(2);
        config.addSolver(0).signDef = SolverStrategies::sign_pos; // assume x1  -> bound = 1
        config.addSolver(1).signDef = SolverStrategies::sign_neg; // assume ~x1 -> bound = 0
        struct Handler : EventHandler {
            Handler() = default;
            bool onModel(const Solver&, const Model&) override {
                waitFor0.fired = false; // ensure that we wait again on next propagate and
                waitFor1.fire();        // wake up Solver 0
                return true;
            }
            EventVar waitFor0, waitFor1;
        } h;
        std::mutex m;
        int        bound{2};
        auto&      asp = libclasp.startAsp(config, true);
        libclasp.registerPropagator(prop, false);
        lpAdd(asp, "{x1}.");
        Potassco::Lit_t lit{0};
        prop.onInit = [&](const auto&, PropagatorInit& init) {
            lit = init.solverLiteral(1);
            init.addWatch(lit);
            init.addWatch(-lit);
            CHECK(init.numSolver() == 2);
        };
        prop.onPropagate = [&](const auto& assignment, const PropagatorControl&, auto) {
            if (assignment.solverId() == 1) {
                h.waitFor0.wait(); // wait until Solver 0 has found its first total assignment
            }
        };
        prop.onCheck = [&](const auto& assignment, PropagatorControl& ctl) {
            // Solver 0 enters first with |vec| = 1 < bound but then waits for Solver 1
            // Solver 1 enters with |vec| = 0 and notifies Solver 0 once the model is committed
            // Solver 0 is forced to enter check() again with |vec| = 1 and discards this now worse assignment
            Potassco::LitVec vec;
            if (assignment.isTrue(lit)) {
                vec.push_back(-lit);
            }

            std::unique_lock lock(m);
            if (std::cmp_less(vec.size(), bound)) {
                bound = static_cast<int>(vec.size());
            }
            else {
                std::ignore = ctl.addClause(vec);
            }
            lock.unlock();
            if (assignment.solverId() == 0) {
                h.waitFor0.fire(); // let Solver 1 continue
                h.waitFor1.wait(); // wait for Solver 1 to commit its model
            }
        };
        libclasp.solve(&h);
        REQUIRE(libclasp.summary().numEnum == 1);
    }
}

#endif

static void getStatsKeys(const Potassco::AbstractStatistics& stats, Potassco::AbstractStatistics::Key_t k,
                         std::vector<std::string>& out, const std::string& p) {
    if (stats.type(k) == StatsType::map) {
        for (auto i : irange(toU32(stats.size(k)))) {
            auto sk = std::string{stats.key(k, i)};
            getStatsKeys(stats, stats.get(k, sk), out, p.empty() ? sk : std::string(p).append(".").append(sk));
        }
    }
    else if (stats.type(k) == StatsType::array) {
        for (auto i : irange(toU32(stats.size(k)))) {
            getStatsKeys(stats, stats.at(k, i), out, std::string(p).append(".").append(std::to_string(i)));
        }
    }
    else {
        out.push_back(p);
    }
}

TEST_CASE("Facade statistics", "[facade]") {
    ClaspConfig config;
    ClaspFacade libclasp;
    const auto  solveCosts = [&](uint32_t pos) -> double {
        auto costs = libclasp.summary().costs();
        return pos < costs.size() ? static_cast<double>(costs[pos]) : throw std::out_of_range("invalid cost position");
    };
    config.stats           = 2;
    config.solve.numModels = 0;
    SECTION("testStatsObject") {
        StatisticObject object;
        REQUIRE(object.toRep() == 0);
        REQUIRE(object.type() == StatsType::value);
        REQUIRE(object.value() == 0.0);
        REQUIRE(object.typeId() == 0);
        double x = 32.0;
        object   = StatisticObject::value(&x);
        REQUIRE(object.toRep() != 0);
        REQUIRE(object.type() == StatsType::value);
        REQUIRE(object.value() == 32.0);
        REQUIRE(object.typeId() != 0);
        object     = StatisticObject();
        auto other = StatisticObject::fromRep(object.toRep());
        REQUIRE(other.type() == StatsType::value);
    }
    SECTION("testClingoStats") {
        auto& asp = libclasp.startAsp(config, true);
        lpAdd(asp, "{x1;x2;x3}. x4. #minimize{x1, x2, x4}.");
        libclasp.prepare();
        libclasp.solve();
        auto* stats = libclasp.getStats();
        auto  r     = stats->root();
        REQUIRE(stats->type(r) == StatsType::map);
        REQUIRE(stats->writable(r) == true);
        auto lp = stats->get(r, "problem.lp");
        REQUIRE(stats->writable(lp) == false);

        auto s = stats->get(r, "solving");
        auto m = stats->get(r, "summary.models");
        REQUIRE(stats->type(lp) == StatsType::map);
        REQUIRE(stats->value(stats->get(lp, "rules")) == double(asp.stats.rules[0].sum()));
        REQUIRE(stats->value(stats->get(m, "enumerated")) == double(libclasp.summary().numEnum));
        auto solvers = stats->get(s, "solvers");
        REQUIRE(stats->value(stats->get(solvers, "choices")) == double(libclasp.ctx.master()->stats.choices));
        auto costs = stats->get(r, "summary.costs");
        REQUIRE(stats->type(costs) == StatsType::array);
        REQUIRE(stats->value(stats->at(costs, 0)) == solveCosts(0));

        auto lower = stats->get(r, "summary.lower");
        REQUIRE(stats->type(lower) == StatsType::array);
        REQUIRE(stats->size(lower) == 1);
        REQUIRE(stats->value(stats->at(lower, 0)) ==
                libclasp.enumerator()->minimizer()->lower(0) + libclasp.enumerator()->minimizer()->adjust(0));

        auto solver = stats->get(s, "solver");
        REQUIRE(stats->type(solver) == StatsType::array);
        auto s0 = stats->at(solver, 0);
        REQUIRE(stats->type(s0) == StatsType::map);
        REQUIRE(stats->value(stats->get(s0, "choices")) == double(libclasp.ctx.master()->stats.choices));
        std::vector<std::string> keys;
        getStatsKeys(*stats, r, keys, "");
        REQUIRE_FALSE(keys.empty());
        for (const auto& key : keys) {
            decltype(r) result;
            REQUIRE(stats->find(r, key, &result));
            REQUIRE(result == stats->get(r, key));
            REQUIRE(stats->type(result) == StatsType::value);
        }
        REQUIRE(keys.size() == 242);

        decltype(r) result;
        REQUIRE(stats->find(r, "problem.lp", &result));
        REQUIRE(result == lp);
        REQUIRE_FALSE(stats->find(lp, "foo", nullptr));
        REQUIRE(stats->find(lp, "rules", &result));
    }
    SECTION("testClingoStatsKeyIntegrity") {
        config.addTesterConfig()->stats = 2;
        auto& asp                       = libclasp.startAsp(config, true);
        lpAdd(asp, "{x1;x2;x3}. #minimize{x1, x2}.");
        libclasp.prepare();
        libclasp.solve();
        auto* stats = libclasp.getStats();
        auto  lp    = stats->get(stats->root(), "problem.lp");
        auto  sccs  = stats->get(lp, "sccs");
        auto  m0    = stats->get(stats->root(), "summary.costs.0");
        auto  l0    = stats->get(stats->root(), "summary.lower.0");
        REQUIRE_THROWS_AS(stats->get(stats->root(), "hcc"), std::logic_error);
        REQUIRE(stats->value(m0) == solveCosts(0));
        REQUIRE(stats->value(l0) == 0);
        libclasp.update();
        lpAdd(asp, "x4 | x5 :- x6, not x1."
                   "x6 :- x4, x5, not x2."
                   "x6 :- not x1.");
        libclasp.prepare();
        libclasp.solve();
        REQUIRE(asp.stats.sccs == 1);
        REQUIRE(asp.stats.nonHcfs == 1);
        REQUIRE(lp == stats->get(stats->root(), "problem.lp"));
        REQUIRE(sccs == stats->get(lp, "sccs"));
        REQUIRE(m0 == stats->get(stats->root(), "summary.costs.0"));
        REQUIRE(l0 == stats->get(stats->root(), "summary.lower.0"));
        REQUIRE(stats->value(sccs) == asp.stats.sccs);
        REQUIRE(stats->value(m0) == solveCosts(0));
        auto hcc0     = stats->get(stats->root(), "problem.hcc.0");
        auto hcc0Vars = stats->get(hcc0, "vars");
        REQUIRE(stats->value(hcc0Vars) != 0.0);
        libclasp.update();
        asp.removeMinimize();
        lpAdd(asp, "x7 | x8 :- x9, not x1."
                   "x9 :- x7, x8, not x2."
                   "x9 :- not x1.");
        libclasp.prepare();
        libclasp.solve();
        REQUIRE(libclasp.summary().lpStats()->sccs == 2);
        REQUIRE(libclasp.summary().lpStats()->nonHcfs == 2);
        REQUIRE(lp == stats->get(stats->root(), "problem.lp"));
        REQUIRE(sccs == stats->get(lp, "sccs"));
        REQUIRE_THROWS_AS(stats->value(m0), std::logic_error);
        REQUIRE_THROWS_AS(stats->value(l0), std::logic_error);
        REQUIRE(stats->value(hcc0Vars) != 0.0);
        REQUIRE(stats->value(stats->get(stats->root(), "problem.hcc.1.vars")) != 0.0);
    }
    SECTION("testClingoStatsWithoutStats") {
        config.stats = 0;
        auto& asp    = libclasp.startAsp(config, true);
        lpAdd(asp, "{x1,x2,x3}."
                   "x3 | x4 :- x5, not x1."
                   "x5 :- x4, x3, not x2."
                   "x5 :- not x1.");
        libclasp.solve();
        auto* stats = libclasp.getStats();
        auto  root  = stats->root();
        REQUIRE(stats->size(root) == 3);
        REQUIRE(stats->get(root, "solving") != root);
        REQUIRE(stats->get(root, "problem") != root);
        REQUIRE(stats->get(root, "summary") != root);
        REQUIRE_THROWS_AS(stats->get(root, "solving.accu"), std::out_of_range);
        auto solving = stats->get(root, "solving");
        REQUIRE(stats->find(solving, "accu", nullptr) == false);
    }
    SECTION("testClingoStatsBug") {
        config.stats = 0;
        auto& asp    = libclasp.startAsp(config, true);
        lpAdd(asp, "{x2,x3}. #minimize{not x1,x2}.");
        libclasp.solve();
        auto* stats = libclasp.getStats();
        auto  root  = stats->root();
        REQUIRE(stats->size(root) == 3);
        auto costs = stats->get(root, "summary.costs");
        REQUIRE(costs != root);
        REQUIRE(stats->type(costs) == StatsType::array);
        REQUIRE(stats->size(costs) == 1);
        auto minVal = stats->get(root, "summary.costs.0");
        REQUIRE(minVal != root);
        REQUIRE(stats->type(minVal) == StatsType::value);
        update(config).solve.numModels = -1;
        libclasp.update();
        lpAdd(asp, ":- not x1.");
        libclasp.solve();
        REQUIRE(stats->type(costs) == StatsType::array);
        REQUIRE(stats->size(costs) == 0);
        REQUIRE_THROWS_AS(stats->value(minVal), std::logic_error);
    }
    SECTION("testWritableStats") {
        ClaspStatistics stats;
        StatsMap*       rootMap = stats.makeRoot();
        double          v1      = 2.0;
        rootMap->add("fixed", StatisticObject::value(&v1));

        auto root = stats.root();
        REQUIRE(stats.writable(root));
        REQUIRE(stats.writable(stats.get(root, "fixed")) == false);

        auto v2 = stats.add(root, "mutable", StatsType::value);
        REQUIRE(stats.writable(v2));
        stats.set(v2, 22.0);
        REQUIRE(stats.value(v2) == 22.0);
        decltype(root) found;
        REQUIRE(stats.find(root, "mutable", &found));
        REQUIRE(found == v2);

        auto arr = stats.add(root, "array", StatsType::array);
        REQUIRE(stats.type(arr) == StatsType::array);
        REQUIRE(stats.writable(arr));
        REQUIRE(stats.size(arr) == 0);

        auto mapAtArr0 = stats.push(arr, StatsType::map);
        REQUIRE(stats.type(mapAtArr0) == StatsType::map);
        REQUIRE(stats.size(arr) == 1);
    }
    SECTION("testClingoUserStats") {
        auto& asp = libclasp.startAsp(config, true);
        lpAdd(asp, "{x1;x2;x3}. #minimize{x1, x2}.");
        libclasp.prepare();
        libclasp.solve();
        auto* stats = libclasp.getStats();

        auto r = stats->root();
        REQUIRE(stats->type(r) == StatsType::map);

        auto u = stats->add(r, "user_step", StatsType::map);
        addExternalStats(stats, u);

        REQUIRE(stats->type(u) == StatsType::map);
        auto user = stats->get(u, "deathCounter");
        REQUIRE(stats->type(user) == StatsType::map);
        REQUIRE(stats->value(stats->get(user, "total")) == double(42));
        REQUIRE(stats->value(stats->get(user, "chickens")) == double(712));
        auto array = stats->get(user, "thread");
        REQUIRE(stats->type(array) == StatsType::array);
        REQUIRE(stats->size(array) == 4);
        for (auto t : irange(4u)) {
            auto m1 = stats->at(array, t);
            REQUIRE(stats->type(m1) == StatsType::map);
            auto value = stats->get(m1, "total");
            REQUIRE(stats->type(value) == StatsType::value);
            REQUIRE(stats->value(value) == double(20 * (t + 1)));
            auto m2 = stats->get(m1, "Animals");
            REQUIRE(stats->type(m2) == StatsType::map);
            value = stats->get(m2, "chicken");
            REQUIRE(stats->value(value) == double(2 * (t + 1)));
            value = stats->get(m2, "cows");
            REQUIRE(stats->value(value) == double(5 * (t + 1)));
            value = stats->get(m1, "feeding cost");
            REQUIRE(stats->value(value) == double(t + 1));
        }
        decltype(r) total;
        REQUIRE(stats->find(r, "user_step.deathCounter.thread.1.total", &total));
        REQUIRE(stats->type(total) == StatsType::value);
        REQUIRE(stats->value(total) == 40.0);
        REQUIRE(stats->find(r, "user_step.deathCounter.thread.001.total", nullptr));
        REQUIRE_FALSE(stats->find(r, "user_step.deathCounter.thread.5.total", nullptr));
        REQUIRE_FALSE(stats->find(r, "user_step.deathCounter.thread.64.total", nullptr));
        REQUIRE_FALSE(stats->find(r, "user_step.deathCounter.thread.-1.total", nullptr));
        REQUIRE_FALSE(stats->find(r, "user_step.deathCounter.thread.  1.total", nullptr));
        REQUIRE_FALSE(stats->find(r, "user_step.deathCounter.thread.0x1.total", nullptr));

        std::vector<std::string> keys;
        getStatsKeys(*stats, r, keys, "");
        REQUIRE_FALSE(keys.empty());
        for (const auto& key : keys) {
            REQUIRE(stats->find(r, key, nullptr));
            REQUIRE(stats->type(stats->get(r, key)) == StatsType::value);
        }
        REQUIRE(keys.size() == 260);

        struct V : StatsVisitor {
            void visitLogicProgramStats(const Asp::LpStats& stats) override {
                ++lps;
                REQUIRE(stats.rules[0][Asp::RuleStats::minimize] == 1);
            }
            void visitProblemStats(const ProblemStats& stats) override {
                ++probs;
                REQUIRE(stats.vars.num == 3);
            }
            void visitSolverStats(const SolverStats& stats) override {
                ++solvers;
                REQUIRE(stats.choices != 0);
            }
            void visitExternalStats(const StatisticObject& stats) override {
                ++user;
                REQUIRE(stats.at("deathCounter").at("total").value() == 42.0);
                REQUIRE(stats.at("deathCounter").at("thread")[1].at("total").value() == double(40.0));
                REQUIRE(stats.at("deathCounter").at("thread")[1].at("Animals").at("chicken").value() == double(4.0));
            }
            int lps     = 0;
            int probs   = 0;
            int solvers = 0;
            int user    = 0;
        } vis;
        libclasp.summary().accept(vis);
        REQUIRE(vis.lps == 1);
        REQUIRE(vis.probs == 1);
        REQUIRE(vis.solvers == 1);
        REQUIRE(vis.user == 1);
    }
}

TEST_CASE("Clingo propagator plain", "[facade][propagator]") {
    using MyInit = ClingoPropagatorInit;
    PropagatorTest test;
    SharedContext& ctx  = test.ctx;
    auto&          vars = test.vars;
    TestPropagator prop;
    MyInit         tp(ctx, prop, nullptr);
    LitVec         changes;
    auto           mapChanges = [&](Potassco::AbstractPropagator::ChangeList x) {
        changes.clear();
        for (auto lit : x) { changes.push_back(decodeLit(lit)); }
    };
    prop.onPropagate = [&](const auto&, const auto&, auto x) { mapChanges(x); };
    prop.onUndo      = [&](const auto&, auto x) { mapChanges(x); };

    SECTION("testAssignmentBasics") {
        ClingoAssignment assignment(*ctx.master());

        REQUIRE(assignment.size() == 1);
        REQUIRE(assignment.trailSize() == 1);
        REQUIRE(assignment.trailBegin(0) == 0);
        REQUIRE(assignment.trailAt(0) == encodeLit(lit_true));
        REQUIRE(assignment.trailEnd(0) == 1);

        test.addVars(2);
        const auto a1 = encodeLit(posLit(vars[1]));
        const auto a2 = encodeLit(posLit(vars[2]));
        REQUIRE(assignment.size() == 3);
        REQUIRE(assignment.level(a1) == UINT32_MAX);
        REQUIRE(assignment.level(a2) == UINT32_MAX);

        ctx.requestStepVar();
        REQUIRE(assignment.size() == 3);
        ctx.endInit();
        REQUIRE(assignment.size() == 4);
        REQUIRE(assignment.trailSize() == 1);

        Solver& master = *ctx.master();
        master.pushRoot(ctx.stepLiteral());
        REQUIRE(assignment.trailSize() == 2);
        REQUIRE(assignment.trailBegin(1) == 1);
        REQUIRE(assignment.trailAt(1) == encodeLit(ctx.stepLiteral()));
        REQUIRE(assignment.trailEnd(1) == 2);

        master.assume(posLit(vars[1])) && master.propagate();
        master.assume(negLit(vars[2])) && master.propagate();

        REQUIRE(assignment.isTotal());
        REQUIRE(assignment.trailSize() == 4);
        REQUIRE(assignment.trailAt(0) == encodeLit(lit_true));
        REQUIRE(assignment.trailAt(1) == encodeLit(ctx.stepLiteral()));
        REQUIRE(assignment.trailAt(2) == Potassco::lit(a1));
        REQUIRE(assignment.trailAt(3) == Potassco::neg(a2));
        REQUIRE(assignment.level() == 3);
        REQUIRE((assignment.trailBegin(0) == 0 && assignment.trailEnd(0) == 1));
        REQUIRE((assignment.trailBegin(1) == 1 && assignment.trailEnd(1) == 2));
        REQUIRE((assignment.trailBegin(2) == 2 && assignment.trailEnd(2) == 3));
        REQUIRE((assignment.trailBegin(3) == 3 && assignment.trailEnd(3) == 4));
        REQUIRE(assignment.level(a1) == 2);
        REQUIRE(assignment.level(a2) == 3);
    }

    SECTION("testClingoAssignmentContainsAllProblemVars") {
        ClingoAssignment assignment(*ctx.master());

        // Add vars to shared context but do not yet commit to solver
        auto v1 = ctx.addVar(VarType::atom);
        auto v2 = ctx.addVar(VarType::atom);
        CHECK(ctx.validVar(v1));
        CHECK(ctx.validVar(v1));
        CHECK_FALSE(ctx.master()->validVar(v1));
        CHECK_FALSE(ctx.master()->validVar(v2));
        CHECK(ctx.master()->numFreeVars() == 0);

        CHECK(assignment.size() == 3);
        CHECK(assignment.trailSize() == 1);
        CHECK(assignment.trailBegin(0) == 0);
        CHECK(assignment.trailAt(0) == encodeLit(lit_true));
        CHECK(assignment.trailEnd(0) == 1);
        CHECK_FALSE(assignment.isTotal());
        CHECK(assignment.unassigned() == 2);
        CHECK(assignment.value(encodeLit(posLit(v1))) == Potassco::TruthValue::free);
        CHECK(assignment.value(encodeLit(posLit(v1))) == Potassco::TruthValue::free);
    }

    SECTION("testAssignment") {
        Potassco::Lit_t v1 = 0, v2 = 0;
        prop.onCheck = [&](const Potassco::AbstractAssignment& a, const PropagatorControl&) {
            REQUIRE_FALSE(a.hasConflict());
            REQUIRE(a.level() == 2);
            REQUIRE(a.value(v1) == Potassco::TruthValue::true_);
            REQUIRE(a.value(v2) == Potassco::TruthValue::false_);
            REQUIRE(a.isTrue(v1));
            REQUIRE(a.isFalse(v2));
            REQUIRE(a.isTrue(Potassco::neg(v2)));
            REQUIRE(a.level(v1) == 1);
            REQUIRE(a.level(v2) == 2);
            REQUIRE_FALSE(a.hasLit(v2 + 1));
            REQUIRE(a.decision(0) == encodeLit(lit_true));
            REQUIRE(a.decision(1) == v1);
            REQUIRE(a.decision(2) == Potassco::neg(v2));
            REQUIRE(a.trailSize() == 3);
            REQUIRE(a.trailAt(0) == encodeLit(lit_true));
            REQUIRE(a.trailAt(1) == v1);
            REQUIRE(a.trailAt(2) == Potassco::neg(v2));
            REQUIRE(a.trailBegin(0) == 0);
            REQUIRE(a.trailEnd(0) == 1);
            REQUIRE(a.trailBegin(1) == 1);
            REQUIRE(a.trailEnd(1) == 2);
            REQUIRE(a.trailBegin(2) == 2);
            REQUIRE(a.trailEnd(2) == 3);
        };

        test.addVars(2);
        v1 = encodeLit(posLit(vars[1]));
        v2 = encodeLit(posLit(vars[2]));
        tp.addPropagator(*ctx.master());
        ctx.endInit();
        ctx.master()->assume(posLit(vars[1])) && ctx.master()->propagate();
        ctx.master()->assume(negLit(vars[2])) && ctx.master()->propagate();
        ctx.master()->search(0, 0);
    }

    SECTION("testPropagateChange") {
        test.addVars(5);
        tp.addWatch(posLit(vars[1]));
        tp.addWatch(posLit(vars[1])); // ignore duplicates
        tp.addWatch(posLit(vars[2]));
        tp.addWatch(posLit(vars[3]));
        tp.addWatch(negLit(vars[3]));
        tp.addWatch(negLit(vars[4]));
        tp.addPropagator(*ctx.master());
        ctx.endInit();
        auto& s = *ctx.master();
        s.assume(posLit(vars[1])) && s.propagate();
        REQUIRE(changes == LitVec{posLit(vars[1])});

        s.assume(negLit(vars[4])) && s.force(posLit(vars[2]), nullptr) && s.propagate();
        REQUIRE(changes == LitVec{negLit(vars[4]), posLit(vars[2])});
        changes.clear();
        s.undoUntil(s.decisionLevel() - 1);
        REQUIRE(changes == LitVec{negLit(vars[4]), posLit(vars[2])});
        s.undoUntil(s.decisionLevel() - 1);
        REQUIRE(changes == LitVec{posLit(vars[1])});
        changes.clear();
        s.assume(negLit(vars[2])) && s.propagate();
        REQUIRE(changes.empty());
    }

    SECTION("testAddClause") {
        test.addVars(3);
        tp.addWatch(prop.fire = negLit(vars[3]));
        prop.addToClause(posLit(vars[1]));
        prop.addToClause(posLit(vars[2]));
        tp.addPropagator(*ctx.master());
        ctx.endInit();
        auto& s = *ctx.master();
        s.assume(negLit(vars[3])) && s.propagate();
        REQUIRE(ctx.numLearntShort() == 1);
    }
    SECTION("testAddUnitClause") {
        test.addVars(3);
        tp.addWatch(prop.fire = negLit(vars[3]));
        prop.addToClause(posLit(vars[1]));
        prop.addToClause(posLit(vars[2]));
        tp.addPropagator(*ctx.master());
        ctx.endInit();
        auto& s = *ctx.master();
        s.assume(negLit(vars[2])) && s.propagate();
        uint32_t learntExpected = 0;
        SECTION("default") {
            prop.clProp    = Potassco::ClauseType::learnt;
            learntExpected = 1;
        }
        SECTION("locked") {
            prop.clProp    = Potassco::ClauseType::locked;
            learntExpected = 0;
        }
        s.assume(negLit(vars[3])) && s.propagate();
        INFO("clause type: " << Potassco::to_underlying(prop.clProp));
        REQUIRE(ctx.numLearntShort() == learntExpected);
        REQUIRE(s.isTrue(posLit(vars[1])));
        REQUIRE(changes == LitVec{negLit(vars[3])});
    }
    SECTION("testAddUnitClauseWithUndo") {
        test.addVars(5);
        prop.fire = posLit(vars[5]);
        tp.addWatch(posLit(vars[3]));
        tp.addWatch(posLit(vars[5]));
        prop.addToClause(posLit(vars[1]));
        prop.addToClause(posLit(vars[2]));
        prop.addToClause(posLit(vars[3]));
        tp.addPropagator(*ctx.master());
        ctx.endInit();
        auto& s = *ctx.master();
        s.assume(negLit(vars[1])) && s.propagate();
        s.assume(posLit(vars[4])) && s.propagate();
        s.assume(negLit(vars[2])) && s.propagate();
        uint32_t learntExpected = 0;
        SECTION("default") {
            prop.clProp    = Potassco::ClauseType::learnt;
            learntExpected = 1;
        }
        SECTION("locked") {
            prop.clProp    = Potassco::ClauseType::locked;
            learntExpected = 0;
        }
        INFO("clause type: " << Potassco::to_underlying(prop.clProp));
        s.assume(posLit(vars[5])) && s.propagate();
        REQUIRE(ctx.numLearntShort() == learntExpected);
        REQUIRE(s.decisionLevel() == 3);
        s.undoUntil(2);
        REQUIRE(contains(changes, posLit(vars[3])));
    }
    SECTION("testAddUnsatClause") {
        test.addVars(3);
        tp.addWatch(prop.fire = negLit(vars[3]));
        prop.addToClause(posLit(vars[1]));
        prop.addToClause(posLit(vars[2]));
        tp.addPropagator(*ctx.master());
        ctx.endInit();
        auto& s = *ctx.master();
        s.assume(negLit(vars[2])) && s.propagate();
        s.assume(negLit(vars[1])) && s.propagate();
        s.assume(negLit(vars[3]));
        s.pushRootLevel(2);
        SECTION("default") { prop.clProp = Potassco::ClauseType::learnt; }
        SECTION("locked") { prop.clProp = Potassco::ClauseType::locked; }
        INFO("clause type: " << Potassco::to_underlying(prop.clProp));
        REQUIRE_FALSE(s.propagate());
        INFO("do not add conflicting constraint");
        REQUIRE(ctx.numLearntShort() == 0);
        s.popRootLevel(1);
        REQUIRE(s.decisionLevel() == 1);
        prop.clause.clear();
        prop.addToClause(negLit(vars[2]));
        prop.addToClause(posLit(vars[3]));
        s.assume(negLit(vars[3]));
        REQUIRE(s.propagate());
        INFO("do not add sat constraint");
        REQUIRE(ctx.numLearntShort() == 0);
    }
    SECTION("testAddEmptyClause") {
        test.addVars(1);
        tp.addWatch(prop.fire = negLit(vars[1]));
        prop.addToClause(negLit(0));
        tp.addPropagator(*ctx.master());
        ctx.endInit();
        auto& s = *ctx.master();
        s.assume(negLit(vars[1]));
        REQUIRE_FALSE(s.propagate());
    }
    SECTION("testAddSatClause") {
        test.addVars(3);
        tp.addWatch(prop.fire = negLit(vars[3]));
        prop.addToClause(posLit(vars[1]));
        prop.addToClause(posLit(vars[2]));
        tp.addPropagator(*ctx.master());
        ctx.endInit();
        auto& s = *ctx.master();
        s.assume(posLit(vars[1])) && s.force(negLit(vars[2]), posLit(vars[1])) && s.propagate();
        s.assume(negLit(vars[3]));
        REQUIRE((s.decisionLevel() == 2 && not s.hasConflict()));
        REQUIRE(s.propagate());
        REQUIRE(uint32_t(2) == s.decisionLevel());
    }
    SECTION("testAddClauseOnModel") {
        test.addVars(3);
        prop.addToClause(posLit(vars[1]));
        prop.addToClause(posLit(vars[3]));
        tp.addPropagator(*ctx.master());
        ctx.endInit();
        auto& s = *ctx.master();
        auto  v = s.search();
        REQUIRE((v == value_true && s.numFreeVars() == 0));
        REQUIRE(ctx.shortImplications().numLearnt() == 1);
    }
    SECTION("testAddConflictOnModel") {
        test.addVars(3);
        prop.addToClause(negLit(vars[1]));
        prop.addToClause(negLit(vars[2]));
        tp.addPropagator(*ctx.master());
        ctx.endInit();
        auto& s = *ctx.master();
        s.assume(posLit(vars[1]));
        s.force(posLit(vars[2]), posLit(vars[1]));
        s.propagate();
        s.assume(posLit(vars[3])) && s.propagate();
        REQUIRE((not s.hasConflict() && s.numFreeVars() == 0));
        REQUIRE_FALSE(s.getPost(PostPropagator::priority_class_general)->isModel(s));
        REQUIRE(s.hasConflict());
        REQUIRE((s.decisionLevel() == 1 && s.resolveConflict()));
    }

    SECTION("testAddLocked") {
        test.addVars(2);
        prop.addToClause(posLit(vars[1]));
        prop.addToClause(posLit(vars[2]));
        prop.fire   = lit_true;
        prop.clProp = Potassco::ClauseType::locked;
        tp.addWatch(negLit(vars[1]));
        tp.addPropagator(*ctx.master());
        ctx.endInit();

        auto& s = *ctx.master();
        REQUIRE(s.numWatches(negLit(vars[2])) == 0);
        s.assume(negLit(vars[1])) && s.propagate();
        REQUIRE(s.numWatches(negLit(vars[2])) == 1);
        s.reduceLearnts(1.0);
        REQUIRE(s.numWatches(negLit(vars[2])) == 1);
    }
    SECTION("testAddLockedAsserting") {
        test.addVars(2);
        prop.addToClause(posLit(vars[1]));
        prop.addToClause(posLit(vars[2]));
        prop.fire   = negLit(vars[2]);
        prop.clProp = Potassco::ClauseType::locked;
        tp.addWatch(negLit(vars[2]));
        tp.addPropagator(*ctx.master());
        ctx.endInit();
        auto& s = *ctx.master();
        s.assume(negLit(vars[1])) && s.propagate();
        REQUIRE(s.assume(negLit(vars[2])));
        REQUIRE(s.propagate());
        REQUIRE(s.numLearntConstraints() == 0);
        REQUIRE(s.isTrue(posLit(vars[2])));
        REQUIRE(s.decisionLevel() == 1);
        prop.fire = lit_false;
        s.undoUntil(0);
        s.assume(negLit(vars[1])) && s.propagate();
        REQUIRE(s.isTrue(posLit(vars[2])));
    }
    SECTION("testAddLockedConflicting") {
        ctx.setShortMode(ContextParams::short_explicit);
        test.addVars(4);
        ctx.addTernary(posLit(vars[1]), negLit(vars[2]), posLit(vars[3]));
        prop.addToClause(posLit(vars[1]));
        prop.addToClause(posLit(vars[2]));
        prop.addToClause(posLit(vars[3]));
        prop.fire   = negLit(vars[4]);
        prop.clProp = Potassco::ClauseType::locked;
        tp.addWatch(negLit(vars[4]));
        tp.addPropagator(*ctx.master());
        ctx.endInit();
        auto& s = *ctx.master();
        s.assume(negLit(vars[1])) && s.propagate();
        s.assume(negLit(vars[3])) && s.propagate();
        REQUIRE(s.propagate());
        REQUIRE(s.isTrue(negLit(vars[2])));
        s.assume(negLit(4));
        REQUIRE_FALSE(s.propagate());
        REQUIRE(s.resolveConflict());
        REQUIRE(s.numLearntConstraints() == 1);
        s.undoUntil(0);
        s.reduceLearnts(1.0f);
        REQUIRE(s.numLearntConstraints() == 0);
        prop.fire = lit_false;
        s.assume(negLit(vars[1])) && s.propagate();
        s.assume(negLit(vars[3]));
        REQUIRE_FALSE(s.propagate());
    }
    SECTION("testAddLockedBacktrackUnit") {
        test.addVars(4);
        prop.addToClause(posLit(vars[1]));
        prop.addToClause(posLit(vars[2]));
        prop.addToClause(posLit(vars[3]));
        prop.fire   = negLit(vars[4]);
        prop.clProp = Potassco::ClauseType::locked;
        tp.addWatch(negLit(vars[4]));
        tp.addPropagator(*ctx.master());
        ctx.endInit();
        auto& s = *ctx.master();
        s.assume(negLit(vars[1])) && s.propagate();
        s.assume(negLit(vars[3])) && s.propagate();
        s.assume(negLit(vars[4]));
        REQUIRE(s.decisionLevel() == 3);
        REQUIRE(s.propagate());
        REQUIRE(s.decisionLevel() == 2);
        REQUIRE(s.isTrue(posLit(vars[2])));
        REQUIRE(s.numLearntConstraints() == 0);
    }
    SECTION("attach") {
        test.addVars(4);
        auto checkCalled = false;
        prop.onInit      = [&](const auto&, auto& init) { init.setCheckMode(Potassco::PropagatorCheckMode::fixpoint); };
        prop.onCheck     = [&](const auto&, PropagatorControl&) { checkCalled = true; };
        SECTION("called once") {
            auto attachCalled = false;
            prop.onAttach     = [&](const auto& a, PropagatorControl&) {
                REQUIRE(prop.inits == 1);
                REQUIRE_FALSE(attachCalled);
                REQUIRE_FALSE(checkCalled);
                REQUIRE(a.solverId() == 0);
                REQUIRE(a.level() == 0);
                attachCalled = true;
            };
            tp.addPropagator(*ctx.master());
            ctx.endInit();
            REQUIRE(prop.inits == 1);
            REQUIRE(attachCalled);
            REQUIRE(checkCalled);
        }
        SECTION("not called on conflict") {
            auto attachCalled = false;
            prop.onAttach     = [&](const auto&, PropagatorControl&) { attachCalled = true; };
            tp.addPropagator(*ctx.master());
            REQUIRE(ctx.addUnary(posLit(1)));
            REQUIRE_FALSE(ctx.addUnary(negLit(1)));
            REQUIRE(ctx.master()->hasConflict());
            ctx.endInit();
            REQUIRE_FALSE(attachCalled);
            REQUIRE(prop.inits == 0);
        }
        SECTION("can add watches") {
            prop.initWatches.push_back(posLit(1));
            prop.onAttach = [&](const auto& a, PropagatorControl& ctl) {
                REQUIRE(ctl.hasWatch(encodeLit(posLit(1))));
                REQUIRE(a.size() == 5);
                REQUIRE_FALSE(ctl.hasWatch(encodeLit(posLit(2))));
                ctl.addWatch(encodeLit(posLit(2)));
                ctl.addWatch(encodeLit(posLit(3)));
                REQUIRE(ctl.hasWatch(encodeLit(posLit(2))));
                REQUIRE(ctl.hasWatch(encodeLit(posLit(3))));
            };
            tp.addPropagator(*ctx.master());
            ctx.addUnary(posLit(3));
            ctx.endInit();
            REQUIRE(contains(changes, posLit(3)));
            changes.clear();
            ctx.master()->assume(posLit(2)) && ctx.master()->propagate();
            REQUIRE(contains(changes, posLit(2)));
        }
        SECTION("can add vars") {
            Potassco::Lit_t v1 = 0, v2 = 0;
            prop.onAttach = [&](const auto& a, PropagatorControl& ctl) {
                REQUIRE(a.size() == 5);
                v1 = ctl.addVariable();
                v2 = ctl.addVariable();
                REQUIRE(a.size() == 7);
                ctl.addWatch(v1);
                ctl.addWatch(-v2);
            };
            prop.onCheck = [&](const auto& a, const PropagatorControl& ctl) {
                REQUIRE(a.size() == 7);
                REQUIRE(ctl.hasWatch(v1));
                REQUIRE(ctl.hasWatch(-v2));
            };
            tp.addPropagator(*ctx.master());
            REQUIRE(ctx.numVars() == 4);
            ctx.endInit();
            REQUIRE(ctx.numVars() == 4);
            REQUIRE(ctx.master()->numAuxVars() == 2);
            REQUIRE(v1 != 0);
            REQUIRE(v2 > v1);
            ctx.unfreeze();
            REQUIRE(ctx.numVars() == 4);
            REQUIRE(ctx.master()->numAuxVars() == 0);
            prop.onCheck  = nullptr;
            prop.onAttach = [&](const auto& a, const PropagatorControl& ctl) {
                REQUIRE(a.size() == 5);
                REQUIRE_FALSE(ctl.hasWatch(v1));
                REQUIRE_FALSE(ctl.hasWatch(-v2));
                v1 = v2 = 0;
            };
            ctx.endInit();
            REQUIRE(v1 == 0);
            REQUIRE(v2 == v1);
        }
        SECTION("can add clauses") {
            ctx.requestStepVar();
            prop.onAttach = [&](const auto& a, PropagatorControl& ctl) {
                prop.addToClause(posLit(1));
                prop.addToClause(posLit(2));
                prop.addToClause(posLit(3));
                prop.addToClause(posLit(4));
                REQUIRE(ctl.addClause(prop.clause));

                ctl.addWatch(encodeLit(negLit(1)));
                prop.clause.clear();
                prop.addToClause(negLit(1));
                REQUIRE(ctl.addClause(prop.clause));
                REQUIRE(ctl.propagate());
                REQUIRE(a.isTrue(prop.clause.front()));
                REQUIRE(changes.empty());
                REQUIRE(ctx.numLearntShort() == 0);
                REQUIRE(ctx.master()->numLearntConstraints() == 1);

                auto v1 = ctl.addVariable();
                auto v2 = ctl.addVariable();
                auto x3 = encodeLit(posLit(4));
                REQUIRE(ctl.addClause(Potassco::LitVec{v1, v2, x3}, Potassco::ClauseType::locked));
            };
            tp.addPropagator(*ctx.master());
            ctx.endInit();
            REQUIRE(ctx.master()->isTrue(negLit(1)));
            REQUIRE(contains(changes, negLit(1)));
            REQUIRE(ctx.numLearntShort() == 1);                 // [2 v 3 v 4]
            REQUIRE(ctx.master()->numLearntConstraints() == 0); // [aux1 v aux2 v 3]
            auto* pp = ctx.master()->getPost<ClingoPropagator>();
            REQUIRE(pp);
            REQUIRE(pp->numConstraints() == 1u);
            ctx.unfreeze();
            REQUIRE(ctx.master()->numLearntConstraints() == 0);
            REQUIRE(ctx.master()->isTrue(negLit(1)));
            REQUIRE(pp->numConstraints() == 0u); // locked ignore due to aux vars
        }
        SECTION("attach is solver-local") {
            ctx.setConcurrency(3, SharedContext::resize_push);
            SolverSet expected;
            for (auto i = 0u; ctx.hasSolver(i); ++i) {
                tp.addPropagator(*ctx.solver(i));
                expected.add(i);
            }
            REQUIRE(expected.count() == 3);
            prop.onAttach = [&](const auto& a, PropagatorControl& ctl) {
                auto id = a.solverId();
                REQUIRE(expected.remove(id));
                ctl.addWatch(encodeLit(posLit(1 + id)));
            };
            ctx.endInit(true);
            REQUIRE(expected.count() == 0);
            for (auto i = 0u; ctx.hasSolver(i); ++i) {
                auto* pp = ctx.solver(i)->getPost(PostPropagator::priority_class_general);
                REQUIRE(ctx.solver(i)->hasWatch(posLit(1 + i), pp));
            }
        }
        SECTION("can add weight constraint") {
            ctx.requestStepVar();
            auto auxLit   = lit_false;
            prop.onAttach = [&](const auto&, PropagatorControl& ctl) {
                auto l1 = encodeLit(posLit(1));
                auto l2 = encodeLit(posLit(2));
                auto l3 = encodeLit(posLit(3));
                auto l4 = encodeLit(posLit(4));
                auto l5 = ctl.addVariable();
                auxLit  = decodeLit(l5);
                REQUIRE(ctl.addWeightConstraint(l1,
                                                std::array{Potassco::WeightLit{l2, 1}, Potassco::WeightLit{l3, 1},
                                                           Potassco::WeightLit{l4, 1}, Potassco::WeightLit{l5, 1}},
                                                2, 0));
            };
            tp.addPropagator(*ctx.master());
            ctx.endInit();
            REQUIRE(prop.inits == 1);
            REQUIRE(ctx.numConstraints() == 0);
            REQUIRE(ctx.numVars() == 5);
            REQUIRE(ctx.master()->numAuxVars() == 1);
            auto* pp = ctx.master()->getPost<ClingoPropagator>();
            REQUIRE(pp);
            REQUIRE(pp->numConstraints() == 1u);
            ctx.master()->assume(posLit(1)) && ctx.master()->propagate();
            ctx.master()->assume(negLit(2)) && ctx.master()->propagate();
            ctx.master()->assume(negLit(4)) && ctx.master()->propagate();
            REQUIRE(ctx.master()->isTrue(posLit(3)));
            REQUIRE(ctx.master()->isTrue(auxLit));
            ctx.unfreeze();
            REQUIRE(pp->numConstraints() == 0u);
        }
    }
    SECTION("exceptions") {
        test.addVars(2);
        auto p = posLit(vars[1]);
        tp.addWatch(p);
        tp.addPropagator(*ctx.master());
        ctx.endInit();
        Solver& s        = *ctx.master();
        bool    fail     = true;
        prop.onPropagate = [&](const auto&, const auto&, Potassco::AbstractPropagator::ChangeList) {
            if (fail) {
                throw std::runtime_error("some error from the propagator");
            }
        };
        s.assume(p);
        REQUIRE_THROWS_AS(s.propagate(), std::runtime_error);
        s.undoUntil(0);
        fail = false;
        s.assume(p);
        REQUIRE_NOTHROW(s.propagate());
    }
}
TEST_CASE("Clingo propagator with facade", "[facade][propagator]") {
    ClaspConfig    config;
    ClaspFacade    libclasp;
    TestPropagator prop;

    SECTION("with program") {
        auto& asp = libclasp.startAsp(config, true);
        libclasp.registerPropagator(prop, false);
        lpAdd(asp, "{x1;x2}.");
        asp.endProgram();
        SECTION("testAttachToSolver") {
            for (auto v : libclasp.ctx.vars()) {
                prop.initWatches.push_back(posLit(v));
                prop.initWatches.push_back(negLit(v));
            }
            prop.clearInitWatches = true;
            libclasp.prepare();
            auto* pp0 = libclasp.ctx.master()->getPost(PostPropagator::priority_class_general);
            REQUIRE(pp0);
            REQUIRE(libclasp.ctx.master()->hasWatch(posLit(1), pp0));
#if CLASP_HAS_THREADS
            update(config).solve.setSolvers(2);
            libclasp.update();
            libclasp.prepare();
            REQUIRE((libclasp.ctx.concurrency() == 2 && libclasp.ctx.hasSolver(1)));
            libclasp.solve();
            auto* pp1 = libclasp.ctx.solver(1)->getPost(PostPropagator::priority_class_general);
            REQUIRE(pp1);
            REQUIRE(libclasp.ctx.solver(1)->hasWatch(posLit(1), pp1));

            update(config).solve.setSolvers(1);
            libclasp.update();
            libclasp.prepare();
            REQUIRE(libclasp.ctx.concurrency() == 1);
            update(config).solve.setSolvers(2);
            libclasp.update();
            libclasp.solve();
            pp1 = libclasp.ctx.solver(1)->getPost(PostPropagator::priority_class_general);
            REQUIRE(pp1);
            REQUIRE(libclasp.ctx.solver(1)->hasWatch(posLit(1), pp1));
#endif
        }

        SECTION("testAddVolatile") {
            prop.initWatches.push_back(negLit(1));
            prop.addToClause(posLit(1));
            prop.addToClause(posLit(2));
            libclasp.prepare();
            prop.fire   = libclasp.ctx.stepLiteral();
            prop.clProp = Potassco::ClauseType::transient;
            libclasp.solve();
            REQUIRE(libclasp.ctx.numLearntShort() == 1);
            libclasp.update();
            REQUIRE(libclasp.ctx.numLearntShort() == 0);
        }
        SECTION("testAddVolatileFact") {
            prop.initWatches.push_back(negLit(1));
            prop.addToClause(posLit(2));

            prop.fire   = negLit(1);
            prop.clProp = Potassco::ClauseType::transient;
            libclasp.ctx.addUnary(negLit(1));
            libclasp.prepare();
            REQUIRE(libclasp.ctx.numLearntShort() == 1);
            libclasp.update();
            REQUIRE(libclasp.ctx.numLearntShort() == 0);
        }
        SECTION("testAddVolatileConflict") {
            prop.initWatches.push_back(negLit(1));
            prop.addToClause(posLit(1));
            prop.fire   = negLit(1);
            prop.clProp = Potassco::ClauseType::transient;
            libclasp.ctx.addUnary(negLit(1));
            libclasp.prepare();
            REQUIRE(libclasp.ctx.ok());
            REQUIRE(libclasp.ctx.stepLiteral() != lit_false);
            REQUIRE(libclasp.ctx.master()->isFalse(libclasp.ctx.stepLiteral()));
            REQUIRE(libclasp.solve().unsat());
            libclasp.update();
            REQUIRE(libclasp.ctx.stepLiteral() == lit_false);
            prop.fire = lit_false;
            prop.clause.clear();
            REQUIRE(libclasp.solve().sat());
        }
        SECTION("testAddVolatileStatic") {
            prop.initWatches.push_back(negLit(1));
            prop.addToClause(posLit(1));
            prop.addToClause(posLit(2));
            libclasp.prepare();
            prop.fire   = libclasp.ctx.stepLiteral();
            prop.clProp = Potassco::ClauseType::transient_locked;
            libclasp.solve();
            REQUIRE(libclasp.ctx.master()->numWatches(negLit(2)) == 1);
            libclasp.update();
            REQUIRE(libclasp.ctx.master()->numWatches(negLit(2)) == 0);
        }
    }
    SECTION("testLookaheadBug") {
        config.addSolver(0).lookType = +VarType::atom;
        SatBuilder& sat              = libclasp.startSat(config);
        libclasp.registerPropagator(prop, false);
        sat.prepareProblem(2);
        LitVec clause;
        clause.push_back(negLit(1));
        clause.push_back(negLit(2));
        sat.addClause(clause);
        clause.pop_back();
        clause.push_back(posLit(2));
        sat.addClause(clause);
        prop.initWatches.push_back(negLit(1));
        bool gotLit      = false;
        prop.onPropagate = [&](const auto&, auto&, Potassco::AbstractPropagator::ChangeList changes) {
            REQUIRE(changes.size() == 1);
            REQUIRE(decodeLit(changes[0]) == negLit(1));
            gotLit = true;
        };
        libclasp.prepare();
        REQUIRE(libclasp.ctx.master()->isTrue(negLit(1)));
        REQUIRE(gotLit);
    }
    SECTION("testNoReentrantBacktrack") {
        prop.onInit = [](const auto&, PropagatorInit& init) {
            init.setCheckMode(Potassco::PropagatorCheckMode::fixpoint);
        };
        prop.initWatches.push_back(negLit(1));
        bool        checkUndo = true;
        std::string undoError;
        auto        undoCb = [&](const auto& a, Potassco::LitSpan changes) {
            if (checkUndo) {
                if (changes.size() != 1) {
                    undoError = "invalid changes - expected size 1 but got " + std::to_string(changes.size());
                }
                else if (auto v = decodeLit(changes[0]).var(); v != 1) {
                    undoError = "invalid changes - expected var 1 but got " + std::to_string(v);
                }
                else if (a.level() != 1) {
                    undoError = "invalid level - expected 1 but got " + std::to_string(a.level());
                }
                checkUndo = false;
            }
        };
        SECTION("Lookahead") {
            config.addSolver(0).lookType = +VarType::atom;
            SatBuilder& sat              = libclasp.startSat(config);
            sat.prepareProblem(4);
            libclasp.registerPropagator(prop, false);
            LitVec clause;
            clause.push_back(negLit(1));
            clause.push_back(negLit(2));
            clause.push_back(negLit(3));
            clause.push_back(negLit(4));
            sat.addClause(clause);

            prop.onUndo  = undoCb;
            prop.onCheck = [&, added = false](const auto& a, PropagatorControl& ctl) mutable {
                if (a.level() == 1 && a.value(4) == Potassco::TruthValue::free) {
                    REQUIRE(a.value(3) == Potassco::TruthValue::free);
                    REQUIRE(not added);
                    Potassco::Lit_t cl[2] = {3, 4};
                    REQUIRE(ctl.addClause(cl));
                    cl[0] = -3;
                    REQUIRE(ctl.addClause(cl));
                    cl[0] = 2;
                    cl[1] = 5;
                    REQUIRE(ctl.addClause(cl));
                    added     = true;
                    auto u    = prop.undos;
                    auto x    = a.level();
                    checkUndo = true;
                    if (not ctl.propagate()) {
                        return;
                    }
                    REQUIRE(u == prop.undos);
                    REQUIRE(x == a.level());
                }
                else if (added) {
                    INFO("lookahead not executed");
                    REQUIRE(a.value(4) != Potassco::TruthValue::free);
                }
            };
            libclasp.prepare();
            CHECK(libclasp.solve().sat());
            CAPTURE(undoError);
            REQUIRE(undoError.empty());
        }

        SECTION("ClingoPropagator") {
            TestPropagator other;
            SatBuilder&    sat = libclasp.startSat(config);
            sat.prepareProblem(4);
            other.onInit = [](const auto&, PropagatorInit& init) {
                init.setCheckMode(Potassco::PropagatorCheckMode::fixpoint);
            };
            other.initWatches.push_back(negLit(1));
            libclasp.registerPropagator(prop, false);
            libclasp.registerPropagator(other, false);
            LitVec clause;
            clause.push_back(negLit(1));
            clause.push_back(negLit(2));
            clause.push_back(negLit(3));
            clause.push_back(negLit(4));
            sat.addClause(clause);
            bool enable   = false;
            other.onCheck = [&](const auto& a, PropagatorControl& ctl) {
                if (a.level() == 1) {
                    if (not enable) {
                        Potassco::Lit_t cl[2] = {2, 5};
                        REQUIRE(ctl.addClause(cl));
                        enable    = true;
                        auto x    = a.level();
                        auto u    = other.undos;
                        checkUndo = true;
                        if (not ctl.propagate()) {
                            return;
                        }
                        REQUIRE(u == other.undos);
                        REQUIRE(x == a.level());
                    }
                    else {
                        INFO("propagator not executed");
                        REQUIRE(a.value(3) != Potassco::TruthValue::free);
                    }
                }
            };
            other.onUndo = undoCb;
            prop.onCheck = [&](const auto& a, PropagatorControl& ctl) {
                if (enable && a.value(3) == Potassco::TruthValue::free) {
                    Potassco::Lit_t c = -3;
                    REQUIRE_FALSE(ctl.addClause(Potassco::toSpan(c)));
                }
            };
            libclasp.prepare();
            CHECK(libclasp.solve().sat());
            CAPTURE(undoError);
            REQUIRE(undoError.empty());
        }
    }
    SECTION("test push variables") {
        uint32_t        aux = 2;
        Potassco::Lit_t next{1};
        prop.onPropagate = [&](const auto& as, PropagatorControl& ctl, auto) {
            if (aux) {
                while (as.hasLit(next)) { ++next; }
                auto x = ctl.addVariable();
                REQUIRE(x == next);
                REQUIRE((not ctl.hasWatch(x) && not ctl.hasWatch(-x)));
                ctl.addWatch(x);
                REQUIRE((ctl.hasWatch(x) && not ctl.hasWatch(-x)));
                ctl.addWatch(-x);
                REQUIRE((ctl.hasWatch(x) && ctl.hasWatch(-x)));
                ctl.removeWatch(x);
                REQUIRE((not ctl.hasWatch(x) && ctl.hasWatch(-x)));
                ctl.removeWatch(-x);
                REQUIRE((not ctl.hasWatch(x) && not ctl.hasWatch(-x)));
                ctl.addWatch(x);
                ctl.addWatch(-x);
                --aux;
            }
        };
        auto& asp = libclasp.startAsp(config, true);
        libclasp.registerPropagator(prop, false);
        lpAdd(asp, "{x1;x2}.");
        prop.initWatches = {posLit(1), negLit(1), posLit(2), negLit(2)};
        SECTION("only during solving") {
            libclasp.prepare();
            uint32_t nv = libclasp.ctx.numVars();
            uint32_t sv = libclasp.ctx.master()->numVars();
            REQUIRE(nv == 3); // x1, x2 + step var
            REQUIRE(sv == 3);
            libclasp.solve();
            REQUIRE(nv == libclasp.ctx.numVars());
            REQUIRE(sv == libclasp.ctx.master()->numVars());
        }
        SECTION("also during init") {
            asp.endProgram();
            libclasp.ctx.addUnary(posLit(1));
            libclasp.prepare();
            uint32_t nv = libclasp.ctx.numVars();
            uint32_t sv = libclasp.ctx.master()->numVars();
            REQUIRE(nv == 3); // x1, x2 + step var
            REQUIRE(sv == 4);
            REQUIRE(libclasp.ctx.stepLiteral().var() == 3);
            libclasp.solve();
            REQUIRE(nv == libclasp.ctx.numVars());
            REQUIRE(nv == libclasp.ctx.master()->numVars());
        }
    }
    SECTION("testAuxVarMakesClauseVolatile") {
        bool            nextStep = false;
        Potassco::Lit_t aux      = 0;
        prop.onPropagate         = [&](const auto& a, PropagatorControl& ctl, auto) {
            if (not aux) {
                aux = ctl.addVariable();
                Potassco::LitVec clause;
                for (auto i : irange(1, aux)) {
                    if (ctl.hasWatch(i)) {
                        clause.push_back(-i);
                    }
                }
                clause.push_back(-aux);
                REQUIRE(ctl.addClause(clause, Potassco::ClauseType::locked));
            }
            REQUIRE((not nextStep || not a.hasLit(aux)));
        };
        auto& asp = libclasp.startAsp(config, true);
        libclasp.registerPropagator(prop, false);
        lpAdd(asp, "{x1;x2}.");
        prop.initWatches      = {posLit(1), posLit(2)};
        prop.clearInitWatches = true;
        LitVec assume;
        libclasp.prepare();
        assume.push_back(posLit(1));
        assume.push_back(posLit(2));
        libclasp.solve(assume);
        libclasp.update();
        nextStep = true;
        libclasp.solve(assume);
    }
    SECTION("testRootLevelBug") {
        prop.onPropagate = [&](const auto& as, PropagatorControl& ctl, auto) {
            REQUIRE(as.level() != 0);
            for (auto a : irange(2u, 4u)) {
                auto            pos = Potassco::lit(a);
                Potassco::Lit_t neg = -pos;
                if (not ctl.addClause({&pos, 1u})) {
                    return;
                }
                if (not ctl.addClause({&neg, 1u})) {
                    return;
                }
            }
        };
        auto& asp = libclasp.startAsp(config, true);
        libclasp.registerPropagator(prop, false);
        lpAdd(asp, "{x1;x2}.");
        prop.initWatches = {posLit(1), negLit(1), posLit(2), negLit(2)};
        libclasp.prepare();
        REQUIRE(libclasp.solve().unsat());
    }
    SECTION("testRelocationBug") {
        prop.onPropagate = [&](const auto& a, PropagatorControl& ctl, auto changes) {
            Potassco::LitVec cmp(begin(changes), end(changes));
            Potassco::LitVec clause;
            clause.assign(1, 0);
            for (uint32_t i = 1; i <= a.level(); ++i) { clause.push_back(-a.decision(i)); }
            for (Potassco::Lit_t lit = 1; a.hasLit(lit); ++lit) {
                if (a.value(lit) == Potassco::TruthValue::free) {
                    clause[0] = lit;
                    REQUIRE(ctl.addClause(clause));
                    ctl.propagate();
                }
            }
            REQUIRE(std::memcmp(cmp.data(), changes.data(), changes.size() * sizeof(Potassco::Lit_t)) == 0);
        };
        auto& asp = libclasp.startAsp(config, true);
        libclasp.registerPropagator(prop, false);
        lpAdd(asp, "{x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15;x16}.");
        asp.endProgram();
        for (auto v : libclasp.ctx.vars()) {
            prop.initWatches.push_back(posLit(v));
            prop.initWatches.push_back(negLit(v));
        }
        libclasp.prepare();
        REQUIRE(libclasp.solve().sat());
    }
    SECTION("testAddWeightConstraint") {
        config.solve.numModels = 0;
        auto& asp              = libclasp.startAsp(config, true);
        libclasp.registerPropagator(prop, false);
        lpAdd(asp, "{x1;x2;x3;x4}.");
        asp.endProgram();
        prop.onInit = [](const auto&, PropagatorInit& init) {
            init.setCheckMode(Potassco::PropagatorCheckMode::fixpoint);
        };
        bool fire = true;
        SECTION("simple") {
            prop.onCheck = [&](const Potassco::AbstractAssignment& a, auto& ctl) {
                if (a.level() == 0) {
                    REQUIRE(ctl.addWeightConstraint(encodeLit(lit_true),
                                                    std::array{Potassco::WeightLit{2, 1}, Potassco::WeightLit{3, 1},
                                                               Potassco::WeightLit{4, 1}, Potassco::WeightLit{5, 1}},
                                                    3, 0));
                }
            };
            REQUIRE(libclasp.solve().sat());
            REQUIRE(libclasp.summary().numEnum == 5);
        }
        SECTION("with backtracking") {
            fire         = false;
            prop.onCheck = [&](const Potassco::AbstractAssignment&, auto& ctl) {
                if (std::exchange(fire, false)) {
                    REQUIRE_FALSE(
                        ctl.addWeightConstraint(encodeLit(lit_true),
                                                std::array{Potassco::WeightLit{2, 1}, Potassco::WeightLit{3, 1},
                                                           Potassco::WeightLit{4, 1}, Potassco::WeightLit{5, 1}},
                                                3, 0));
                }
            };
            libclasp.prepare();
            REQUIRE((libclasp.ctx.master()->assume(negLit(1)) && libclasp.ctx.master()->propagate()));
            REQUIRE((libclasp.ctx.master()->assume(negLit(2)) && libclasp.ctx.master()->propagate()));
            fire = true;
            REQUIRE((libclasp.ctx.master()->assume(negLit(3)) && libclasp.ctx.master()->propagate()));
            REQUIRE(libclasp.ctx.master()->decisionLevel() == 1);
            libclasp.ctx.master()->undoUntil(0);
            REQUIRE(libclasp.solve().sat());
            REQUIRE(libclasp.summary().numEnum == 5);
        }
        SECTION("with conflict") {
            fire         = false;
            prop.onCheck = [&](const Potassco::AbstractAssignment&, auto& ctl) {
                if (std::exchange(fire, false)) {
                    REQUIRE_FALSE(ctl.addWeightConstraint(
                        encodeLit(negLit(1)),
                        std::array{Potassco::WeightLit{3, 1}, Potassco::WeightLit{4, 1}, Potassco::WeightLit{5, 1}}, 1,
                        0));
                }
            };
            libclasp.prepare();
            REQUIRE((libclasp.ctx.master()->assume(posLit(1)) && libclasp.ctx.master()->propagate()));
            fire = true;
            libclasp.ctx.master()->force(posLit(3), negLit(1));
            REQUIRE_FALSE(libclasp.ctx.master()->propagate());
            libclasp.ctx.master()->undoUntil(0);
            REQUIRE(libclasp.solve().sat());
            REQUIRE(libclasp.summary().numEnum == 8);
        }
        SECTION("with aux") {
            prop.onCheck = [&](const Potassco::AbstractAssignment&, auto& ctl) {
                if (std::exchange(fire, false)) {
                    auto con = ctl.addVariable();
                    REQUIRE(ctl.addWeightConstraint(con,
                                                    std::array{Potassco::WeightLit{2, 1}, Potassco::WeightLit{3, 1},
                                                               Potassco::WeightLit{4, 1}, Potassco::WeightLit{5, 1}},
                                                    3, 0));
                    REQUIRE(ctl.addClause(Potassco::toSpan(con)));
                }
            };
            REQUIRE(libclasp.solve().sat());
            REQUIRE(libclasp.summary().numEnum == 5);
            REQUIRE(libclasp.update());
            REQUIRE(libclasp.solve().sat());
            REQUIRE(libclasp.summary().numEnum == 16);
        }
        SECTION("ignore sat") {
            prop.onCheck = [&](const Potassco::AbstractAssignment&, auto& ctl) {
                if (std::exchange(fire, false)) {
                    REQUIRE(ctl.addWeightConstraint(encodeLit(lit_true),
                                                    std::array{Potassco::WeightLit{2, 1},
                                                               Potassco::WeightLit{encodeLit(lit_true), 1},
                                                               Potassco::WeightLit{encodeLit(lit_true), 1}},
                                                    1, 0));
                }
            };
            REQUIRE(libclasp.prepare());
            REQUIRE_FALSE(fire);
            auto* pp = libclasp.ctx.master()->getPost<ClingoPropagator>();
            REQUIRE(pp);
            REQUIRE(pp->numConstraints() == 0u);
        }
        SECTION("fail unsat") {
            prop.onCheck = [&](const Potassco::AbstractAssignment&, auto& ctl) {
                if (std::exchange(fire, false)) {
                    REQUIRE_FALSE(ctl.addWeightConstraint(encodeLit(lit_true),
                                                          std::array{Potassco::WeightLit{2, 1},
                                                                     Potassco::WeightLit{encodeLit(lit_false), 1},
                                                                     Potassco::WeightLit{encodeLit(lit_false), 1}},
                                                          2, 0));
                }
            };
            REQUIRE(libclasp.prepare());
            REQUIRE_FALSE(fire);
            REQUIRE_FALSE(libclasp.ctx.ok());
            auto* pp = libclasp.ctx.master()->getPost<ClingoPropagator>();
            REQUIRE(pp);
            REQUIRE(pp->numConstraints() == 0u);
        }
    }

    SECTION("test check mode") {
        int  last{0};
        int  props{0};
        int  checks{0};
        int  totals{0};
        bool makeTotal   = false;
        prop.onPropagate = [&](const auto& a, PropagatorControl& ctl, auto c) {
            REQUIRE_FALSE(c.empty());
            ++props;
            if (c.front() == last) {
                return;
            }
            for (int x = c.front() + 1; a.hasLit(x); ++x) {
                if (a.value(x) == Potassco::TruthValue::free) {
                    last = x;
                    REQUIRE(ctl.addClause({&x, 1u}));
                    break;
                }
            }
        };
        prop.onCheck = [&](const auto& a, PropagatorControl& ctl) {
            ++checks;
            totals += a.isTotal();
            if (makeTotal && not a.isTotal()) {
                for (int x = 1; a.hasLit(x); ++x) {
                    if (a.value(x) == Potassco::TruthValue::free) {
                        REQUIRE(ctl.addClause({&x, 1u}));
                        return;
                    }
                }
                REQUIRE(a.isTotal());
                REQUIRE(a.level() == 0);
                ++totals;
            }
        };

        auto& asp = libclasp.startAsp(config);
        libclasp.registerPropagator(prop, false);
        lpAdd(asp, "{x1;x2;x3;x4;x5}.");
        asp.endProgram();
        SECTION("test check and propagate") {
            makeTotal   = true;
            prop.onInit = [&](const auto&, PropagatorInit& init) {
                init.setCheckMode(Potassco::PropagatorCheckMode::fixpoint);
                init.addWatch(init.solverLiteral(1));
                init.addWatch(init.solverLiteral(2));
                init.addWatch(init.solverLiteral(3));
                init.addWatch(init.solverLiteral(4));
                init.addWatch(init.solverLiteral(5));
            };
            libclasp.prepare();
            REQUIRE(libclasp.ctx.master()->numFreeVars() == 0);
            REQUIRE(totals == 1);
            REQUIRE(checks > 1);
        }
        SECTION("test check is called only once per fixpoint") {
            auto expectedUndos = 0u;
            auto undoMode      = Potassco::PropagatorUndoMode::def;
            prop.onInit        = [&](const auto&, PropagatorInit& init) {
                init.setCheckMode(Potassco::PropagatorCheckMode::fixpoint);
                init.setUndoMode(undoMode);
            };
            SECTION("fixpoint default undo") { expectedUndos = 0; }
            SECTION("fixpoint always undo") {
                undoMode      = Potassco::PropagatorUndoMode::always;
                expectedUndos = 1;
            }
            libclasp.prepare();
            REQUIRE(checks == 1u);
            libclasp.ctx.master()->propagate();
            REQUIRE(checks == 1u);
            libclasp.ctx.master()->pushRoot(posLit(1));
            REQUIRE(checks == 2u);
            libclasp.ctx.master()->assume(posLit(2)) && libclasp.ctx.master()->propagate();
            REQUIRE(checks == 3u);
            libclasp.ctx.master()->propagate();
            REQUIRE(checks == 3u);
            libclasp.ctx.master()->restart();
            REQUIRE(prop.undos == expectedUndos);
            libclasp.ctx.master()->propagate();
            INFO("Restart introduces new fix point");
            REQUIRE(checks == 4u);
        }
        SECTION("with mode total check is called once on total") {
            auto expectedUndos = 0u;
            auto undoMode      = Potassco::PropagatorUndoMode::def;
            prop.onInit        = [&](const auto&, PropagatorInit& init) {
                init.setCheckMode(Potassco::PropagatorCheckMode::total);
                init.setUndoMode(undoMode);
            };
            SECTION("total default undo") { expectedUndos = 0; }
            SECTION("total always undo") {
                undoMode      = Potassco::PropagatorUndoMode::always;
                expectedUndos = 1;
            }
            libclasp.solve();
            libclasp.ctx.master()->undoUntil(0);
            REQUIRE(checks == 1u);
            REQUIRE(totals == 1u);
            REQUIRE(prop.undos == expectedUndos);
        }
        SECTION("with mode fixpoint check is called once on total") {
            prop.onInit = [&](const auto&, PropagatorInit& init) {
                init.setCheckMode(Potassco::PropagatorCheckMode::fixpoint);
            };
            libclasp.solve();
            REQUIRE(std::cmp_greater(checks, 1));
            REQUIRE(totals == 1u);
        }
    }
}

TEST_CASE("Clingo propagator init", "[facade][propagator]") {
    using MyInit = ClingoPropagatorInit;

    PropagatorTest test;
    SharedContext& ctx = test.ctx;
    TestPropagator prop;
    MyInit         init(ctx, prop, nullptr);

    test.addVars(5);
    Solver& s0 = *ctx.master();

    SECTION("add watches") {
        init.addWatch(posLit(1));
        init.addWatch(posLit(2));
        init.addWatch(posLit(4));
        init.addPropagator(s0);
        REQUIRE(init.hasWatch(encodeLit(posLit(1))));
        REQUIRE(init.hasWatch(encodeLit(posLit(4))));
        REQUIRE_FALSE(init.hasWatch(encodeLit(posLit(3))));
        ctx.endInit();
        auto* pp = s0.getPost(PostPropagator::priority_class_general);
        REQUIRE(s0.hasWatch(posLit(1), pp));
        REQUIRE(s0.hasWatch(posLit(2), pp));
        REQUIRE(s0.hasWatch(posLit(4), pp));
        REQUIRE_FALSE(s0.hasWatch(posLit(3), pp));

        REQUIRE(test.isFrozen(posLit(1)));
        REQUIRE(test.isFrozen(posLit(2)));
        REQUIRE(test.isFrozen(posLit(4)));
        REQUIRE_FALSE(test.isFrozen(posLit(3)));
    }

    SECTION("add propagator only once") {
        init.addWatch(posLit(1));
        init.addPropagator(s0);
        init.addPropagator(s0);
        ctx.endInit();
        auto* pp = s0.getPost(PostPropagator::priority_class_general);
        REQUIRE(pp->next == nullptr);
        ctx.unfreeze();
        init.unfreeze();

        init.addPropagator(s0);
        ctx.endInit();
        REQUIRE(s0.getPost(PostPropagator::priority_class_general) == pp);
        REQUIRE(pp->next == nullptr);
    }

    SECTION("freezeLit") {
        init.addWatch(posLit(1));
        REQUIRE(init.hasWatch(encodeLit(posLit(1))));
        init.removeWatch(posLit(1));
        REQUIRE_FALSE(init.hasWatch(encodeLit(posLit(1))));
        init.freezeLit(posLit(1));
        init.addPropagator(s0);
        ctx.endInit();
        auto* pp = s0.getPost(PostPropagator::priority_class_general);
        REQUIRE_FALSE(s0.hasWatch(posLit(1), pp));
        REQUIRE(test.isFrozen(posLit(1)));
    }

    SECTION("init acquires all problem vars") {
        auto v = ctx.addVar(VarType::atom);
        init.addWatch(posLit(v));
        init.addPropagator(s0);
        ctx.endInit();
        auto* pp = s0.getPost(PostPropagator::priority_class_general);
        REQUIRE(s0.hasWatch(posLit(v), pp));
    }

    SECTION("ignore duplicate watches from init") {
        init.addWatch(posLit(1));
        init.addWatch(posLit(1));
        init.addPropagator(s0);
        ctx.endInit();
        auto* pp = s0.getPost(PostPropagator::priority_class_general);
        REQUIRE(s0.hasWatch(posLit(1), pp));
        s0.removeWatch(posLit(1), pp);
        REQUIRE_FALSE(s0.hasWatch(posLit(1), pp));
    }

    SECTION("ignore duplicates on solver-specific init") {
        init.addWatch(posLit(1));
        prop.onAttach = [](const auto&, PropagatorControl& ctl) { ctl.addWatch(encodeLit(posLit(1))); };
        init.addPropagator(s0);
        ctx.endInit();
        auto* pp = s0.getPost(PostPropagator::priority_class_general);
        REQUIRE(s0.hasWatch(posLit(1), pp));
        s0.removeWatch(posLit(1), pp);
        REQUIRE_FALSE(s0.hasWatch(posLit(1), pp));
    }

    SECTION("add solver-specific watches") {
        Solver& s1 = ctx.pushSolver();
        init.addWatch(posLit(1)); // add to both
        init.freezeLit(posLit(2));
        prop.onAttach = [](const auto& assignment, PropagatorControl& ctl) {
            if (auto id = assignment.solverId(); id == 0) {
                ctl.addWatch(encodeLit(posLit(2)));
            }
            else {
                ctl.addWatch(encodeLit(posLit(3)));
            }
        };
        init.addPropagator(s0);
        init.addPropagator(s1);
        ctx.endInit(true);

        auto* pp0 = s0.getPost(PostPropagator::priority_class_general);
        auto* pp1 = s1.getPost(PostPropagator::priority_class_general);
        REQUIRE(s0.hasWatch(posLit(1), pp0));
        REQUIRE(s1.hasWatch(posLit(1), pp1));

        REQUIRE(s0.hasWatch(posLit(2), pp0));
        REQUIRE_FALSE(s1.hasWatch(posLit(2), pp1));

        REQUIRE_FALSE(s0.hasWatch(posLit(3), pp0));
        REQUIRE(s1.hasWatch(posLit(3), pp1));

        REQUIRE(test.isFrozen(posLit(1)));
        REQUIRE(test.isFrozen(posLit(2)));
        REQUIRE_FALSE(test.isFrozen(posLit(3)));
    }

    SECTION("don't add removed watch") {
        Solver& s1 = ctx.pushSolver();
        init.addWatch(posLit(1));
        init.addWatch(posLit(2));
        init.addWatch(posLit(3));
        prop.onAttach = [](const auto& assignment, PropagatorControl& ctl) {
            if (assignment.solverId() == 1) {
                ctl.removeWatch(encodeLit(posLit(2)));
            }
        };
        // S0: [1,2,3]
        // S1: [1, ,3]
        init.addPropagator(s0);
        init.addPropagator(s1);
        ctx.endInit(true);

        auto* pp0 = s0.getPost(PostPropagator::priority_class_general);
        auto* pp1 = s1.getPost(PostPropagator::priority_class_general);
        REQUIRE(s0.hasWatch(posLit(1), pp0));
        REQUIRE(s0.hasWatch(posLit(2), pp0));
        REQUIRE(s0.hasWatch(posLit(3), pp0));

        REQUIRE(s1.hasWatch(posLit(1), pp1));
        REQUIRE_FALSE(s1.hasWatch(posLit(2), pp1));
        REQUIRE(s1.hasWatch(posLit(3), pp1));

        REQUIRE(test.isFrozen(posLit(1)));
        REQUIRE(test.isFrozen(posLit(2)));
        REQUIRE(test.isFrozen(posLit(3)));
        ctx.unfreeze();
        init.unfreeze();

        init.addWatch(posLit(4));
        ctx.endInit(true);
        REQUIRE(s0.hasWatch(posLit(4), pp0));
        REQUIRE(s1.hasWatch(posLit(4), pp1));
        REQUIRE_FALSE(s1.hasWatch(posLit(2), pp0));
    }

    SECTION("last call wins") {
        init.addWatch(posLit(1));
        init.removeWatch(posLit(1));
        init.addWatch(posLit(1));
        init.addPropagator(s0);
        ctx.endInit();
        auto* pp = s0.getPost(PostPropagator::priority_class_general);
        REQUIRE(s0.hasWatch(posLit(1), pp));
        REQUIRE(test.isFrozen(posLit(1)));
    }

    SECTION("watched facts") {
        LitVec changes;
        prop.onPropagate = [&](const auto&, const auto&, Potassco::AbstractPropagator::ChangeList cl) {
            for (auto lit : cl) { changes.push_back(decodeLit(lit)); }
        };
        init.addWatch(posLit(1));
        ctx.startAddConstraints();
        ctx.addUnary(posLit(1));
        SECTION("are propagated") {
            init.addPropagator(s0);
            ctx.endInit();
            auto* pp = s0.getPost(PostPropagator::priority_class_general);
            REQUIRE(changes == LitVec{posLit(1)});
            REQUIRE_FALSE(s0.hasWatch(posLit(1), pp));
        }
        SECTION("be watched even after propagate") {
            s0.propagate();
            init.addPropagator(s0);
            ctx.endInit();
            auto* pp = s0.getPost(PostPropagator::priority_class_general);
            REQUIRE(changes == LitVec{posLit(1)});
            REQUIRE_FALSE(s0.hasWatch(posLit(1), pp));
            REQUIRE(test.isFrozen(posLit(1)));
        }
        SECTION("are propagated only once") {
            init.addPropagator(s0);
            ctx.endInit();
            changes.clear();
            ctx.unfreeze();
            init.unfreeze();
            ctx.startAddConstraints();
            ctx.addUnary(posLit(2));
            init.addWatch(posLit(1));
            init.addWatch(posLit(2));
            ctx.endInit();
            REQUIRE(changes == LitVec{posLit(2)});
        }
    }

    SECTION("init keeps history so that future solvers get correct watches") {
        Solver& s1 = ctx.pushSolver();
        // S0: [1,2,3]
        // S1: [1, ,3]
        init.addWatch(posLit(1));
        init.addWatch(posLit(2));
        init.addWatch(posLit(3));
        prop.onAttach = [](const auto& a, PropagatorControl& ctl) {
            if (auto id = a.solverId(); id == 1 || id == 2) {
                ctl.removeWatch(encodeLit(posLit(id + 1)));
            }
        };
        init.addPropagator(s0);
        init.addPropagator(s1);
        ctx.endInit(true);
        ctx.unfreeze();
        init.unfreeze();
        Solver& s2 = ctx.pushSolver();
        ctx.startAddConstraints();
        init.addWatch(posLit(4));
        init.addWatch(posLit(5));
        init.removeWatch(posLit(1));
        init.addPropagator(s2);
        ctx.endInit(true);
        auto* pp2 = s2.getPost(PostPropagator::priority_class_general);
        REQUIRE_FALSE(s2.hasWatch(posLit(1), pp2));
        REQUIRE(s2.hasWatch(posLit(2), pp2));
        REQUIRE_FALSE(s2.hasWatch(posLit(3), pp2));
        REQUIRE(s2.hasWatch(posLit(4), pp2));
        REQUIRE(s2.hasWatch(posLit(5), pp2));

        auto* pp0 = s0.getPost(PostPropagator::priority_class_general);
        REQUIRE_FALSE(s0.hasWatch(posLit(1), pp0));

        ctx.unfreeze();
        init.unfreeze();

        Solver& s3 = ctx.pushSolver();
        auto    x  = ctx.addVar(VarType::atom);
        ctx.startAddConstraints();
        init.addWatch(posLit(x));
        init.addPropagator(s3);
        ctx.endInit(true);

        auto* pp3 = s3.getPost(PostPropagator::priority_class_general);
        REQUIRE_FALSE(s3.hasWatch(posLit(1), pp3));
        REQUIRE(s3.hasWatch(posLit(2), pp3));
        REQUIRE(s3.hasWatch(posLit(3), pp3));
        REQUIRE(s3.hasWatch(posLit(4), pp3));
        REQUIRE(s3.hasWatch(posLit(5), pp3));

        REQUIRE(s0.hasWatch(posLit(x), pp0));
        REQUIRE(s2.hasWatch(posLit(x), pp2));
        REQUIRE(s3.hasWatch(posLit(x), pp3));
    }

    SECTION("test init-solve interplay") {
        LitVec add;
        LitVec remove;
        prop.onCheck = [&](const auto&, PropagatorControl& ctl) {
            while (not add.empty()) {
                ctl.addWatch(encodeLit(add.back()));
                add.pop_back();
            }
            while (not remove.empty()) {
                ctl.removeWatch(encodeLit(remove.back()));
                remove.pop_back();
            }
        };
        MyInit pp(ctx, prop, nullptr);
        pp.setCheckMode(Potassco::PropagatorCheckMode::fixpoint);

        SECTION("ignore watches already added in init") {
            pp.addWatch(posLit(1));
            add.push_back(posLit(1));
            pp.addPropagator(s0);
            ctx.endInit();
            auto* post = s0.getPost(PostPropagator::priority_class_general);
            REQUIRE(s0.hasWatch(posLit(1), post));
            REQUIRE(add.empty());
            s0.removeWatch(posLit(1), post);
            REQUIRE_FALSE(s0.hasWatch(posLit(1), post));
        }

        SECTION("ignore watches in init already added during solving") {
            add.push_back(posLit(1));
            pp.addPropagator(s0);
            ctx.endInit();
            auto* post = s0.getPost(PostPropagator::priority_class_general);
            REQUIRE(add.empty());
            ctx.unfreeze();
            pp.unfreeze();
            ctx.startAddConstraints();
            pp.addWatch(posLit(1));
            pp.addWatch(posLit(2));
            ctx.endInit();
            REQUIRE(s0.hasWatch(posLit(1), post));
            REQUIRE(s0.hasWatch(posLit(2), post));
            s0.removeWatch(posLit(1), post);
            REQUIRE_FALSE(s0.hasWatch(posLit(1), post));
        }

        SECTION("remove watch during solving") {
            pp.addWatch(posLit(1));
            remove.push_back(posLit(1));
            pp.addPropagator(s0);
            ctx.endInit();
            auto* post = s0.getPost(PostPropagator::priority_class_general);
            ctx.unfreeze();
            pp.unfreeze();
            ctx.startAddConstraints();
            ctx.endInit();
            REQUIRE_FALSE(s0.hasWatch(posLit(1), post));
        }

        SECTION("remove watch during solving then add on init") {
            pp.addWatch(posLit(1));
            remove.push_back(posLit(1));
            pp.addPropagator(s0);
            ctx.endInit();
            auto* post = s0.getPost(PostPropagator::priority_class_general);
            ctx.unfreeze();
            pp.unfreeze();
            REQUIRE_FALSE(s0.hasWatch(posLit(1), post));
            pp.addWatch(posLit(1));
            ctx.startAddConstraints();
            ctx.endInit();
            REQUIRE(s0.hasWatch(posLit(1), post));
        }

        SECTION("add watch during solving then remove on init") {
            add.push_back(posLit(1));
            pp.addPropagator(s0);
            ctx.endInit();
            auto* post = s0.getPost(PostPropagator::priority_class_general);
            ctx.unfreeze();
            pp.unfreeze();
            REQUIRE(s0.hasWatch(posLit(1), post));
            pp.removeWatch(posLit(1));
            ctx.startAddConstraints();
            ctx.endInit();
            REQUIRE_FALSE(s0.hasWatch(posLit(1), post));
        }
    }
    SECTION("with sat preprocessing") {
        ClaspConfig config;
        config.satPre.type = SatPreParams::sat_pre_full;
        ctx.setConfiguration(&config);
        REQUIRE(ctx.validVar(4));
        ctx.startAddConstraints();
        REQUIRE(ctx.addBinary(posLit(1), posLit(2)));
        REQUIRE(ctx.master()->value(1) == value_free);
        REQUIRE(ctx.master()->value(2) == value_free);
        REQUIRE(ctx.addUnary(negLit(2)));
        REQUIRE(ctx.master()->value(1) == value_free);
        REQUIRE(ctx.addBinary(posLit(3), posLit(4)));
        REQUIRE(ctx.master()->value(3) == value_free);
        REQUIRE(ctx.master()->value(4) == value_free);

        init.addPropagator(*ctx.master());

        SECTION("assignment is fully propagated on init") {
            prop.onInit = [&](const Potassco::AbstractAssignment& a, PropagatorInit&) {
                REQUIRE_FALSE(a.hasConflict());
                REQUIRE(a.value(encodeLit(posLit(2))) == Potassco::TruthValue::false_);
                REQUIRE(a.value(encodeLit(posLit(1))) == Potassco::TruthValue::true_);
            };
            REQUIRE(ctx.endInit());
            REQUIRE(prop.inits == 1);
        }
        SECTION("new clauses are propagated") {
            prop.onInit = [&](const Potassco::AbstractAssignment& a, PropagatorInit& ctrl) {
                REQUIRE(a.value(encodeLit(posLit(3))) == Potassco::TruthValue::free);
                REQUIRE(a.value(encodeLit(posLit(4))) == Potassco::TruthValue::free);

                auto unit = encodeLit(negLit(3));
                REQUIRE(ctrl.addClause(Potassco::toSpan(unit)));
                REQUIRE(a.value(encodeLit(posLit(4))) == Potassco::TruthValue::free);

                REQUIRE(ctrl.propagate());
                REQUIRE(a.value(encodeLit(posLit(3))) == Potassco::TruthValue::false_);
                REQUIRE(a.value(encodeLit(posLit(4))) == Potassco::TruthValue::true_);
            };
            REQUIRE(ctx.endInit());
            REQUIRE(prop.inits == 1);
        }
    }
}

TEST_CASE("Clingo propagator init with facade", "[facade][propagator]") {
    ClaspConfig    config;
    ClaspFacade    libclasp;
    SharedContext& ctx = libclasp.ctx;
    SECTION("init acquires all problem vars") {
        TestPropagator prop1, prop2;
        auto&          asp = libclasp.startAsp(config);
        prop1.onInit       = [&](const auto&, PropagatorInit& init) {
            REQUIRE(libclasp.asp());
            init.addWatch(init.solverLiteral(1));
        };
        prop2.onInit = [&](const auto&, PropagatorInit& init) { init.addWatch(-init.solverLiteral(1)); };

        libclasp.registerPropagator(prop1, false);
        libclasp.registerPropagator(prop2, false);
        lpAdd(asp, "{x1}.");
        libclasp.prepare();
        auto    v  = Asp::solverLiteral(asp, 1);
        Solver& s0 = *ctx.master();
        auto*   pp = s0.getPost(PostPropagator::priority_class_general);
        REQUIRE(s0.hasWatch(v, pp));
        REQUIRE(pp->next != nullptr);
        REQUIRE(s0.hasWatch(~v, pp->next));
    }

    SECTION("init is called again on second solve") {
        TestPropagator prop;
        auto&          asp = libclasp.startAsp(config, true);
        libclasp.registerPropagator(prop, false);
        lpAdd(asp, "{x1}.");
        libclasp.solve();
        REQUIRE(prop.inits == 1);
        SECTION("without update") {
            libclasp.solve();
            REQUIRE(prop.inits == 2);
        }
        SECTION("with update") {
            libclasp.update();
            libclasp.solve();
            REQUIRE(prop.inits == 2);
        }
    }

    SECTION("init is not called on initial conflict") {
        TestPropagator prop;
        auto&          asp = libclasp.startAsp(config, true);
        libclasp.registerPropagator(prop, false);
        lpAdd(asp, "x1 :- not x1.");
        libclasp.prepare();
        REQUIRE(prop.inits == 0);
    }

    SECTION("with sat preprocessing") {
        TestPropagator prop;
        config.satPre.type = SatPreParams::sat_pre_full;
        auto& sat          = libclasp.startSat(config);
        libclasp.registerPropagator(prop, false);
        sat.prepareProblem(4);
        REQUIRE(libclasp.ctx.validVar(4));
        LitVec clause = {posLit(1), posLit(2)};
        sat.addClause(clause);
        clause = {negLit(2)};
        sat.addClause(clause);
        clause = {posLit(3), posLit(4)};
        sat.addClause(clause);
        SECTION("assignment is fully propagated on init") {
            prop.onInit = [&](const Potassco::AbstractAssignment& a, PropagatorInit&) {
                REQUIRE_FALSE(a.hasConflict());
                REQUIRE(a.size() == 5);
                REQUIRE(a.value(encodeLit(posLit(2))) == Potassco::TruthValue::false_);
                REQUIRE(a.value(encodeLit(posLit(1))) == Potassco::TruthValue::true_);
            };
            libclasp.prepare();
            REQUIRE(prop.inits == 1);
        }
        SECTION("new clauses are propagated") {
            prop.onInit = [&](const Potassco::AbstractAssignment& a, PropagatorInit& init) {
                REQUIRE(a.value(encodeLit(posLit(3))) == Potassco::TruthValue::free);
                REQUIRE(a.value(encodeLit(posLit(4))) == Potassco::TruthValue::free);

                auto unit = encodeLit(negLit(3));
                REQUIRE(init.addClause(Potassco::toSpan(unit)));
                REQUIRE(a.value(encodeLit(posLit(4))) == Potassco::TruthValue::free);

                REQUIRE(init.propagate());
                REQUIRE(a.value(encodeLit(posLit(3))) == Potassco::TruthValue::false_);
                REQUIRE(a.value(encodeLit(posLit(4))) == Potassco::TruthValue::true_);
            };
            libclasp.prepare();
            REQUIRE(prop.inits == 1);
        }
    }

    SECTION("map literal") {
        TestPropagator prop;
        auto&          asp = libclasp.startAsp(config, true);
        libclasp.registerPropagator(prop, false);
        lpAdd(asp, "{x1, x3}. x2 :- x1, x3.");
        prop.onInit = [&](const auto&, const PropagatorInit& init) {
            REQUIRE(init.solverLiteral(1) == encodeLit(asp.getLiteral(1)));
            REQUIRE(init.solverLiteral(2) == encodeLit(asp.getLiteral(2)));
            REQUIRE(init.solverLiteral(3) == encodeLit(asp.getLiteral(3)));
            REQUIRE(init.solverLiteral(4) == encodeLit(lit_false));
        };
        libclasp.prepare();
    }

    SECTION("add variable") {
        TestPropagator prop;
        libclasp.startAsp(config);
        libclasp.registerPropagator(prop, false);
        Var_t lit1 = 0, lit2 = 0;
        prop.onInit = [&](const auto&, PropagatorInit& init) {
            lit1 = decodeLit(init.addVariable(false)).var();
            lit2 = decodeLit(init.addVariable(true)).var();
        };
        libclasp.prepare();
        REQUIRE(lit1 != 0);
        REQUIRE(lit2 > lit1);
        REQUIRE_FALSE(ctx.varInfo(lit1).frozen());
        REQUIRE(ctx.varInfo(lit2).frozen());
    }
    SECTION("add clause") {
        TestPropagator prop;
        libclasp.startAsp(config, true);
        libclasp.registerPropagator(prop, false);
        prop.onInit = [&](const auto&, PropagatorInit& init) {
            auto l1 = init.addVariable(false);
            auto l2 = init.addVariable(false);
            auto l3 = init.addVariable(false);
            REQUIRE(init.addClause(std::array{l1, l2}));
            REQUIRE(init.addClause(std::array{-l1, -l2, -l2})); // Duplicate literal: should be removed
            REQUIRE(init.addClause(std::array{l1, -l1, l2}));   // Taut: should be removed
            REQUIRE(init.addClause(std::array{-l1, l3}, Potassco::ClauseType::transient));
        };
        libclasp.prepare();
        REQUIRE(ctx.stepLiteral().var() != 0);
        REQUIRE(ctx.numVars() == 4);
        CHECK(ctx.numBinary() == 2);
        CHECK(ctx.numTernary() == 1);
        CHECK(ctx.numConstraints() == 3);

        REQUIRE((ctx.master()->assume(ctx.stepLiteral()) && ctx.master()->propagate()));
        ctx.master()->assume(posLit(1)) && ctx.master()->propagate();
        REQUIRE(ctx.master()->isFalse(posLit(2)));
        REQUIRE(ctx.master()->isTrue(posLit(3)));

        prop.onInit = nullptr;
        libclasp.update();
        CHECK(ctx.numBinary() == 2);
        CHECK(ctx.numTernary() == 0);
        CHECK(ctx.numConstraints() == 2);

        libclasp.prepare();
        REQUIRE((ctx.master()->assume(ctx.stepLiteral()) && ctx.master()->propagate()));
        ctx.master()->assume(posLit(1)) && ctx.master()->propagate();
        REQUIRE(ctx.master()->isFalse(posLit(2)));
        REQUIRE(ctx.master()->value(3) == value_free);
    }

    SECTION("add weight constraint") {
        TestPropagator prop;
        libclasp.startAsp(config);
        libclasp.registerPropagator(prop, false);
        prop.onInit = [&](const auto&, PropagatorInit& init) {
            auto l1 = init.addVariable(false);
            auto l2 = init.addVariable(false);
            auto l3 = init.addVariable(false);
            auto l4 = init.addVariable(false);
            auto l5 = init.addVariable(false);
            REQUIRE(init.addWeightConstraint(l1,
                                             std::array{Potassco::WeightLit{l2, 1}, Potassco::WeightLit{l3, 1},
                                                        Potassco::WeightLit{l4, 1}, Potassco::WeightLit{l5, 1}},
                                             2, 0));
        };
        libclasp.prepare();
        REQUIRE(ctx.numVars() == 5);
        REQUIRE(ctx.numBinary() == 0);
        REQUIRE(ctx.numConstraints() == 1);
        ctx.master()->assume(posLit(1)) && ctx.master()->propagate();
        ctx.master()->assume(negLit(2)) && ctx.master()->propagate();
        ctx.master()->assume(negLit(4)) && ctx.master()->propagate();
        REQUIRE(ctx.master()->isTrue(posLit(3)));
        REQUIRE(ctx.master()->isTrue(posLit(5)));
    }
    SECTION("add minimize") {
        TestPropagator prop;
        libclasp.startAsp(config);
        libclasp.registerPropagator(prop, false);
        prop.onInit = [&](const auto&, PropagatorInit& init) {
            auto l1 = init.addVariable(false);
            auto l2 = init.addVariable(false);
            init.addMinimize(0, {l1, 1});
            init.addMinimize(0, {l2, 2});
        };
        libclasp.prepare();
        REQUIRE(ctx.numVars() == 2);
        REQUIRE(ctx.hasMinimize());
        REQUIRE(ctx.minimizeNoCreate());
        REQUIRE(ctx.minimizeNoCreate()->lits[0] == WeightLiteral{posLit(2), 2});
        REQUIRE(ctx.minimizeNoCreate()->lits[1] == WeightLiteral{posLit(1), 1});
        REQUIRE(ctx.minimizeNoCreate()->lits[2] == WeightLiteral{posLit(0), 0});
    }
    SECTION("propagate") {
        TestPropagator prop;
        libclasp.startAsp(config);
        libclasp.registerPropagator(prop, false);
        prop.onInit = [&](const auto& as, PropagatorInit& init) {
            auto l1 = init.addVariable(false);
            auto l2 = init.addVariable(false);
            REQUIRE(init.addClause(std::array{l1, l2}));
            REQUIRE(init.addClause(std::array{-l1, -l2}));
            REQUIRE(init.addClause(std::array{l1}));
            REQUIRE(as.isTrue(l1));
            REQUIRE(as.isFixed(l1));
            REQUIRE(as.value(l2) == Potassco::TruthValue::free);
            REQUIRE(init.propagate());
            REQUIRE(as.isTrue(l2));
            REQUIRE(as.isFixed(l2));
            REQUIRE(as.isTotal());

            auto l3 = init.addVariable(false);
            REQUIRE_FALSE(as.isTotal());
            REQUIRE(as.value(l3) == Potassco::TruthValue::free);
        };
    }
}

TEST_CASE("Clingo heuristic", "[facade][heuristic]") {
    class ClingoHeu : public Potassco::AbstractHeuristic {
    public:
        ClingoHeu() = default;
        Potassco::Lit_t decide(const Potassco::AbstractAssignment& assignment, Potassco::Lit_t fallback) override {
            REQUIRE_FALSE(assignment.isTotal());
            REQUIRE(assignment.value(fallback) == Potassco::TruthValue::free);
            fallbacks.push_back(fallback);
            for (auto i = Potassco::lit(Potassco::atom(fallback) + 1);; ++i) {
                if (not assignment.hasLit(i)) {
                    i = 1;
                }
                if (assignment.value(i) == Potassco::TruthValue::free) {
                    selected.push_back(Potassco::neg(i));
                    return selected.back();
                }
            }
        }
        Potassco::LitVec selected;
        Potassco::LitVec fallbacks;
    };
    ClaspConfig config;
    ClaspFacade libclasp;
    ClingoHeu   heuristic;
    SECTION("Clingo heuristic is called with fallback") {
        SolverParams& opts = config.addSolver(0);
        opts.heuId         = +HeuristicType::none;
        auto& asp          = libclasp.startAsp(config);
        libclasp.registerHeuristic(heuristic);
        lpAdd(asp, "{x1;x2;x3}.");
        asp.endProgram();
        libclasp.prepare();

        auto  fallback(createHeuristic(HeuristicType::none, HeuParams()));
        auto& s = *libclasp.ctx.master();

        while (s.numFreeVars() != 0) {
            Literal fb  = fallback->doSelect(s);
            auto    lit = s.heuristic()->doSelect(s);
            REQUIRE(lit == decodeLit(heuristic.selected.back()));
            REQUIRE(fb == decodeLit(heuristic.fallbacks.back()));
            s.assume(lit) && s.propagate();
        }

        REQUIRE(heuristic.selected.size() == s.numVars());
    }

    SECTION("Restricted lookahead decorates clingo heuristic") {
        SolverParams& opts = config.addSolver(0);
        opts.lookOps       = 2;
        opts.lookType      = 1;
        opts.heuId         = +HeuristicType::vsids;
        auto& asp          = libclasp.startAsp(config);
        libclasp.registerHeuristic(heuristic);
        lpAdd(asp, "{x1;x2;x3}.");
        asp.endProgram();
        libclasp.prepare();
        DecisionHeuristic* heu = libclasp.ctx.master()->heuristic();
        // heuristic is Restricted(Clingo(Vsids))
        REQUIRE(dynamic_cast<ClingoHeuristic*>(heu) == nullptr);
        REQUIRE(dynamic_cast<UnitHeuristic*>(heu) != nullptr);

        // Restricted does not forward to its decorated heuristic
        auto lit = heu->doSelect(*libclasp.ctx.master());
        REQUIRE(heuristic.fallbacks.empty());
        REQUIRE(heuristic.selected.empty());
        libclasp.ctx.master()->assume(lit);

        // Last lookahead operation - disables restricted heuristic
        libclasp.ctx.master()->propagate();

        // Restricted is no longer enabled and should remove itself on this call
        lit = heu->doSelect(*libclasp.ctx.master());
        REQUIRE(heuristic.fallbacks.size() == 1);
        REQUIRE(heuristic.selected.size() == 1);
        REQUIRE(heuristic.selected.back() == encodeLit(lit));
        REQUIRE(std::cmp_not_equal(heuristic.fallbacks.back(), heuristic.selected.size()));

        // From now on, we only have Clingo(Vsids)
        heu = libclasp.ctx.master()->heuristic();
        REQUIRE(dynamic_cast<ClingoHeuristic*>(heu));
        REQUIRE(dynamic_cast<ClaspVsids*>(dynamic_cast<ClingoHeuristic*>(heu)->fallback()));
    }
}

} // namespace Clasp::Test
