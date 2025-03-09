//
// Copyright (c) 2014-present Benjamin Kaufmann
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
#include <clasp/cli/clasp_options.h>
#include <clasp/logic_program.h>
#include <clasp/lookahead.h>
#include <clasp/unfounded_check.h>

#include <catch2/catch_test_macros.hpp>

#include <fstream>
namespace Clasp {
static bool operator==(const ScheduleStrategy& lhs, const ScheduleStrategy& rhs) {
    return lhs.type == rhs.type && lhs.base == rhs.base && lhs.len == rhs.len && lhs.grow == rhs.grow;
}
namespace Cli::Test {
static void traverseKey(const ClaspCliConfig& c, std::vector<std::string>& keys, ClaspCliConfig::KeyType k,
                        std::string accu) {
    if (k == ClaspCliConfig::key_invalid) {
        throw std::runtime_error("Invalid key");
    }
    if (ClaspCliConfig::isLeafKey(k)) {
        keys.push_back(accu);
    }
    else {
        if (not accu.empty()) {
            accu += '.';
        }
        std::size_t pop = accu.size();
        auto        i   = 0u;
        for (const char* x = nullptr; (x = c.getSubkey(k, i)) != nullptr; ++i, accu.resize(pop)) {
            accu += x;
            traverseKey(c, keys, c.getKey(k, x), accu);
        }
    }
}
static bool isValidOption(const ClaspCliConfig& c, const std::string& k) {
    return ClaspCliConfig::isLeafKey(c.getKey(ClaspCliConfig::key_root, k.c_str()));
}
static bool hasOption(const ClaspCliConfig& c, const std::string& o, const std::vector<std::string>& keys,
                      bool tester) {
    return contains(keys, o) || (tester && not isValidOption(c, o));
}
TEST_CASE("Cli options", "[cli]") {
    ClaspCliConfig config;
    std::string    val;
    REQUIRE(config.numSolver() == 1);
    REQUIRE(config.testerConfig() == 0);
    REQUIRE_FALSE(config.solve.limit.enabled());
    SECTION("test init from argv") {
        REQUIRE(config.solve.numSolver() == 1);
        REQUIRE(config.solve.numModels != 0);
        const char* argv[] = {"-n0", "--save-progress=20", "--stats", "--tester=--config=frumpy"};
        config.setConfig(argv, argv + (sizeof(argv) / sizeof(const char*)), ProblemType::asp);
        REQUIRE(config.getValue("configuration") == "auto");
        REQUIRE(config.getValue("asp.eq") == "3");
        REQUIRE(config.getValue("asp.trans_ext") == "dynamic");
        REQUIRE(config.solve.numSolver() == 1);
        REQUIRE(config.numSolver() == 1);
        REQUIRE(config.solve.numModels == 0);
        REQUIRE(config.solver(0).saveProgress == 20);
        REQUIRE(config.testerConfig());
        REQUIRE(config.testerConfig()->numSolver() == 1);
        REQUIRE(config.getValue("tester.configuration") == "frumpy");
    }
    SECTION("test init sat defaults") {
        SECTION("sat-pre is added") {
            const char* argv[] = {"--config=frumpy"};
            config.setConfig(argv, argv + (sizeof(argv) / sizeof(const char*)), ProblemType::sat);
            REQUIRE(config.getValue("sat_prepro") == "2,iter=20,occ=25,time=120,size=4000");
        }
        SECTION("explicit sat-pre wins") {
            SECTION("with keys") {
                const char* argv[] = {"--config=frumpy --sat-pre=2,iter=40,occ=50,time=300"};
                config.setConfig(argv, argv + (sizeof(argv) / sizeof(const char*)), ProblemType::sat);
            }
            SECTION("without keys") {
                const char* argv[] = {"--config=frumpy --sat-pre=2,40,50,300"};
                config.setConfig(argv, argv + (sizeof(argv) / sizeof(const char*)), ProblemType::sat);
            }
            REQUIRE(config.getValue("sat_prepro") == "2,iter=40,occ=50,time=300,size=4000");
        }
    }
    SECTION("test init") {
        ClaspCliConfig::KeyType initGen  = config.getKey(ClaspCliConfig::key_root, "configuration");
        ClaspCliConfig::KeyType initTest = config.getKey(ClaspCliConfig::key_tester, "configuration");
        REQUIRE((ClaspCliConfig::isLeafKey(initGen) && ClaspCliConfig::isLeafKey(initTest) && initTest != initGen));
        int         nSub, nArr, nVal;
        const char* help;
        config.getKeyInfo(initGen, &nSub, &nArr, &help, &nVal);
        REQUIRE((nSub == 0 && nArr == -1 && nVal == 1 && std::strstr(help, "frumpy") != nullptr));
        help = "";
        nArr = -2;
        config.getKeyInfo(initTest, &nSub, &nArr, &help, &nVal);
        REQUIRE((nSub == 0 && nArr == -1 && nVal == 0 && std::strstr(help, "tweety") != nullptr));

        REQUIRE(config.setValue("configuration", "many"));
        REQUIRE(config.numSolver() > 1);
        REQUIRE(config.testerConfig() == 0);
        REQUIRE(config.setValue("tester.configuration", "tweety"));
        REQUIRE(config.testerConfig() != 0);
        REQUIRE(config.testerConfig()->hasConfig);
        config.getKeyInfo(initTest, nullptr, nullptr, nullptr, &nVal);
        REQUIRE(nVal == 1);

        REQUIRE(config.solver(1).id == 1);
        REQUIRE(config.solver(0).heuId == HeuristicType::vsids);
        config.setValue("configuration", "frumpy");
        REQUIRE(config.solver(0).heuId == HeuristicType::berkmin);
        REQUIRE(config.numSolver() == 1);
    }
    SECTION("test init from file") {
        const char*   tempName = ".test_testConfigInitFromFile.port";
        std::ofstream temp(tempName);
        temp << "# A test config" << std::endl;
        temp << "[t0]: --models=0 --heuristic=Berkmin --restarts=x,100,1.5\n";
        temp.close();
        config.setValue("configuration", tempName);

        REQUIRE(config.getValue("configuration") == tempName);
        REQUIRE(config.solve.numModels == 0);
        REQUIRE(config.solver(0).heuId == HeuristicType::berkmin);
        REQUIRE(config.search(0).restart.rsSched == ScheduleStrategy::geom(100, 1.5));
        std::remove(tempName);
        REQUIRE(config.setValue(config.getKey(ClaspCliConfig::key_root, "configuration"), tempName) == -2);
    }
    SECTION("test init from file applies base") {
        const char*   tempName = ".test_testConfigInitFromFile.port";
        std::ofstream temp(tempName);
        temp << "# A test config" << std::endl;
        SECTION("valid") {
            temp << "[t0](trendy): --models=0 --heuristic=Berkmin\n";
            temp.close();
            REQUIRE(config.getValue("solver.otfs") == "0");
            config.setValue("configuration", tempName);
            REQUIRE(config.getValue("configuration") == tempName);
            CHECK(config.getValue("solver.otfs") == "2");
        }
        SECTION("invalid") {
            temp << "[t0](invalidBase): --models=0 --heuristic=Berkmin --restarts=x,100,1.5\n";
            temp.close();
            CHECK_THROWS_AS(config.setValue("configuration", tempName), std::logic_error);
        }
        std::remove(tempName);
    }
    SECTION("test init with invalid file") {
        const char*   tempName = ".test_testConfigInitInvalidOptionInCmdString.port";
        std::ofstream temp(tempName);
        SECTION("invalid option") {
            temp << "[fail]: --config=many" << std::endl;
            temp.close();
            CHECK_THROWS_AS(config.setValue("configuration", tempName), std::logic_error);
            CHECK(config.validate());
        }
        SECTION("invalid config") {
            temp << "[fail]: --no-lookback --heuristic=Berkmin" << std::endl;
            temp.close();
            CHECK(config.setValue("configuration", tempName));
            CHECK_THROWS_AS(config.validate(), std::logic_error);
            SharedContext ctx;
            CHECK_THROWS_AS(config.prepare(ctx), std::logic_error);
        }
        std::remove(tempName);
    }
    SECTION("test init ignore deletion if disabled") {
        const char* argv[] = {"--config=tweety --deletion=no"};
        config.setConfig(argv, argv + (sizeof(argv) / sizeof(const char*)), ProblemType::asp);
        REQUIRE(config.getValue("configuration") == "tweety");
        REQUIRE(config.getValue("solver.0.deletion") == "no");
        REQUIRE(config.getValue("solver.0.del_cfl") == "0");
        REQUIRE(config.getValue("solver.0.del_grow") == "no");
        REQUIRE(config.getValue("solver.0.del_max") == "umax,0");
    }
    SECTION("test ambiguous option") {
        const char* argv[] = {"--del=no"};
        REQUIRE_THROWS_AS(config.setConfig(argv, argv + (sizeof(argv) / sizeof(const char*)), ProblemType::asp),
                          std::logic_error);
    }
    SECTION("test string interface") {
        config.setValue("configuration", "auto,6");
        REQUIRE(config.numSolver() == 6);
        REQUIRE(config.solve.numSolver() == 1);
        REQUIRE((config.setValue("asp.eq", "0") && config.asp.iters == 0));
        REQUIRE((config.setValue("solver.0.heuristic", "berkmin") && config.solver(0).heuId == HeuristicType::berkmin));

        REQUIRE(config.getValue("asp.eq") == "0");
        REQUIRE(config.getValue("solver.0.heuristic").find("berkmin") == 0);

        REQUIRE(config.validate());
        REQUIRE(config.setValue("tester.configuration", "frumpy"));
        REQUIRE((config.testerConfig() && config.testerConfig()->numSolver() == 1));
        REQUIRE(config.setValue("tester.configuration", "many,6"));
        REQUIRE((config.testerConfig() && config.testerConfig()->numSolver() == config.numSolver()));

        REQUIRE_THROWS_AS(config.setValue("foo.bar", "123"), std::logic_error);
        REQUIRE_THROWS_AS(config.setValue("tester.eq", "1"), std::logic_error);
        REQUIRE_THROWS_AS(config.setValue("solver.2", "1"), std::logic_error);

        REQUIRE_THROWS_AS(config.getValue("foo.bar"), std::logic_error);
        REQUIRE_THROWS_AS(config.getValue("tester.eq"), std::logic_error);
        REQUIRE_THROWS_AS(config.getValue("solver.0"), std::logic_error);
    }
    SECTION("test master solver is implicit") {
        REQUIRE(config.getValue("solver.heuristic") == "auto,0");
        REQUIRE((config.setValue("solver.heuristic", "berkmin") && config.solver(0).heuId == HeuristicType::berkmin));
        REQUIRE_FALSE(config.hasConfig);
        REQUIRE(config.getValue("configuration") == "auto");
    }
    SECTION("test solver is implicitly created") {
        // solver option
        REQUIRE(config.setValue("solver.1.heuristic", "berkmin"));
        REQUIRE(config.numSolver() == 2);
        REQUIRE(config.solver(1).heuId == HeuristicType::berkmin);
        // search option
        REQUIRE(config.setValue("solver.2.restarts", "+,100,10"));
        REQUIRE(config.numSearch() == 3);
        REQUIRE(config.search(2).restart.rsSched == ScheduleStrategy::arith(100, 10));
        REQUIRE(config.numSolver() == 3);

        REQUIRE(config.setValue("solver.17.heuristic", "unit"));
        REQUIRE(config.numSolver() == 18);
        for (uint32_t i : irange(config.numSolver())) { REQUIRE(i == config.solver(i).id); }
    }
    SECTION("test get does not create solver") {
        REQUIRE(config.numSolver() == 1);
        REQUIRE(config.setValue("solver.heuristic", "berkmin"));
        ClaspCliConfig::KeyType k = config.getKey(ClaspCliConfig::key_solver, "1.heuristic");
        REQUIRE(k != ClaspCliConfig::key_invalid);
        REQUIRE(config.numSolver() == 1);
        SECTION("by key") {
            CHECK(config.getValue(k, val) > 0);
            CHECK(val == config.getValue("solver.heuristic"));
        }
        SECTION("by path") { CHECK(config.getValue("solver.1.heuristic") == config.getValue("solver.heuristic")); }
    }
    SECTION("test tester is implicitly created") {
        REQUIRE(config.setValue("tester.learn_explicit", "1"));
        REQUIRE((config.testerConfig() != nullptr && config.testerConfig()->shortMode == 1));
        REQUIRE_FALSE(config.testerConfig()->hasConfig);
        REQUIRE(config.getValue("tester.configuration") == "auto");
        REQUIRE(config.testerConfig()->satPre.type == 0);
        REQUIRE(config.config("tester"));
        REQUIRE(config.testerConfig()->satPre.type == 0);
        REQUIRE_FALSE(config.testerConfig()->hasConfig);
    }

    SECTION("test keys") {
        SECTION("test enumerate") {
            std::vector<std::string> keys;
            traverseKey(config, keys, ClaspCliConfig::key_root, "");
            REQUIRE(contains(keys, "configuration"));
            REQUIRE(contains(keys, "tester.configuration"));
            bool tester = false;
            for (std::string grp;;) {
#define OPTION(k, e, a, d, x, ...) REQUIRE(hasOption(config, grp + #k, keys, tester));
#define GROUP_BEGIN(X)             grp += (X);
#define GROUP_END(X)               grp.erase(grp.find(X));
#define CLASP_CONTEXT_OPTIONS      ""
#define CLASP_GLOBAL_OPTIONS       ""
#define CLASP_SOLVE_OPTIONS        "solve."
#define CLASP_ASP_OPTIONS          "asp."
#define CLASP_SOLVER_OPTIONS       "solver."
#define CLASP_SEARCH_OPTIONS       "solver."
#include <clasp/cli/clasp_cli_options.inl>

                if (tester) {
                    break;
                }
                tester = true;
                grp    = "tester.";
            }
        }

        SECTION("test query") {
            int         nSubkeys, arrLen, nValues;
            const char* help;
            REQUIRE(config.getKeyInfo(ClaspCliConfig::key_root, &nSubkeys, &arrLen, &help, &nValues) == 4);
            REQUIRE((nSubkeys > 0 && arrLen == -1 && help != nullptr && nValues == -1 &&
                     ClaspCliConfig::isLeafKey(ClaspCliConfig::key_root) == false));

            REQUIRE(config.getKeyInfo(ClaspCliConfig::key_solver, &nSubkeys, &arrLen, &help, &nValues) == 4);
            REQUIRE((nSubkeys > 0 && arrLen >= 0 && help != nullptr && nValues == -1 &&
                     ClaspCliConfig::isLeafKey(ClaspCliConfig::key_root) == false));

            ClaspCliConfig::KeyType s1 = config.getKey(ClaspCliConfig::key_solver, "1");
            REQUIRE(s1 != ClaspCliConfig::key_invalid);
            int nSolverKeys = nSubkeys;
            REQUIRE(config.getKeyInfo(s1, &nSubkeys, &arrLen, &help, &nValues) == 4);
            REQUIRE((nSubkeys == nSolverKeys && arrLen == -1));

            REQUIRE(config.getKey(ClaspCliConfig::key_solver, "heuristic") != ClaspCliConfig::key_invalid);
            REQUIRE(config.getKey(s1, ".heuristic") != ClaspCliConfig::key_invalid);
            REQUIRE(config.getKey(ClaspCliConfig::key_solver, ".") == ClaspCliConfig::key_solver);
            REQUIRE(config.getKey(ClaspCliConfig::key_solver, "") == ClaspCliConfig::key_solver);
            REQUIRE(config.getKey(ClaspCliConfig::key_solver, "asp") == ClaspCliConfig::key_invalid);

            REQUIRE(config.getKey(ClaspCliConfig::key_root, "stats") != ClaspCliConfig::key_invalid);
            REQUIRE(config.getKey(ClaspCliConfig::key_tester, "stats") == ClaspCliConfig::key_invalid);
            REQUIRE(config.getKey(ClaspCliConfig::key_root, "tester") != ClaspCliConfig::key_invalid);
            REQUIRE(config.getKey(ClaspCliConfig::key_tester, "tester") == ClaspCliConfig::key_invalid);

            ClaspCliConfig::KeyType tester = config.getKey(ClaspCliConfig::key_root, "tester");
            REQUIRE(tester == ClaspCliConfig::key_tester);
            REQUIRE(config.getKey(tester, "asp") == ClaspCliConfig::key_invalid);

            ClaspCliConfig::KeyType heuS0 = config.getKey(ClaspCliConfig::key_solver, "heuristic");
            ClaspCliConfig::KeyType heuS1 = config.getKey(s1, "heuristic");
            ClaspCliConfig::KeyType heuT  = config.getKey(ClaspCliConfig::key_tester, "solver.heuristic");

            REQUIRE((heuS0 != heuS1 && heuS0 != heuT && heuS1 != heuT));

            REQUIRE(config.getKey(heuS0, "restarts") == ClaspCliConfig::key_invalid);

            REQUIRE((config.getKeyInfo(heuS0, nullptr, nullptr, &help, nullptr) == 1 && help));
            REQUIRE(std::strstr(help, "decision heuristic") != 0);
        }
        SECTION("test query array") {
            REQUIRE(config.getArrKey(ClaspCliConfig::key_root, 0) == ClaspCliConfig::key_invalid);
            ClaspCliConfig::KeyType s0 = config.getArrKey(ClaspCliConfig::key_solver, 0);
            REQUIRE(s0 != ClaspCliConfig::key_invalid);
            REQUIRE(s0 != ClaspCliConfig::key_solver);
            REQUIRE(config.getArrKey(ClaspCliConfig::key_solver, 64) == ClaspCliConfig::key_invalid);

            ClaspCliConfig::KeyType st0 = config.getArrKey(config.getKey(ClaspCliConfig::key_tester, "solver"), 0);
            REQUIRE((s0 != st0 && st0 != ClaspCliConfig::key_invalid));
            if (Clasp::SolveOptions::supportedSolvers() > 1) {
                ClaspCliConfig::KeyType s5 = config.getArrKey(ClaspCliConfig::key_solver, 5);
                config.setValue(config.getKey(s5, "heuristic"), "unit");
                REQUIRE(config.solver(5).heuId == HeuristicType::unit);
            }
        }
    }
    SECTION("test project option") {
        REQUIRE(std::string("no") == config.getValue("solve.project"));
        REQUIRE(config.solve.project == 0u);
        REQUIRE(config.setValue("solve.project", "auto,0"));
        REQUIRE(std::string("auto,0") == config.getValue("solve.project"));
        REQUIRE(config.solve.project);
        REQUIRE(config.setValue("solve.project", "project,2"));
        REQUIRE(std::string("project,2") == config.getValue("solve.project"));
        REQUIRE(config.solve.project);

        REQUIRE(config.setValue("solve.project", "1"));
        REQUIRE(std::string("auto,0") == config.getValue("solve.project"));
    }
    SECTION("test lookahead option") {
        ClaspCliConfig::KeyType lookahead = config.getKey(ClaspCliConfig::key_root, "solver.lookahead");
        REQUIRE(config.setValue(lookahead, "no,0") == 0);
        REQUIRE(config.setValue(lookahead, "body,0") > 0);
        REQUIRE((config.solver(0).lookType == VarType::body && config.solver(0).lookOps == 0));
        REQUIRE(config.setValue(lookahead, "hybrid,umax") > 0);
        REQUIRE((config.solver(0).lookType == VarType::hybrid && config.solver(0).lookOps == 0));
        REQUIRE(config.setValue(lookahead, "no") > 0);
        REQUIRE((not Lookahead::isType(config.solver(0).lookType) && config.solver(0).lookOps == 0));
    }
    SECTION("test heuristic option") {
        ClaspCliConfig::KeyType heuristic = config.getKey(ClaspCliConfig::key_root, "solver.heuristic");
        REQUIRE(0 == config.setValue(heuristic, "vsidsS"));
        REQUIRE(1 == config.setValue(heuristic, "vsids"));
        REQUIRE((config.solver(0).heuId == HeuristicType::vsids && config.solver(0).heuristic.param == 0));
        REQUIRE(1 == config.setValue(heuristic, "vmtf,12"));
        REQUIRE((config.solver(0).heuId == HeuristicType::vmtf && config.solver(0).heuristic.param == 12));
        REQUIRE(1 == config.setValue(heuristic, "Berkmin"));
        REQUIRE((config.solver(0).heuId == HeuristicType::berkmin && config.solver(0).heuristic.param == 0));

        heuristic = config.getKey(ClaspCliConfig::key_solver, "score_other");
        REQUIRE(1 == config.setValue(heuristic, "all"));
        REQUIRE(config.solver(0).heuristic.other == HeuParams::other_all);
    }
    SECTION("test strengthen option") {
        ClaspCliConfig::KeyType strengthen = config.getKey(ClaspCliConfig::key_root, "solver.strengthen");
        REQUIRE(1 == config.setValue(strengthen, "no"));
        REQUIRE(config.solver(0).ccMinAntes == SolverStrategies::no_antes);
        REQUIRE(0 == config.setValue(strengthen, "no,1"));

        REQUIRE(1 == config.setValue(strengthen, "recursive"));
        REQUIRE(config.solver(0).ccMinAntes == SolverStrategies::all_antes);
        REQUIRE(config.solver(0).ccMinRec == SolverStrategies::cc_recursive);

        REQUIRE(1 == config.setValue(strengthen, "local,binary"));
        REQUIRE(config.solver(0).ccMinAntes == SolverStrategies::binary_antes);
        REQUIRE(config.solver(0).ccMinRec == SolverStrategies::cc_local);

        REQUIRE(0 == config.setValue(strengthen, "recs"));
    }
    SECTION("test contraction option") {
        ClaspCliConfig::KeyType contraction = config.getKey(ClaspCliConfig::key_root, "solver.contraction");
        REQUIRE(1 == config.setValue(contraction, "no"));
        REQUIRE(1 == config.setValue(contraction, "0"));

        REQUIRE(0 == config.setValue(contraction, "0,allUip"));
        REQUIRE(1 == config.setValue(contraction, "1,decisionSeq"));
    }
    SECTION("test loop option") {
        ClaspCliConfig::KeyType loops = config.getKey(ClaspCliConfig::key_root, "solver.loops");
        REQUIRE(1 == config.setValue(loops, "no"));
        REQUIRE(config.solver(0).loopRep == DefaultUnfoundedCheck::only_reason);
        loops = config.getKey(ClaspCliConfig::key_root, "solver.1.loops");
        REQUIRE(1 == config.setValue(loops, "shared"));
        REQUIRE(config.solver(1).loopRep == DefaultUnfoundedCheck::shared_reason);
    }
    SECTION("test deletion option") {
        ClaspCliConfig::KeyType deletion = config.getKey(ClaspCliConfig::key_root, "solver.deletion");
        REQUIRE(1 == config.setValue(deletion, "0"));
        REQUIRE(config.search(0).reduce.strategy.fReduce == 0);
        REQUIRE(0 == config.setValue(deletion, "0,10"));
        REQUIRE(1 == config.setValue(deletion, "ipSort"));
        REQUIRE(config.search(0).reduce.strategy.algo == ReduceStrategy::reduce_sort);
        REQUIRE(config.search(0).reduce.strategy.fReduce == 75);
        REQUIRE(config.search(0).reduce.strategy.score == 0);

        REQUIRE(1 == config.setValue(deletion, "sort,50"));
        REQUIRE(config.search(0).reduce.strategy.algo == ReduceStrategy::reduce_stable);
        REQUIRE(config.search(0).reduce.strategy.fReduce == 50);
        REQUIRE(config.search(0).reduce.strategy.score == 0);

        REQUIRE(1 == config.setValue(deletion, "basic,90,lbd"));
        REQUIRE(config.search(0).reduce.strategy.algo == ReduceStrategy::reduce_linear);
        REQUIRE(config.search(0).reduce.strategy.fReduce == 90);
        REQUIRE(config.search(0).reduce.strategy.score == 1);

        REQUIRE(0 == config.setValue(deletion, "basic,102"));
    }
    SECTION("test share option") {
        ClaspCliConfig::KeyType share = config.getKey(ClaspCliConfig::key_root, "share");
        REQUIRE(1 == config.setValue(share, "no"));
        REQUIRE(config.shareMode == ContextParams::share_no);

        REQUIRE(1 == config.setValue(share, "problem"));
        REQUIRE(config.shareMode == ContextParams::share_problem);

        REQUIRE(1 == config.setValue(share, "LEARNT"));
        REQUIRE(config.shareMode == ContextParams::share_learnt);
    }
    SECTION("test short simp option") {
        ClaspCliConfig::KeyType key = config.getKey(ClaspCliConfig::key_root, "short_simp_mode");
        REQUIRE(config.getValue(key, val) == 2);
        REQUIRE(val == "no");

        for (auto [x, y] : {std::pair{ContextParams::simp_learnt, "learnt"}, std::pair{ContextParams::simp_all, "all"},
                            std::pair{ContextParams::simp_no, "no"}}) {
            CAPTURE(y);
            REQUIRE(1 == config.setValue(key, y));
            REQUIRE(config.shortSimp == x);
            config.getValue(key, val);
            REQUIRE(val == y);
        }
    }
    SECTION("test trans-ext option") {
        ClaspCliConfig::KeyType tr = config.getKey(ClaspCliConfig::key_root, "asp.trans_ext");
        REQUIRE(1 == config.setValue(tr, "no"));
        REQUIRE(config.asp.erMode == Asp::LogicProgram::mode_native);
        REQUIRE(1 == config.setValue(tr, "scc"));
        REQUIRE(config.asp.erMode == Asp::LogicProgram::mode_transform_scc);
        tr = config.getKey(ClaspCliConfig::key_root, "tester.asp.trans_ext");
        REQUIRE(ClaspCliConfig::key_invalid == tr);
        REQUIRE(config.setValue(tr, "scc") == -1);
        REQUIRE_THROWS_AS(config.setValue("tester.asp.trans_ext", "scc"), std::logic_error);
    }
    SECTION("test enum-mode option") {
        ClaspCliConfig::KeyType eMode = config.getKey(ClaspCliConfig::key_root, "solve.enum_mode");

        REQUIRE(1 == config.setValue(eMode, "brave"));
        REQUIRE(config.solve.enumMode == EnumOptions::enum_brave);
        REQUIRE(0 == config.setValue(eMode, "consequences"));

        REQUIRE(config.setValue("solve.opt_mode", "ignore"));
        REQUIRE(config.solve.optMode == MinimizeMode::ignore);

        REQUIRE_THROWS_AS(config.setValue("tester.solve.enum_mode", "brave"), std::logic_error);
    }
    SECTION("test opt-strategy option") {
        ClaspCliConfig::KeyType oStrat = config.getKey(ClaspCliConfig::key_root, "solver.opt_strategy");
        REQUIRE(1 == config.setValue(oStrat, "bb"));
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "bb,lin"));
        REQUIRE(1 == config.setValue(oStrat, "bb,INC"));
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "bb,inc"));
        REQUIRE((config.solver(0).opt.type == 0u && config.solver(0).opt.algo == OptParams::bb_inc));
        REQUIRE(0 == config.setValue(oStrat, "bb,foo"));

        REQUIRE(1 == config.setValue(oStrat, "usc"));
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "usc,oll"));
        REQUIRE((config.solver(0).opt.type == OptParams::type_usc));
        REQUIRE(1 == config.setValue(oStrat, "usc,k"));
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "usc,k,0"));
        REQUIRE(config.solver(0).opt.type == OptParams::type_usc);
        REQUIRE((config.solver(0).opt.algo == OptParams::usc_k && config.solver(0).opt.kLim == 0));

        REQUIRE(1 == config.setValue(oStrat, "usc,k,4"));
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "usc,k,4"));
        REQUIRE(config.solver(0).opt.type == OptParams::type_usc);
        REQUIRE((config.solver(0).opt.algo == OptParams::usc_k && config.solver(0).opt.kLim == 4));

        REQUIRE(0 == config.setValue(oStrat, "usc,foo"));

        REQUIRE(1 == config.setValue(oStrat, "usc,oll,3"));
        REQUIRE(config.solver(0).opt.opts == 3u);
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "usc,oll,disjoint,succinct"));
        REQUIRE(1 == config.setValue(oStrat, "usc,oll,stratify,disjoint"));
        REQUIRE(config.solver(0).opt.opts == uint32_t(OptParams::usc_disjoint | OptParams::usc_stratify));
        REQUIRE(1 == config.setValue(oStrat, "usc,oll,0"));
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "usc,oll"));
        REQUIRE(0 == config.setValue(oStrat, "usc,oll,1,2"));

        ClaspCliConfig::KeyType uShrink = config.getKey(ClaspCliConfig::key_root, "solver.opt_usc_shrink");
        REQUIRE((config.getValue(uShrink, val) > 0 && val == "no"));
        REQUIRE(1 == config.setValue(uShrink, "exp"));
        REQUIRE((config.getValue(uShrink, val) > 0 && val == "exp,10"));
        REQUIRE(1 == config.setValue(uShrink, "bin,12"));
        REQUIRE((config.getValue(uShrink, val) > 0 && val == "bin,12"));
    }
    SECTION("test opt-strategy legacy option") {
        ClaspCliConfig::KeyType oStrat = config.getKey(ClaspCliConfig::key_root, "solver.opt_strategy");
        // clasp-3.0:
        REQUIRE(1 == config.setValue(oStrat, "1"));
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "bb,hier"));
        REQUIRE(1 == config.setValue(oStrat, "5"));
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "usc,oll,disjoint"));
        // clasp-3.1
        REQUIRE(1 == config.setValue(oStrat, "bb,1"));
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "bb,hier"));
        REQUIRE(1 == config.setValue(oStrat, "usc,7"));
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "usc,pmres,disjoint,succinct"));
        // clasp-3.2:
        REQUIRE(1 == config.setValue(oStrat, "usc,15"));
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "usc,pmres,disjoint,succinct,stratify"));
    }
    SECTION("test solve-limit option") {
        ClaspCliConfig::KeyType limit = config.getKey(ClaspCliConfig::key_root, "solve.solve_limit");
        REQUIRE(1 == config.setValue(limit, "0"));
        REQUIRE(config.getValue(limit, val) > 0);
        REQUIRE(std::string("0,umax") == val);
        REQUIRE(config.solve.limit.conflicts == 0);
        REQUIRE(config.solve.limit.enabled());

        REQUIRE(1 == config.setValue(limit, "no"));
        REQUIRE(config.getValue(limit, val) > 0);
        REQUIRE(config.solve.limit.conflicts == UINT64_MAX);
        REQUIRE(std::string("umax,umax") == val);
        REQUIRE_FALSE(config.solve.limit.enabled());
    }

    SECTION("test opt-mode option") {
        REQUIRE(config.getValue("solve.opt_mode") == "opt");
        REQUIRE(config.setValue("solve.opt_mode", "optN"));
        REQUIRE(config.getValue("solve.opt_mode") == "optN");

        REQUIRE(config.setValue("solve.opt_mode", "enum,100"));
        REQUIRE(config.getValue("solve.opt_mode") == "enum,100");
        REQUIRE(config.setValue("solve.opt_mode", "opt,50,20"));
        REQUIRE(config.getValue("solve.opt_mode") == "opt,50,20");

        REQUIRE(config.setValue("solve.opt_mode", "ignore"));
        REQUIRE(config.getValue("solve.opt_mode") == "ignore");

        REQUIRE(config.setValue("solve.opt_mode", "opt,50,20"));
        REQUIRE_FALSE(config.setValue("solve.opt_mode", "enum,a,b"));
        REQUIRE(config.getValue("solve.opt_mode") == "opt,50,20");
    }

    SECTION("test dynamic restart option") {
        REQUIRE(config.getValue("solver.restarts") == "x,100,1.5,0");
        REQUIRE_FALSE(config.setValue("solver.restarts", "D,100"));
        REQUIRE_FALSE(config.setValue("solver.restarts", "D,0"));

        REQUIRE(config.setValue("solver.restarts", "D,50,0.8"));
        REQUIRE(config.getValue("solver.restarts") == "d,50,0.8");

        REQUIRE(config.setValue("solver.restarts", "D,100,0.9,20"));
        REQUIRE(config.getValue("solver.restarts") == "d,100,0.9,20");
        REQUIRE(config.search(0).restart.rsSched.isDynamic());
        REQUIRE(config.search(0).restart.rsSched.lbdLim() == 20);

        REQUIRE(config.setValue("solver.restarts", "D,100,0.9,0,es,r"));
        REQUIRE(config.getValue("solver.restarts") == "d,100,0.9,0,es,r");
        const RestartSchedule& rs = config.search(0).restart.rsSched;
        REQUIRE(rs.isDynamic());
        REQUIRE(rs.lbdLim() == 0);
        REQUIRE(rs.fastAvg() == MovingAvg::Type::avg_ema_smooth);
        REQUIRE(rs.keepAvg() == RestartSchedule::keep_restart);

        REQUIRE(config.setValue("solver.restarts", "D,100,0.9,255,ls,rb,e,1234"));
        REQUIRE(config.getValue("solver.restarts") == "d,100,0.9,255,ls,br,e,1234");
        REQUIRE(rs.isDynamic());
        REQUIRE(rs.lbdLim() == 255);
        REQUIRE(rs.fastAvg() == MovingAvg::Type::avg_ema_log_smooth);
        REQUIRE(rs.keepAvg() == RestartSchedule::keep_always);
        REQUIRE(rs.slowAvg() == MovingAvg::Type::avg_ema);
        REQUIRE(rs.slowWin() == 1234);

        REQUIRE_FALSE(config.setValue("solver.restarts", "D,100,0.9,255,ls,rb,e,1234,12"));

        REQUIRE(config.setValue("solver.restarts", "D,50,0.8,0,ls,es,10000"));
        REQUIRE(config.getValue("solver.restarts") == "d,50,0.8,0,ls,es,10000");
        REQUIRE(rs.isDynamic());
        REQUIRE(rs.lbdLim() == 0);
        REQUIRE(rs.fastAvg() == MovingAvg::Type::avg_ema_log_smooth);
        REQUIRE(rs.keepAvg() == RestartSchedule::keep_never);
        REQUIRE(rs.slowAvg() == MovingAvg::Type::avg_ema_smooth);
        REQUIRE(rs.slowWin() == 10000);
    }

    SECTION("test block restart option") {
        auto r = Potassco::initFpuPrecision();
        REQUIRE(r != UINT32_MAX);
        POTASSCO_SCOPE_EXIT({ Potassco::restoreFpuPrecision(r); });
        REQUIRE(config.getValue("solver.block_restarts") == "no");
        REQUIRE_FALSE(config.setValue("solver.block_restarts", "0,1.3"));

        REQUIRE(config.setValue("solver.block_restarts", "5000"));
        REQUIRE(config.getValue("solver.block_restarts") == "5000,1.4,10000,e");
        RestartParams::Block b = config.search(0).restart.block;
        REQUIRE(b.window == 5000);
        REQUIRE(b.first == 10000);
        REQUIRE(b.fscale == 140u);
        REQUIRE(b.scale() == 1.4);
        REQUIRE(b.avg == uint32_t(MovingAvg::Type::avg_ema));

        REQUIRE_FALSE(config.setValue("solver.block_restarts", "5000,0.8"));
        REQUIRE_FALSE(config.setValue("solver.block_restarts", "5000,5.1"));

        REQUIRE(config.setValue("solver.block_restarts", "10000,1.1,0,d"));
        b = config.search(0).restart.block;
        REQUIRE(b.window == 10000);
        REQUIRE(b.fscale == 110u);
        REQUIRE(b.scale() == 1.1);
        REQUIRE(b.first == 0);
        REQUIRE(b.avg == uint32_t(MovingAvg::Type::avg_sma));
    }

    SECTION("test opt-stop option") {
        SumVec exp;
        REQUIRE(config.getValue("solve.opt_stop") == "no");
        REQUIRE(config.solve.optStop.empty());

        REQUIRE(config.setValue("solve.opt_stop", "10,17"));
        REQUIRE(config.getValue("solve.opt_stop") == "10,17");
        exp.push_back(10);
        exp.push_back(17);
        REQUIRE(config.solve.optStop == exp);

        REQUIRE(config.setValue("solve.opt_stop", "-4"));
        REQUIRE(config.getValue("solve.opt_stop") == "-4");
        exp.assign(1, -4);
        REQUIRE(config.solve.optStop == exp);

        REQUIRE(config.setValue("solve.opt_stop", "off"));
        REQUIRE(config.getValue("solve.opt_stop") == "no");
        REQUIRE(config.solve.optStop.empty());

        REQUIRE(config.setValue("solve.opt_stop", "0"));
        REQUIRE(config.getValue("solve.opt_stop") == "0");
        exp.assign(1, 0);
        REQUIRE(config.solve.optStop == exp);
    }

    SECTION("test get values") {
        std::string out;
        REQUIRE(config.getValue(config.getKey(ClaspCliConfig::key_tester, "configuration"), out) == -1);
        config.setValue("configuration", "tweety");
        REQUIRE(config.getValue("configuration") == "tweety");

        REQUIRE(config.getValue("solver.heuristic") == "vsids,92");
        REQUIRE(config.getValue("solver.strengthen") == "recursive,all,yes");
        REQUIRE(config.getValue("solver.deletion") == "basic,50,activity");
        REQUIRE(config.getValue("solver.restarts") == "l,60");
        REQUIRE(config.getValue("solver.loops") == "shared");
        REQUIRE(config.getValue("solver.partial_check") == "no");

        REQUIRE(config.getValue("sat_prepro") == "no");

        std::vector<std::string> leafs;
        traverseKey(config, leafs, ClaspCliConfig::key_root, "");
        for (const auto& leaf : leafs) {
            if (config.hasValue(leaf.c_str())) {
                val = config.getValue(leaf.c_str());
                REQUIRE(config.setValue(leaf.c_str(), val.c_str()));
            }
        }
        config.setValue("sat_prepro", "2,20,25");
        REQUIRE(std::strcmp(config.getValue("sat_prepro").c_str(), "2,iter=20,occ=25,size=4000") == 0);
        config.reset();
        std::string x = config.getValue("solver.del_cfl");
        REQUIRE((x == "no" || x == "0"));
        x = config.getValue("solver.del_grow");

        REQUIRE(config.setValue("solver.del_grow", x.c_str()));
        x = config.getValue("solve.opt_mode");
        REQUIRE(x == "opt");
        config.setValue("solve.opt_mode", "opt,122");
        REQUIRE(config.getValue("solve.opt_mode") == "opt,122");
        config.setValue("solver.del_init", "3,100,200");
        REQUIRE(config.getValue("solver.del_init") == "3,100,200");

        REQUIRE_FALSE(config.hasValue("tester.learn_explicit"));
        config.setValue("tester.learn_explicit", "1");
        REQUIRE(config.hasValue("tester.learn_explicit"));

        REQUIRE_THROWS_AS(config.getValue("enum"), std::logic_error);
        REQUIRE_THROWS_AS(config.getValue("tester.solve.opt_mode"), std::logic_error);
    }
}

#if CLASP_HAS_THREADS
TEST_CASE("Cli mt options", "[cli][mt]") {
    ClaspCliConfig config;
    SECTION("test config from argv") {
        REQUIRE(config.numSolver() == 1);
        REQUIRE(config.solve.numSolver() == 1);
        REQUIRE(config.solve.numModels != 0);
        const char* argv[] = {"-n0",     "--parallel-mode",         "4", "--save-progress=20",
                              "--stats", "--tester=--config=frumpy"};
        config.setConfig(argv, argv + (sizeof(argv) / sizeof(const char*)), ProblemType::asp);
        REQUIRE(config.getValue("configuration") == "auto");
        REQUIRE(config.getValue("asp.eq") == "3");
        REQUIRE(config.getValue("asp.trans_ext") == "dynamic");
        REQUIRE(config.solve.numSolver() == 4);
        REQUIRE(config.numSolver() == 4);
        REQUIRE(config.solve.numModels == 0);
        for (uint32_t i : irange(config.numSolver())) { REQUIRE(config.solver(i).saveProgress == 20); }
        REQUIRE(config.testerConfig());
        REQUIRE(config.testerConfig()->numSolver() == 1);
        REQUIRE(config.testerConfig()->hasConfig);
        REQUIRE(config.getValue("tester.configuration") == "frumpy");
    }
    SECTION("test init from file") {
        const char*   tempName = ".test_testConfigInitFromFile.port";
        std::ofstream temp(tempName);
        temp << "[t0]: --models=0 --parallel-mode=4 --heuristic=Berkmin --restarts=x,100,1.5\n"
             << "[t1](tweety): --heuristic=Vsids,98 --restarts=L,128\n"
             << "t2   (jumpy): --heuristic=Vmtf --restarts=D,100,0.7\n"
             << "[t3]: --heuristic=None --restarts=F,1000\n";
        temp.close();
        config.setValue("configuration", tempName);

        REQUIRE(config.getValue("configuration") == tempName);
        REQUIRE_THROWS_AS(config.getValue("tester.configuration"), std::logic_error);
        REQUIRE_THROWS_AS(config.getValue("tester.learn_explicit"), std::logic_error);
        REQUIRE(config.solve.numModels == 0);
        REQUIRE(config.solver(0).heuId == HeuristicType::berkmin);
        REQUIRE(config.search(0).restart.rsSched == ScheduleStrategy::geom(100, 1.5));
        REQUIRE(config.solve.numSolver() == 4);
        REQUIRE(config.numSolver() == 4);
        REQUIRE(config.solver(1).heuId == HeuristicType::vsids);
        REQUIRE(config.solver(2).heuId == HeuristicType::vmtf);
        REQUIRE(config.solver(3).heuId == HeuristicType::none);
        REQUIRE(config.search(1).restart.rsSched == ScheduleStrategy::luby(128));
        REQUIRE(config.search(2).restart.rsSched.isDynamic());
        REQUIRE(config.search(2).restart.base() == 100);
        REQUIRE(config.search(2).restart.rsSched.k() == 0.7f);
        REQUIRE(config.search(2).restart.rsSched.lbdLim() == 0);
        REQUIRE(config.search(3).restart.rsSched == ScheduleStrategy::fixed(1000));

        config.setValue("tester.configuration", tempName);
        REQUIRE(config.getValue("tester.configuration") == tempName);
        std::remove(tempName);
        REQUIRE(config.setValue(config.getKey(ClaspCliConfig::key_root, "configuration"), tempName) == -2);
        REQUIRE(config.setValue(config.getKey(ClaspCliConfig::key_tester, "configuration"), tempName) == -2);
    }
    SECTION("test parallel-mode option") {
        ClaspCliConfig::KeyType pMode = config.getKey(ClaspCliConfig::key_root, "solve.parallel_mode");
        REQUIRE(0 == config.setValue(pMode, "0"));
        REQUIRE(uint32_t(1) == config.solve.algorithm.threads);
        REQUIRE(SolveOptions::Algorithm::mode_compete == config.solve.algorithm.mode);
        REQUIRE(config.solve.numSolver() == 1);

        REQUIRE(1 == config.setValue(pMode, "10"));
        REQUIRE(uint32_t(10) == config.solve.algorithm.threads);
        REQUIRE(SolveOptions::Algorithm::mode_compete == config.solve.algorithm.mode);
        REQUIRE(config.solve.numSolver() == 10);

        REQUIRE(1 == config.setValue(pMode, "10,split"));
        REQUIRE(uint32_t(10) == config.solve.algorithm.threads);
        REQUIRE(SolveOptions::Algorithm::mode_split == config.solve.algorithm.mode);
        REQUIRE(config.solve.numSolver() == 10);

        REQUIRE(0 == config.setValue(pMode, "65"));
    }
    SECTION("test distribute option") {
        ClaspCliConfig::KeyType distribute = config.getKey(ClaspCliConfig::key_root, "solve.distribute");
        REQUIRE(1 == config.setValue(distribute, "0"));
        REQUIRE(0 == config.setValue(distribute, "0,1"));
        REQUIRE(1 == config.setValue(distribute, "conflict"));
        REQUIRE(Distributor::Policy::conflict == config.solve.distribute.types);
        REQUIRE(4 == config.solve.distribute.lbd);

        REQUIRE(1 == config.setValue(distribute, "loop,2"));
        REQUIRE(Distributor::Policy::loop == config.solve.distribute.types);
        REQUIRE(2 == config.solve.distribute.lbd);

        REQUIRE(1 == config.setValue(distribute, "all,2,123"));
        REQUIRE(Distributor::Policy::all == config.solve.distribute.types);
        REQUIRE(2 == config.solve.distribute.lbd);
        REQUIRE(123 == config.solve.distribute.size);
    }
    SECTION("test integrate option") {
        ClaspCliConfig::KeyType integrate = config.getKey(ClaspCliConfig::key_root, "solve.integrate");

        REQUIRE(0 == config.setValue(integrate, "0"));
        REQUIRE(0 == config.setValue(integrate, "no"));

        REQUIRE(1 == config.setValue(integrate, "active"));
        REQUIRE(SolveOptions::Integration::filter_heuristic == config.solve.integrate.filter);
        REQUIRE(1024 == config.solve.integrate.grace);
        REQUIRE(SolveOptions::Integration::topo_all == config.solve.integrate.topo);

        REQUIRE(1 == config.setValue(integrate, "unsat,100"));
        REQUIRE(SolveOptions::Integration::filter_sat == config.solve.integrate.filter);
        REQUIRE(100 == config.solve.integrate.grace);
        REQUIRE(SolveOptions::Integration::topo_all == config.solve.integrate.topo);

        REQUIRE(1 == config.setValue(integrate, "gp,200,cubeX"));
        REQUIRE(SolveOptions::Integration::filter_gp == config.solve.integrate.filter);
        REQUIRE(200 == config.solve.integrate.grace);
        REQUIRE(SolveOptions::Integration::topo_cubex == config.solve.integrate.topo);

        REQUIRE(1 == config.setValue(integrate, "gp,77,cube"));
        REQUIRE(SolveOptions::Integration::filter_gp == config.solve.integrate.filter);
        REQUIRE(77 == config.solve.integrate.grace);
        REQUIRE(SolveOptions::Integration::topo_cube == config.solve.integrate.topo);
    }
}
#endif

} // namespace Cli::Test

} // namespace Clasp
