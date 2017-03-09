//
// Copyright (c) 2014-2017 Benjamin Kaufmann
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
#include <clasp/cli/clasp_options.h>
#include <clasp/lookahead.h>
#include <clasp/unfounded_check.h>
#include <clasp/logic_program.h>
namespace Clasp { namespace Cli { namespace Test {

inline bool operator==(const ScheduleStrategy& lhs, const ScheduleStrategy& rhs) {
	return lhs.type == rhs.type && lhs.base == rhs.base && lhs.len == rhs.len && lhs.grow == rhs.grow;
}

class CliTest : public CppUnit::TestFixture {
  CPPUNIT_TEST_SUITE(CliTest);
	CPPUNIT_TEST(testConfigArgv);

	CPPUNIT_TEST(testConfigStrInterface);
	CPPUNIT_TEST(testConfigImplicitSolverMaster);
	CPPUNIT_TEST(testConfigImplicitCreateSolver);
	CPPUNIT_TEST(testConfigImplicitCreateTester);

	CPPUNIT_TEST(testConfigEnumerateKeys);
	CPPUNIT_TEST(testConfigQueryKeys);
	CPPUNIT_TEST(testConfigQueryArrKey);

	CPPUNIT_TEST(testConfigInit);
	CPPUNIT_TEST(testConfigInitFromFile);
	CPPUNIT_TEST(testConfigInitInvalidOptionInFile);

	CPPUNIT_TEST(testSetLookahead);
	CPPUNIT_TEST(testSetHeuristic);
	CPPUNIT_TEST(testSetStrengthen);
	CPPUNIT_TEST(testSetContraction);
	CPPUNIT_TEST(testSetLoops);
	CPPUNIT_TEST(testSetDeletion);
	CPPUNIT_TEST(testSetShareMode);
	CPPUNIT_TEST(testSetTrMode);
	CPPUNIT_TEST(testSetEnumMode);
	CPPUNIT_TEST(testSetOptStrategy);
	CPPUNIT_TEST(testSetLegacyOptStrategy);
	CPPUNIT_TEST(testSetSolveLimit);
#if CLASP_HAS_THREADS
	CPPUNIT_TEST(testSetParallelMode);
	CPPUNIT_TEST(testSetDistribute);
	CPPUNIT_TEST(testSetIntegrate);
#endif
	CPPUNIT_TEST(testConfigQueryStrValues);
	CPPUNIT_TEST(testSetOptBound);
	CPPUNIT_TEST_SUITE_END();
public:
	void testConfigArgv() {
		ClaspCliConfig config;
		CPPUNIT_ASSERT(config.numSolver() == 1);
		CPPUNIT_ASSERT(config.solve.numSolver() == 1);
		CPPUNIT_ASSERT(config.solve.numModels != 0);
		uint32 nSolver = 1;
#if CLASP_HAS_THREADS
		const char* argv[] = {"-n0", "--parallel-mode", "4", "--save-progress=20", "--stats", "--tester=--config=frumpy"};
		nSolver = 4;
#else
		const char* argv[] = {"-n0", "--save-progress=20", "--stats", "--tester=--config=frumpy"};
#endif
		config.setConfig(argv, argv + (sizeof(argv)/sizeof(const char*)), Problem_t::Asp);
		CPPUNIT_ASSERT(config.solve.numSolver() == nSolver);
		CPPUNIT_ASSERT(config.numSolver() == nSolver);
		CPPUNIT_ASSERT(config.solve.numModels == 0);
		for (uint32 i = 0; i != config.numSolver(); ++i) {
			CPPUNIT_ASSERT(config.solver(i).saveProgress == 20);
		}
		CPPUNIT_ASSERT(config.testerConfig() && config.testerConfig()->numSolver() == 1);
		CPPUNIT_ASSERT(config.getValue("tester.configuration") == "frumpy");
	}

	void testConfigStrInterface()  {
		ClaspCliConfig config;
		config.setValue("configuration", "auto,6");
		CPPUNIT_ASSERT(config.numSolver() == 6);
		CPPUNIT_ASSERT(config.setValue("asp.eq", "0") && config.asp.iters == 0);
		CPPUNIT_ASSERT(config.setValue("solver.0.heuristic", "berkmin") && config.solver(0).heuId == Heuristic_t::Berkmin);

		CPPUNIT_ASSERT(config.getValue("asp.eq") == "0");
		CPPUNIT_ASSERT(config.getValue("solver.0.heuristic").find("berkmin") == 0);

		CPPUNIT_ASSERT(config.validate());
		CPPUNIT_ASSERT(config.setValue("tester.configuration", "frumpy"));
		CPPUNIT_ASSERT(config.testerConfig() && config.testerConfig()->numSolver() == 1);
		CPPUNIT_ASSERT(config.setValue("tester.configuration", "many,6"));
		CPPUNIT_ASSERT(config.testerConfig() && config.testerConfig()->numSolver() == config.numSolver());

		CPPUNIT_ASSERT_THROW(config.setValue("foo.bar", "123"), std::logic_error);
		CPPUNIT_ASSERT_THROW(config.setValue("tester.eq", "1"), std::logic_error);
		CPPUNIT_ASSERT_THROW(config.setValue("solver.2", "1"), std::logic_error);

		CPPUNIT_ASSERT_THROW(config.getValue("foo.bar"), std::logic_error);
		CPPUNIT_ASSERT_THROW(config.getValue("tester.eq"), std::logic_error);
		CPPUNIT_ASSERT_THROW(config.getValue("solver.0"), std::logic_error);
	}

	void testConfigImplicitSolverMaster() {
		ClaspCliConfig config;
		CPPUNIT_ASSERT(config.getValue("solver.heuristic") == "auto,0");
		CPPUNIT_ASSERT(config.setValue("solver.heuristic", "berkmin") && config.solver(0).heuId == Heuristic_t::Berkmin);
	}
	void testConfigImplicitCreateSolver() {
		ClaspCliConfig config;
		CPPUNIT_ASSERT(config.numSolver() == 1);
		// solver option
		CPPUNIT_ASSERT(config.setValue("solver.1.heuristic", "berkmin"));
		CPPUNIT_ASSERT(config.numSolver() == 2);
		CPPUNIT_ASSERT(config.solver(1).heuId == Heuristic_t::Berkmin);
		// search option
		CPPUNIT_ASSERT(config.setValue("solver.2.restarts", "+,100,10"));
		CPPUNIT_ASSERT(config.numSearch() == 3);
		CPPUNIT_ASSERT(config.search(2).restart.sched == ScheduleStrategy::arith(100, 10));
		CPPUNIT_ASSERT(config.numSolver() == 3);

		CPPUNIT_ASSERT(config.setValue("solver.17.heuristic", "unit"));
		CPPUNIT_ASSERT(config.numSolver() == 18);
		for (uint32 i = 0; i != config.numSolver(); ++i) {
			CPPUNIT_ASSERT_EQUAL_MESSAGE("solver id not set", i, config.solver(i).id);
		}
	}
	void testConfigImplicitCreateTester() {
		ClaspCliConfig config;
		CPPUNIT_ASSERT(config.testerConfig() == 0);
		CPPUNIT_ASSERT(config.setValue("tester.learn_explicit", "1"));
		CPPUNIT_ASSERT(config.testerConfig() != 0 && config.testerConfig()->shortMode == 1);
	}

	void testConfigEnumerateKeys() {
		ClaspCliConfig config;
		std::vector<std::string> keys;
		traverseKey(config, keys, ClaspCliConfig::KEY_ROOT, "");
		CPPUNIT_ASSERT(std::find(keys.begin(), keys.end(), "configuration") != keys.end());
		CPPUNIT_ASSERT(std::find(keys.begin(), keys.end(), "tester.configuration") != keys.end());
		bool tester = false;
		for (std::string grp;; ) {
			#define OPTION(k, e, a, d, x,...) CPPUNIT_ASSERT_MESSAGE(grp + #k, std::find(keys.begin(), keys.end(), grp + #k) != keys.end() || (tester && !isValidOption(config, grp + #k)));
			#define GROUP_BEGIN(X) grp += X;
			#define GROUP_END(X)   grp.erase(grp.find(X));
			#define CLASP_CONTEXT_OPTIONS ""
			#define CLASP_GLOBAL_OPTIONS ""
			#define CLASP_SOLVE_OPTIONS   "solve."
			#define CLASP_ASP_OPTIONS     "asp."
			#define CLASP_SOLVER_OPTIONS  "solver."
			#define CLASP_SEARCH_OPTIONS  "solver."
			#include <clasp/cli/clasp_cli_options.inl>
			if (tester) { break; }
			tester = true;
			grp    = "tester.";
		}
	}

	void testConfigQueryKeys(){
		ClaspCliConfig config;
		int nSubkeys, arrLen, nValues;
		const char* help;
		CPPUNIT_ASSERT(config.getKeyInfo(ClaspCliConfig::KEY_ROOT, &nSubkeys, &arrLen, &help, &nValues) == 4);
		CPPUNIT_ASSERT(nSubkeys > 0 && arrLen == -1 && help != 0 && nValues == -1 && ClaspCliConfig::isLeafKey(ClaspCliConfig::KEY_ROOT) == false);

		CPPUNIT_ASSERT(config.getKeyInfo(ClaspCliConfig::KEY_SOLVER, &nSubkeys, &arrLen, &help, &nValues) == 4);
		CPPUNIT_ASSERT(nSubkeys > 0 && arrLen >= 0 && help != 0 && nValues == -1 && ClaspCliConfig::isLeafKey(ClaspCliConfig::KEY_ROOT) == false);

		ClaspCliConfig::KeyType s1 = config.getKey(ClaspCliConfig::KEY_SOLVER, "1");
		CPPUNIT_ASSERT(s1 != ClaspCliConfig::KEY_INVALID);
		int nSolverKeys = nSubkeys;
		CPPUNIT_ASSERT(config.getKeyInfo(s1, &nSubkeys, &arrLen, &help, &nValues) == 4);
		CPPUNIT_ASSERT(nSubkeys == nSolverKeys && arrLen == -1);

		CPPUNIT_ASSERT(config.getKey(ClaspCliConfig::KEY_SOLVER, "heuristic") != ClaspCliConfig::KEY_INVALID);
		CPPUNIT_ASSERT(config.getKey(s1, ".heuristic") != ClaspCliConfig::KEY_INVALID);
		CPPUNIT_ASSERT(config.getKey(ClaspCliConfig::KEY_SOLVER, ".") == ClaspCliConfig::KEY_SOLVER);
		CPPUNIT_ASSERT(config.getKey(ClaspCliConfig::KEY_SOLVER, "") == ClaspCliConfig::KEY_SOLVER);
		CPPUNIT_ASSERT(config.getKey(ClaspCliConfig::KEY_SOLVER, "asp") == ClaspCliConfig::KEY_INVALID);

		CPPUNIT_ASSERT(config.getKey(ClaspCliConfig::KEY_ROOT, "stats") != ClaspCliConfig::KEY_INVALID);
		CPPUNIT_ASSERT(config.getKey(ClaspCliConfig::KEY_TESTER, "stats") == ClaspCliConfig::KEY_INVALID);
		CPPUNIT_ASSERT(config.getKey(ClaspCliConfig::KEY_ROOT, "tester")!= ClaspCliConfig::KEY_INVALID);
		CPPUNIT_ASSERT(config.getKey(ClaspCliConfig::KEY_TESTER, "tester")== ClaspCliConfig::KEY_INVALID);


		ClaspCliConfig::KeyType tester = config.getKey(ClaspCliConfig::KEY_ROOT, "tester");
		CPPUNIT_ASSERT(tester == ClaspCliConfig::KEY_TESTER);
		CPPUNIT_ASSERT(config.getKey(tester, "asp") == ClaspCliConfig::KEY_INVALID);

		ClaspCliConfig::KeyType heuS0 = config.getKey(ClaspCliConfig::KEY_SOLVER, "heuristic");
		ClaspCliConfig::KeyType heuS1 = config.getKey(s1, "heuristic");
		ClaspCliConfig::KeyType heuT  = config.getKey(ClaspCliConfig::KEY_TESTER, "solver.heuristic");

		CPPUNIT_ASSERT(heuS0 != heuS1 && heuS0 != heuT && heuS1 != heuT);

		CPPUNIT_ASSERT(config.getKey(heuS0, "restarts") == ClaspCliConfig::KEY_INVALID);

		CPPUNIT_ASSERT(config.getKeyInfo(heuS0, 0, 0, &help, 0) == 1 && help);
		CPPUNIT_ASSERT(std::strstr(help, "decision heuristic") != 0);
	}

	void testConfigQueryArrKey() {
		ClaspCliConfig config;
		CPPUNIT_ASSERT(config.getArrKey(ClaspCliConfig::KEY_ROOT, 0) == ClaspCliConfig::KEY_INVALID);
		ClaspCliConfig::KeyType s0 = config.getArrKey(ClaspCliConfig::KEY_SOLVER, 0);
		CPPUNIT_ASSERT(s0 != ClaspCliConfig::KEY_INVALID);
		CPPUNIT_ASSERT(s0 != ClaspCliConfig::KEY_SOLVER);
		CPPUNIT_ASSERT(config.getArrKey(ClaspCliConfig::KEY_SOLVER, 64) == ClaspCliConfig::KEY_INVALID);

		ClaspCliConfig::KeyType st0 = config.getArrKey(config.getKey(ClaspCliConfig::KEY_TESTER, "solver"), 0);
		CPPUNIT_ASSERT(s0 != st0 && st0 != ClaspCliConfig::KEY_INVALID);
		if (config.solve.supportedSolvers() > 1) {
			ClaspCliConfig::KeyType s5 = config.getArrKey(ClaspCliConfig::KEY_SOLVER, 5);
			config.setValue(config.getKey(s5, "heuristic"), "unit");
			CPPUNIT_ASSERT(config.solver(5).heuId == Heuristic_t::Unit);
		}
	}
	void testConfigInit() {
		ClaspCliConfig config;
		ClaspCliConfig::KeyType initGen  = config.getKey(ClaspCliConfig::KEY_ROOT, "configuration");
		ClaspCliConfig::KeyType initTest = config.getKey(ClaspCliConfig::KEY_TESTER, "configuration");
		CPPUNIT_ASSERT(ClaspCliConfig::isLeafKey(initGen) && ClaspCliConfig::isLeafKey(initTest) && initTest != initGen);
		int nSub, nArr, nVal;
		const char* help;
		config.getKeyInfo(initGen, &nSub, &nArr, &help, &nVal);
		CPPUNIT_ASSERT(nSub == 0 && nArr == -1 && nVal == 1 && std::strstr(help, "frumpy") != 0);
		config.getKeyInfo(initTest, &nSub, &nArr, &help, &nVal);
		CPPUNIT_ASSERT(nSub == 0 && nArr == -1 && nVal == 0 && std::strstr(help, "tweety") != 0);

		CPPUNIT_ASSERT_EQUAL(true, config.setValue("configuration", "many"));
		CPPUNIT_ASSERT(config.numSolver() > 1);
		CPPUNIT_ASSERT(config.testerConfig() == 0);
		CPPUNIT_ASSERT_EQUAL(true, config.setValue("tester.configuration", "tweety"));
		CPPUNIT_ASSERT(config.testerConfig() != 0);
		config.getKeyInfo(initTest, 0, 0, 0, &nVal);
		CPPUNIT_ASSERT(nVal == 1);

		CPPUNIT_ASSERT(config.solver(1).id == 1);
		CPPUNIT_ASSERT(config.solver(0).heuId == Heuristic_t::Vsids);
		config.setValue("configuration", "frumpy");
		CPPUNIT_ASSERT(config.solver(0).heuId == Heuristic_t::Berkmin);
		CPPUNIT_ASSERT(config.numSolver() == 1);
	}

	void testConfigInitFromFile() {
		const char* tempName = ".test_testConfigInitFromFile.port";
		std::ofstream temp(tempName);
		const char* parallel = "";
#if CLASP_HAS_THREADS
		parallel = "--parallel-mode=4";
#endif
		temp << "# A test portfolio" << std::endl;
		temp << "[t0]: --models=0 " << parallel << " --heuristic=Berkmin --restarts=x,100,1.5\n"
		     << "[t1](tweety): --heuristic=Vsids,98 --restarts=L,128\n"
		     << "t2   (jumpy): --heuristic=Vmtf --restarts=D,100,0.7\n"
		     << "[t3]: --heuristic=None --restarts=F,1000\n";
		temp.close();
		ClaspCliConfig config;
		config.setValue("configuration", tempName);

		CPPUNIT_ASSERT(config.getValue("configuration") == tempName);
		CPPUNIT_ASSERT(config.solve.numModels == 0);
		CPPUNIT_ASSERT(config.solver(0).heuId == Heuristic_t::Berkmin);
		CPPUNIT_ASSERT(config.search(0).restart.sched == ScheduleStrategy::geom(100, 1.5));
		if (std::strcmp(parallel, "") != 0) {
			CPPUNIT_ASSERT(config.solve.numSolver() == 4);
			CPPUNIT_ASSERT(config.numSolver() == 4);
			CPPUNIT_ASSERT(config.solver(1).heuId == Heuristic_t::Vsids);
			CPPUNIT_ASSERT(config.solver(2).heuId == Heuristic_t::Vmtf);
			CPPUNIT_ASSERT(config.solver(3).heuId == Heuristic_t::None);
			CPPUNIT_ASSERT(config.search(1).restart.sched == ScheduleStrategy::luby(128));
			CPPUNIT_ASSERT(config.search(2).restart.sched == ScheduleStrategy(ScheduleStrategy::User, 100, 0.7, 0));
			CPPUNIT_ASSERT(config.search(3).restart.sched == ScheduleStrategy::fixed(1000));
		}
		std::remove(tempName);
		CPPUNIT_ASSERT(config.setValue(config.getKey(ClaspCliConfig::KEY_ROOT, "configuration"), tempName) == -2);
	}

	void testConfigInitInvalidOptionInFile() {
		const char* tempName = ".test_testConfigInitInvalidOptionInCmdString.port";
		std::ofstream temp(tempName);
		temp << "[fail]: --config=many" << std::endl;
		temp.close();
		ClaspCliConfig config;
		CPPUNIT_ASSERT_THROW(config.setValue("configuration", tempName), std::logic_error);
		std::remove(tempName);
	}

	void testSetLookahead() {
		ClaspCliConfig config;
		ClaspCliConfig::KeyType lookahead = config.getKey(ClaspCliConfig::KEY_ROOT, "solver.lookahead");
		CPPUNIT_ASSERT(config.setValue(lookahead, "no,0") == 0);
		CPPUNIT_ASSERT(config.setValue(lookahead, "body,0") > 0);
		CPPUNIT_ASSERT(config.solver(0).lookType == Var_t::Body && config.solver(0).lookOps == 0);
		CPPUNIT_ASSERT(config.setValue(lookahead, "hybrid,umax") > 0);
		CPPUNIT_ASSERT(config.solver(0).lookType == Var_t::Hybrid && config.solver(0).lookOps == 0);
		CPPUNIT_ASSERT(config.setValue(lookahead, "no") > 0);
		CPPUNIT_ASSERT(!Lookahead::isType(config.solver(0).lookType) && config.solver(0).lookOps == 0);
	}
	void testSetHeuristic() {
		ClaspCliConfig config;
		ClaspCliConfig::KeyType heuristic = config.getKey(ClaspCliConfig::KEY_ROOT, "solver.heuristic");
		CPPUNIT_ASSERT_EQUAL(0, config.setValue(heuristic, "vsidsS"));
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(heuristic, "vsids"));
		CPPUNIT_ASSERT(config.solver(0).heuId == Heuristic_t::Vsids && config.solver(0).heuristic.param == 0);
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(heuristic, "vmtf,12"));
		CPPUNIT_ASSERT(config.solver(0).heuId == Heuristic_t::Vmtf && config.solver(0).heuristic.param == 12);
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(heuristic, "Berkmin"));
		CPPUNIT_ASSERT(config.solver(0).heuId == Heuristic_t::Berkmin && config.solver(0).heuristic.param == 0);

		heuristic = config.getKey(ClaspCliConfig::KEY_SOLVER, "score_other");
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(heuristic, "2"));
		CPPUNIT_ASSERT(config.solver(0).heuristic.other == 2);
	}
	void testSetStrengthen() {
		ClaspCliConfig config;
		ClaspCliConfig::KeyType strengthen = config.getKey(ClaspCliConfig::KEY_ROOT, "solver.strengthen");
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(strengthen, "no"));
		CPPUNIT_ASSERT(config.solver(0).ccMinAntes == SolverStrategies::no_antes);
		CPPUNIT_ASSERT_EQUAL(0, config.setValue(strengthen, "no,1"));

		CPPUNIT_ASSERT_EQUAL(1, config.setValue(strengthen, "recursive"));
		CPPUNIT_ASSERT(config.solver(0).ccMinAntes == SolverStrategies::all_antes);
		CPPUNIT_ASSERT(config.solver(0).ccMinRec == SolverStrategies::cc_recursive);

		CPPUNIT_ASSERT_EQUAL(1, config.setValue(strengthen, "local,2"));
		CPPUNIT_ASSERT(config.solver(0).ccMinAntes == SolverStrategies::binary_antes);
		CPPUNIT_ASSERT(config.solver(0).ccMinRec == SolverStrategies::cc_local);

		CPPUNIT_ASSERT_EQUAL(0, config.setValue(strengthen, "recs"));
	}
	void testSetContraction() {
		ClaspCliConfig config;
		ClaspCliConfig::KeyType contraction = config.getKey(ClaspCliConfig::KEY_ROOT, "solver.contraction");
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(contraction, "no"));
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(contraction, "0"));


		CPPUNIT_ASSERT_EQUAL(0, config.setValue(contraction, "0,1"));
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(contraction, "1,1"));
	}
	void testSetLoops() {
		ClaspCliConfig config;
		ClaspCliConfig::KeyType loops = config.getKey(ClaspCliConfig::KEY_ROOT, "solver.loops");
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(loops, "no"));
		CPPUNIT_ASSERT(config.solver(0).loopRep == DefaultUnfoundedCheck::only_reason);
		loops = config.getKey(ClaspCliConfig::KEY_ROOT, "solver.1.loops");
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(loops, "shared"));
		CPPUNIT_ASSERT(config.solver(1).loopRep == DefaultUnfoundedCheck::shared_reason);
	}
	void testSetDeletion() {
		ClaspCliConfig config;
		ClaspCliConfig::KeyType deletion = config.getKey(ClaspCliConfig::KEY_ROOT, "solver.deletion");
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(deletion, "0"));
		CPPUNIT_ASSERT(config.search(0).reduce.strategy.fReduce == 0);
		CPPUNIT_ASSERT_EQUAL(0, config.setValue(deletion, "0,10"));
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(deletion, "ipSort"));
		CPPUNIT_ASSERT(config.search(0).reduce.strategy.algo == ReduceStrategy::reduce_sort);
		CPPUNIT_ASSERT(config.search(0).reduce.strategy.fReduce == 75);
		CPPUNIT_ASSERT(config.search(0).reduce.strategy.score == 0);

		CPPUNIT_ASSERT_EQUAL(1, config.setValue(deletion, "sort,50"));
		CPPUNIT_ASSERT(config.search(0).reduce.strategy.algo == ReduceStrategy::reduce_stable);
		CPPUNIT_ASSERT(config.search(0).reduce.strategy.fReduce == 50);
		CPPUNIT_ASSERT(config.search(0).reduce.strategy.score == 0);

		CPPUNIT_ASSERT_EQUAL(1, config.setValue(deletion, "basic,90,1"));
		CPPUNIT_ASSERT(config.search(0).reduce.strategy.algo == ReduceStrategy::reduce_linear);
		CPPUNIT_ASSERT(config.search(0).reduce.strategy.fReduce == 90);
		CPPUNIT_ASSERT(config.search(0).reduce.strategy.score == 1);

		CPPUNIT_ASSERT_EQUAL(0, config.setValue(deletion, "basic,102"));
	}
	void testSetShareMode() {
		ClaspCliConfig config;
		ClaspCliConfig::KeyType share = config.getKey(ClaspCliConfig::KEY_ROOT, "share");
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(share, "no"));
		CPPUNIT_ASSERT(config.shareMode == ContextParams::share_no);

		CPPUNIT_ASSERT_EQUAL(1, config.setValue(share, "problem"));
		CPPUNIT_ASSERT(config.shareMode == ContextParams::share_problem);

		CPPUNIT_ASSERT_EQUAL(1, config.setValue(share, "LEARNT"));
		CPPUNIT_ASSERT(config.shareMode == ContextParams::share_learnt);
	}

	void testSetTrMode() {
		ClaspCliConfig config;
		ClaspCliConfig::KeyType tr = config.getKey(ClaspCliConfig::KEY_ROOT, "asp.trans_ext");
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(tr, "no"));
		CPPUNIT_ASSERT(config.asp.erMode == Asp::LogicProgram::mode_native);
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(tr, "scc"));
		CPPUNIT_ASSERT(config.asp.erMode == Asp::LogicProgram::mode_transform_scc);
		tr = config.getKey(ClaspCliConfig::KEY_ROOT, "tester.asp.trans_ext");
		CPPUNIT_ASSERT_EQUAL(ClaspCliConfig::KEY_INVALID, tr);
		CPPUNIT_ASSERT(config.setValue(tr, "scc") == -1);
		CPPUNIT_ASSERT_THROW(config.setValue("tester.asp.trans_ext", "scc"), std::logic_error);
	}
	void testSetEnumMode() {
		ClaspCliConfig config;
		ClaspCliConfig::KeyType eMode = config.getKey(ClaspCliConfig::KEY_ROOT, "solve.enum_mode");

		CPPUNIT_ASSERT_EQUAL(1, config.setValue(eMode, "brave"));
		CPPUNIT_ASSERT(config.solve.enumMode == EnumOptions::enum_brave);
		CPPUNIT_ASSERT_EQUAL(0, config.setValue(eMode, "consequences"));

		CPPUNIT_ASSERT_EQUAL(true, config.setValue("solve.opt_mode", "ignore"));
		CPPUNIT_ASSERT(config.solve.optMode == MinimizeMode_t::ignore);

		CPPUNIT_ASSERT_THROW(config.setValue("tester.solve.enum_mode", "brave"), std::logic_error);
	}
	void testSetOptStrategy() {
		ClaspCliConfig config;
		ClaspCliConfig::KeyType oStrat = config.getKey(ClaspCliConfig::KEY_ROOT, "solver.opt_strategy");
		std::string val;
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(oStrat, "bb"));
		CPPUNIT_ASSERT(config.getValue(oStrat, val) > 0 && val == "bb,lin");
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(oStrat, "bb,INC"));
		CPPUNIT_ASSERT(config.getValue(oStrat, val) > 0 && val == "bb,inc");
		CPPUNIT_ASSERT(config.solver(0).opt.type == 0u && config.solver(0).opt.algo == OptParams::bb_inc);
		CPPUNIT_ASSERT_EQUAL(0, config.setValue(oStrat, "bb,foo"));

		CPPUNIT_ASSERT_EQUAL(1, config.setValue(oStrat, "usc"));
		CPPUNIT_ASSERT(config.getValue(oStrat, val) > 0 && val == "usc,oll");
		CPPUNIT_ASSERT(config.solver(0).opt.type == OptParams::type_usc);
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(oStrat, "usc,k"));
		CPPUNIT_ASSERT(config.getValue(oStrat, val) > 0 && val == "usc,k,0");
		CPPUNIT_ASSERT(config.solver(0).opt.type == OptParams::type_usc);
		CPPUNIT_ASSERT(config.solver(0).opt.algo == OptParams::usc_k && config.solver(0).opt.kLim == 0);

		CPPUNIT_ASSERT_EQUAL(1, config.setValue(oStrat, "usc,k,4"));
		CPPUNIT_ASSERT(config.getValue(oStrat, val) > 0 && val == "usc,k,4");
		CPPUNIT_ASSERT(config.solver(0).opt.type == OptParams::type_usc);
		CPPUNIT_ASSERT(config.solver(0).opt.algo == OptParams::usc_k && config.solver(0).opt.kLim == 4);

		CPPUNIT_ASSERT_EQUAL(0, config.setValue(oStrat, "usc,foo"));

		CPPUNIT_ASSERT_EQUAL(1, config.setValue(oStrat, "usc,oll,3"));
		CPPUNIT_ASSERT(config.solver(0).opt.opts == 3u);
		CPPUNIT_ASSERT(config.getValue(oStrat, val) > 0 && val == "usc,oll,disjoint,succinct");
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(oStrat, "usc,oll,stratify,disjoint"));
		CPPUNIT_ASSERT(config.solver(0).opt.opts == uint32(OptParams::usc_disjoint|OptParams::usc_stratify));
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(oStrat, "usc,oll,0"));
		CPPUNIT_ASSERT(config.getValue(oStrat, val) > 0 && val == "usc,oll");
		CPPUNIT_ASSERT_EQUAL(0, config.setValue(oStrat, "usc,oll,1,2"));

		ClaspCliConfig::KeyType uShrink = config.getKey(ClaspCliConfig::KEY_ROOT, "solver.opt_usc_shrink");
		CPPUNIT_ASSERT(config.getValue(uShrink, val) > 0 && val == "no");
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(uShrink, "exp"));
		CPPUNIT_ASSERT(config.getValue(uShrink, val) > 0 && val == "exp,10");
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(uShrink, "bin,12"));
		CPPUNIT_ASSERT(config.getValue(uShrink, val) > 0 && val == "bin,12");
	}
	void testSetLegacyOptStrategy() {
		ClaspCliConfig config;
		ClaspCliConfig::KeyType oStrat = config.getKey(ClaspCliConfig::KEY_ROOT, "solver.opt_strategy");
		std::string val;
		// clasp-3.0:
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(oStrat, "1"));
		CPPUNIT_ASSERT(config.getValue(oStrat, val) > 0 && val == "bb,hier");
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(oStrat, "5"));
		CPPUNIT_ASSERT(config.getValue(oStrat, val) > 0 && val == "usc,oll,disjoint");
		// clasp-3.1
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(oStrat, "bb,1"));
		CPPUNIT_ASSERT(config.getValue(oStrat, val) > 0 && val == "bb,hier");
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(oStrat, "usc,7"));
		CPPUNIT_ASSERT(config.getValue(oStrat, val) > 0 && val == "usc,pmres,disjoint,succinct");
		// clasp-3.2:
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(oStrat, "usc,15"));
		CPPUNIT_ASSERT(config.getValue(oStrat, val) > 0 && val == "usc,pmres,disjoint,succinct,stratify");
	}
	void testSetSolveLimit() {
		ClaspCliConfig config;
		ClaspCliConfig::KeyType limit = config.getKey(ClaspCliConfig::KEY_ROOT, "solve.solve_limit");
		std::string val;
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(limit, "0"));
		CPPUNIT_ASSERT(config.getValue(limit, val) > 0);
		CPPUNIT_ASSERT_EQUAL(std::string("0,umax"), val);
		CPPUNIT_ASSERT(config.solve.limit.conflicts == 0);

		CPPUNIT_ASSERT_EQUAL(1, config.setValue(limit, "no"));
		CPPUNIT_ASSERT(config.getValue(limit, val) > 0);
		CPPUNIT_ASSERT(config.solve.limit.conflicts == UINT64_MAX);
		CPPUNIT_ASSERT_EQUAL(std::string("umax,umax"), val);
	}

#if CLASP_HAS_THREADS
	void testSetParallelMode() {
		ClaspCliConfig config;
		ClaspCliConfig::KeyType pMode = config.getKey(ClaspCliConfig::KEY_ROOT, "solve.parallel_mode");
		CPPUNIT_ASSERT_EQUAL(0, config.setValue(pMode, "0"));
		CPPUNIT_ASSERT_EQUAL(uint32(1), config.solve.algorithm.threads);
		CPPUNIT_ASSERT(SolveOptions::Algorithm::mode_compete == config.solve.algorithm.mode);

		CPPUNIT_ASSERT_EQUAL(1, config.setValue(pMode, "10"));
		CPPUNIT_ASSERT_EQUAL(uint32(10), config.solve.algorithm.threads);
		CPPUNIT_ASSERT(SolveOptions::Algorithm::mode_compete == config.solve.algorithm.mode);

		CPPUNIT_ASSERT_EQUAL(1, config.setValue(pMode, "10,split"));
		CPPUNIT_ASSERT_EQUAL(uint32(10), config.solve.algorithm.threads);
		CPPUNIT_ASSERT(SolveOptions::Algorithm::mode_split == config.solve.algorithm.mode);

		CPPUNIT_ASSERT_EQUAL(0, config.setValue(pMode, "65"));
	}
	void testSetDistribute() {
		ClaspCliConfig config;
		ClaspCliConfig::KeyType distribute = config.getKey(ClaspCliConfig::KEY_ROOT, "solve.distribute");
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(distribute, "0"));
		CPPUNIT_ASSERT_EQUAL(0, config.setValue(distribute, "0,1"));
		CPPUNIT_ASSERT_EQUAL(1, config.setValue(distribute, "conflict"));
		CPPUNIT_ASSERT(Distributor::Policy::conflict == config.solve.distribute.types);
		CPPUNIT_ASSERT(4 == config.solve.distribute.lbd);

		CPPUNIT_ASSERT_EQUAL(1, config.setValue(distribute, "loop,2"));
		CPPUNIT_ASSERT(Distributor::Policy::loop == config.solve.distribute.types);
		CPPUNIT_ASSERT(2 == config.solve.distribute.lbd);

		CPPUNIT_ASSERT_EQUAL(1, config.setValue(distribute, "all,2,123"));
		CPPUNIT_ASSERT(Distributor::Policy::all == config.solve.distribute.types);
		CPPUNIT_ASSERT(2 == config.solve.distribute.lbd);
		CPPUNIT_ASSERT(123 == config.solve.distribute.size);
	}
	void testSetIntegrate() {
		ClaspCliConfig config;
		ClaspCliConfig::KeyType integrate = config.getKey(ClaspCliConfig::KEY_ROOT, "solve.integrate");

		CPPUNIT_ASSERT_EQUAL(0, config.setValue(integrate, "0"));
		CPPUNIT_ASSERT_EQUAL(0, config.setValue(integrate, "no"));

		CPPUNIT_ASSERT_EQUAL(1, config.setValue(integrate, "active"));
		CPPUNIT_ASSERT(SolveOptions::Integration::filter_heuristic == config.solve.integrate.filter);
		CPPUNIT_ASSERT(1024 == config.solve.integrate.grace);
		CPPUNIT_ASSERT(SolveOptions::Integration::topo_all == config.solve.integrate.topo);

		CPPUNIT_ASSERT_EQUAL(1, config.setValue(integrate, "unsat,100"));
		CPPUNIT_ASSERT(SolveOptions::Integration::filter_sat == config.solve.integrate.filter);
		CPPUNIT_ASSERT(100 == config.solve.integrate.grace);
		CPPUNIT_ASSERT(SolveOptions::Integration::topo_all == config.solve.integrate.topo);

		CPPUNIT_ASSERT_EQUAL(1, config.setValue(integrate, "gp,200,cubeX"));
		CPPUNIT_ASSERT(SolveOptions::Integration::filter_gp == config.solve.integrate.filter);
		CPPUNIT_ASSERT(200 == config.solve.integrate.grace);
		CPPUNIT_ASSERT(SolveOptions::Integration::topo_cubex == config.solve.integrate.topo);

		CPPUNIT_ASSERT_EQUAL(1, config.setValue(integrate, "gp,77,cube"));
		CPPUNIT_ASSERT(SolveOptions::Integration::filter_gp == config.solve.integrate.filter);
		CPPUNIT_ASSERT(77 == config.solve.integrate.grace);
		CPPUNIT_ASSERT(SolveOptions::Integration::topo_cube == config.solve.integrate.topo);
	}
#endif

	void testConfigQueryStrValues() {
		ClaspCliConfig config;
		std::string out;
		CPPUNIT_ASSERT(config.getValue(config.getKey(ClaspCliConfig::KEY_TESTER, "configuration"), out) == -1);
		config.setValue("configuration", "tweety");
		CPPUNIT_ASSERT(config.getValue("configuration") == "tweety");

		CPPUNIT_ASSERT(config.getValue("solver.heuristic") == "vsids,92");
		CPPUNIT_ASSERT(config.getValue("solver.strengthen") == "recursive,0,0");
		CPPUNIT_ASSERT(config.getValue("solver.deletion") == "basic,50,0");
		CPPUNIT_ASSERT(config.getValue("solver.restarts") == "l,60");
		CPPUNIT_ASSERT(config.getValue("solver.loops") == "shared");
		CPPUNIT_ASSERT(config.getValue("solver.partial_check") == "no");

		CPPUNIT_ASSERT(config.getValue("sat_prepro") == "no");

		std::vector<std::string> leafs;
		traverseKey(config, leafs, ClaspCliConfig::KEY_ROOT, "");
		std::string val;
		for (uint32 i = 0; i != leafs.size(); ++i) {
			if (config.hasValue(leafs[i].c_str())) {
				val = config.getValue(leafs[i].c_str());
				CPPUNIT_ASSERT(config.setValue(leafs[i].c_str(), val.c_str()));
			}
		}
		config.setValue("sat_prepro", "2,20,25");
		CPPUNIT_ASSERT(std::strncmp(config.getValue("sat_prepro").c_str(), "2,20,25", std::strlen("2,20,25")) == 0);
		config.reset();
		std::string x = config.getValue("solver.del_cfl");
		CPPUNIT_ASSERT(x == "no" || x == "0");
		x = config.getValue("solver.del_grow");

		CPPUNIT_ASSERT(config.setValue("solver.del_grow", x.c_str()));
		x = config.getValue("solve.opt_bound");
		CPPUNIT_ASSERT(x == "no");
		config.setValue("solve.opt_bound", "122");
		CPPUNIT_ASSERT(config.getValue("solve.opt_bound") == "122");
		config.setValue("solver.del_init", "3,100,200");
		CPPUNIT_ASSERT(config.getValue("solver.del_init") == "3,100,200");

		CPPUNIT_ASSERT(!config.hasValue("tester.learn_explicit"));
		config.setValue("tester.learn_explicit", "1");
		CPPUNIT_ASSERT(config.hasValue("tester.learn_explicit"));

		CPPUNIT_ASSERT_THROW(config.getValue("enum"), std::logic_error);
		CPPUNIT_ASSERT_THROW(config.getValue("tester.solve.opt_bound"), std::logic_error);
	}

	void testSetOptBound() {
		ClaspCliConfig config;
		std::string bound = config.getValue("solve.opt_bound");
		CPPUNIT_ASSERT(bound == "no");
		CPPUNIT_ASSERT_EQUAL(true, config.setValue("solve.opt_bound", "100"));
		CPPUNIT_ASSERT((bound = config.getValue("solve.opt_bound")) == "100");
		CPPUNIT_ASSERT_EQUAL(true, config.setValue("solve.opt_bound", "50,20"));
		bound = config.getValue("solve.opt_bound");
		CPPUNIT_ASSERT_EQUAL(bound, std::string("50,20"));
		CPPUNIT_ASSERT_EQUAL(true, config.setValue("solve.opt_bound", "no"));
		CPPUNIT_ASSERT((bound = config.getValue("solve.opt_bound")) == "no");

		CPPUNIT_ASSERT_EQUAL(true, config.setValue("solve.opt_bound", "50,20"));
		CPPUNIT_ASSERT_EQUAL(false, config.setValue("solve.opt_bound", "a,b"));
		bound = config.getValue("solve.opt_bound");
		CPPUNIT_ASSERT_EQUAL(bound, std::string("50,20"));
	}
private:
	bool isValidOption(const ClaspCliConfig& c, const std::string& k) const {
		return ClaspCliConfig::isLeafKey(c.getKey(ClaspCliConfig::KEY_ROOT, k.c_str()));
	}
	void traverseKey(const ClaspCliConfig& c, std::vector<std::string>& keys, ClaspCliConfig::KeyType k, std::string accu) {
		if (k == ClaspCliConfig::KEY_INVALID) { throw std::runtime_error("Invalid key"); }
		if (ClaspCliConfig::isLeafKey(k)) {
			keys.push_back(accu);
		}
		else {
			int i = 0;
			if (!accu.empty()) { accu += '.'; }
			std::size_t pop = accu.size();
			for (const char* x = 0; (x = c.getSubkey(k, i)) != 0; ++i, accu.resize(pop)) {
				accu += x;
				traverseKey(c, keys, c.getKey(k, x), accu);
			}
		}
	}
};

CPPUNIT_TEST_SUITE_REGISTRATION(CliTest);
} } }

