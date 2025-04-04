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
#include <clasp/model_enumerators.h>

#include <clasp/clause.h>
#include <clasp/logic_program.h>
#include <clasp/solve_algorithms.h>
#include <clasp/solver.h>
#include <clasp/unfounded_check.h>

#include <catch2/catch_test_macros.hpp>

using namespace std;
namespace Clasp::Test {
using namespace Clasp::Asp;
template <size_t S>
static void checkModels(Solver& s, Enumerator& e, uint32_t expected, Literal (*x)[S]) {
    for (uint32_t seenModels = 0;; ++x, e.update(s)) {
        if (auto val = s.search(); val == value_true && ++seenModels <= expected) {
            e.commitModel(s);
            for (auto i : irange(S)) {
                auto lit = x[0][i];
                REQUIRE(s.isTrue(lit));
            }
        }
        else {
            REQUIRE(seenModels == expected);
            break;
        }
    }
}

TEST_CASE("Enumerator", "[enum]") {
    SharedContext ctx;
    Solver&       solver = *ctx.master();
    LogicProgram  lp;
    SECTION("testProjectToOutput") {
        auto v1 = ctx.addVar(VarType::atom);
        auto v2 = ctx.addVar(VarType::atom);
        auto v3 = ctx.addVar(VarType::atom);
        ctx.output.add("a", posLit(v1));
        ctx.output.add("_aux", posLit(v2));
        ctx.output.add("b", posLit(v3));
        ctx.startAddConstraints();
        ModelEnumerator e;
        e.setStrategy(ModelEnumerator::strategy_backtrack, ModelEnumerator::project_enable_simple, '_');
        e.init(ctx);
        ctx.endInit();
        REQUIRE(ctx.output.projectMode() == ProjectMode::output);
        REQUIRE(e.project(v1));
        REQUIRE(e.project(v3));

        ctx.detach(0);
    }
    SECTION("testProjectExplicit") {
        auto v1 = ctx.addVar(VarType::atom);
        auto v2 = ctx.addVar(VarType::atom);
        auto v3 = ctx.addVar(VarType::atom);
        ctx.output.add("a", posLit(v1));
        ctx.output.add("_aux", posLit(v2));
        ctx.output.add("b", posLit(v3));
        ctx.output.addProject(posLit(v2));
        ctx.output.addProject(posLit(v3));
        REQUIRE(ctx.output.projectMode() == ProjectMode::project);

        ctx.startAddConstraints();
        ModelEnumerator e;
        e.setStrategy(ModelEnumerator::strategy_backtrack, ModelEnumerator::project_enable_simple, '_');
        e.init(ctx);
        ctx.endInit();
        REQUIRE_FALSE(e.project(v1));
        REQUIRE(e.project(v2));
        REQUIRE(e.project(v3));
        ctx.detach(0);
    }
    SECTION("testMiniProject") {
        lpAdd(lp.start(ctx, LogicProgram::AspOptions().noEq().noScc()), "{x1;x2;x3}.\n"
                                                                        "x3 :- not x1.\n"
                                                                        "x3 :- not x2.\n"
                                                                        "#minimize{x3}.");
        lp.addAtomOutput(1, "a");
        lp.addAtomOutput(2, "b");
        lp.addAtomOutput(3, "_ignore_in_project");
        REQUIRE(lp.endProgram());
        ModelEnumerator e;
        e.setStrategy(ModelEnumerator::strategy_backtrack, ModelEnumerator::project_enable_simple);
        e.init(ctx);
        ctx.endInit();

        solver.assume(lp.getLiteral(1));
        solver.propagate();
        solver.assume(lp.getLiteral(2));
        solver.propagate();
        solver.assume(lp.getLiteral(3));
        solver.propagate();
        REQUIRE(solver.numVars() == solver.numAssignedVars());
        e.commitModel(solver);
        bool ok = e.update(solver) && solver.propagate();
        REQUIRE_FALSE(ok);
        solver.backtrack();
        REQUIRE((not solver.propagate() && not solver.resolveConflict()));
    }

    SECTION("testProjectBug") {
        lpAdd(lp.start(ctx, LogicProgram::AspOptions().noEq().noScc()), "{x1;x2;x4}.\n"
                                                                        "x5 :- x1, x4.\n"
                                                                        "x6 :- x2, x4.\n"
                                                                        "x3 :- x5, x6.\n");
        Var_t x = 1, y = 2, z = 3, hp = 4;
        lp.addAtomOutput(x, "x").addAtomOutput(y, "y").addAtomOutput(z, "z").addAtomOutput(hp, "_p");
        REQUIRE(lp.endProgram());
        ModelEnumerator e;
        e.setStrategy(ModelEnumerator::strategy_backtrack, ModelEnumerator::project_enable_full);
        e.init(ctx);
        ctx.endInit();

        solver.assume(lp.getLiteral(x));
        solver.propagate();
        solver.assume(lp.getLiteral(y));
        solver.propagate();
        solver.assume(lp.getLiteral(hp));
        solver.propagate();
        REQUIRE(solver.numVars() == solver.numAssignedVars());
        REQUIRE((e.commitModel(solver) && e.update(solver)));

        solver.undoUntil(0);
        uint32_t numT = 0;
        if (solver.value(lp.getLiteral(x).var()) == value_free) {
            solver.assume(lp.getLiteral(x)) && solver.propagate();
            ++numT;
        }
        else if (solver.isTrue(lp.getLiteral(x))) {
            ++numT;
        }
        if (solver.value(lp.getLiteral(y).var()) == value_free) {
            solver.assume(lp.getLiteral(y)) && solver.propagate();
            ++numT;
        }
        else if (solver.isTrue(lp.getLiteral(y))) {
            ++numT;
        }
        if (solver.value(lp.getLiteral(hp).var()) == value_free) {
            solver.assume(lp.getLiteral(hp)) && solver.propagate();
        }
        if (solver.isTrue(lp.getLiteral(z))) {
            ++numT;
        }
        REQUIRE(numT < 3);
    }

    SECTION("testProjectRestart") {
        lpAdd(lp.start(ctx, LogicProgram::AspOptions().noEq().noScc()), "{x1;x2;x3}.");
        lp.addAtomOutput(1, "a").addAtomOutput(2, "b");
        REQUIRE(lp.endProgram());
        ModelEnumerator e;
        e.setStrategy(ModelEnumerator::strategy_backtrack, ModelEnumerator::project_enable_full);
        e.init(ctx);
        ctx.endInit();

        solver.assume(lp.getLiteral(1));
        solver.propagate();
        solver.assume(lp.getLiteral(2));
        solver.propagate();
        solver.assume(lp.getLiteral(3));
        solver.propagate();
        solver.strategies().restartOnModel = true;
        REQUIRE(solver.numVars() == solver.numAssignedVars());
        REQUIRE(e.commitModel(solver));
        REQUIRE(e.update(solver));
        REQUIRE(solver.isFalse(lp.getLiteral(2)));
    }
    SECTION("testProjectWithBacktracking") {
        lpAdd(lp.start(ctx, LogicProgram::AspOptions().noEq().noScc()), "{x1, x2, x3}."
                                                                        "#output a : x1.");
        REQUIRE(lp.endProgram());
        ModelEnumerator e;
        e.setStrategy(ModelEnumerator::strategy_backtrack, ModelEnumerator::project_enable_full);
        e.init(ctx);
        ctx.endInit();

        solver.assume(lp.getLiteral(2));
        solver.propagate();
        solver.assume(lp.getLiteral(3));
        solver.propagate();
        // x2@1 -x3
        solver.backtrack();
        // x1@1 -x3 a@2
        solver.assume(lp.getLiteral(1));
        solver.propagate();
        REQUIRE(solver.numVars() == solver.numAssignedVars());
        REQUIRE(e.commitModel(solver));
        e.update(solver);
        solver.undoUntil(0);
        while (solver.backtrack()) { ; }
        REQUIRE(solver.isFalse(lp.getLiteral(1)));
    }
    SECTION("testTerminateRemovesWatches") {
        lpAdd(lp.start(ctx, LogicProgram::AspOptions().noEq().noScc()), "{x1;x2;x3;x4}.");
        REQUIRE(lp.endProgram());
        ModelEnumerator e(ModelEnumerator::strategy_record);
        e.init(ctx);
        REQUIRE(ctx.endInit());

        solver.assume(lp.getLiteral(1)) && solver.propagate();
        solver.assume(lp.getLiteral(2)) && solver.propagate();
        solver.assume(lp.getLiteral(3)) && solver.propagate();
        solver.assume(lp.getLiteral(4)) && solver.propagate();
        REQUIRE(uint32_t(0) == solver.numFreeVars());
        e.commitModel(solver) && e.update(solver);
        uint32_t numW = solver.numWatches(lp.getLiteral(1)) + solver.numWatches(lp.getLiteral(2)) +
                        solver.numWatches(lp.getLiteral(3)) + solver.numWatches(lp.getLiteral(4));
        REQUIRE(numW > 0);
        ctx.detach(solver);
        numW = solver.numWatches(lp.getLiteral(1)) + solver.numWatches(lp.getLiteral(2)) +
               solver.numWatches(lp.getLiteral(3)) + solver.numWatches(lp.getLiteral(4));
        REQUIRE(numW == 0);
    }

    SECTION("testParallelRecord") {
        lpAdd(lp.start(ctx, LogicProgram::AspOptions().noEq().noScc()), "{x1;x2;x3;x4}.");
        REQUIRE(lp.endProgram());
        ctx.setConcurrency(2);
        ModelEnumerator e(ModelEnumerator::strategy_record);
        e.init(ctx);
        Solver& solver2 = ctx.pushSolver();
        ctx.endInit(true);

        solver.assume(lp.getLiteral(1)) && solver.propagate();
        solver.assume(lp.getLiteral(2)) && solver.propagate();
        solver.assume(lp.getLiteral(3)) && solver.propagate();
        solver.assume(lp.getLiteral(4)) && solver.propagate();
        REQUIRE(uint32_t(0) == solver.numFreeVars());
        e.commitModel(solver) && e.update(solver);
        solver.undoUntil(0);

        REQUIRE(e.update(solver2));

        solver2.assume(lp.getLiteral(1)) && solver2.propagate();
        solver2.assume(lp.getLiteral(2)) && solver2.propagate();
        solver2.assume(lp.getLiteral(3)) && solver2.propagate();
        REQUIRE((solver2.isFalse(lp.getLiteral(4)) && solver2.propagate()));
        REQUIRE(uint32_t(0) == solver2.numFreeVars());
        e.commitModel(solver2) && e.update(solver2);
        solver.undoUntil(0);

        REQUIRE(e.update(solver));

        solver.assume(lp.getLiteral(1)) && solver.propagate();
        solver.assume(lp.getLiteral(2)) && solver.propagate();
        REQUIRE(solver.isFalse(lp.getLiteral(3)));

        ctx.detach(solver2);
        ctx.detach(solver);
        solver2.undoUntil(0);
        ctx.attach(solver2);
        solver2.assume(lp.getLiteral(1)) && solver2.propagate();
        solver2.assume(lp.getLiteral(2)) && solver2.propagate();
        solver2.assume(lp.getLiteral(3)) && solver2.propagate();
        REQUIRE(solver2.value(lp.getLiteral(4).var()) == value_free);
    }

    SECTION("testParallelUpdate") {
        lpAdd(lp.start(ctx, LogicProgram::AspOptions().noEq().noScc()), "{x1;x2;x3}. #minimize{x2}.");
        REQUIRE(lp.endProgram());
        ctx.setConcurrency(2);
        ModelEnumerator e(ModelEnumerator::strategy_record);
        e.init(ctx);

        Solver& solver2 = ctx.pushSolver();
        ctx.endInit(true);

        // x1
        solver.assume(lp.getLiteral(1));
        solver.pushRootLevel(1);
        solver.propagate();
        // ~x2
        solver2.assume(~lp.getLiteral(1));
        solver2.pushRootLevel(1);
        solver2.propagate();

        // M1: ~x2, x3
        solver.assume(~lp.getLiteral(2));
        solver.propagate();
        solver.assume(lp.getLiteral(3));
        solver.propagate();
        REQUIRE(uint32_t(0) == solver.numFreeVars());
        e.commitModel(solver);
        solver.undoUntil(0);
        e.update(solver);

        // M2: ~x2, ~x3
        solver2.assume(~lp.getLiteral(2));
        solver2.propagate();
        solver2.assume(~lp.getLiteral(3));
        solver2.propagate();
        // M2 is NOT VALID!
        REQUIRE(false == e.update(solver2));
    }

    SECTION("testTagLiteral") {
        ModelEnumerator e;
        ctx.addVar(VarType::atom);
        ctx.addVar(VarType::atom);
        ctx.startAddConstraints();
        e.init(ctx);
        ctx.endInit();
        REQUIRE(2 == ctx.numVars());
        e.start(*ctx.master());
        ctx.master()->pushTagVar(true);
        REQUIRE(2 == ctx.numVars());
        REQUIRE(3 == ctx.master()->numVars());
        REQUIRE(ctx.master()->isTrue(ctx.master()->tagLiteral()));
    }
    SECTION("testIgnoreTagLiteralInPath") {
        auto a = ctx.addVar(VarType::atom);
        ctx.addVar(VarType::atom);
        Solver& s1 = ctx.startAddConstraints();
        Solver& s2 = ctx.pushSolver();
        ctx.endInit();
        ctx.attach(s2);
        s1.pushRoot(posLit(a));
        s1.pushTagVar(true);
        REQUIRE((s1.rootLevel() == 2 && s1.isTrue(s1.tagLiteral())));
        LitVec path;
        s1.copyGuidingPath(path);
        REQUIRE((path.size() == 1 && path.back() == posLit(a)));
    }
    SECTION("testSplittable") {
        auto    a = ctx.addVar(VarType::atom);
        auto    b = ctx.addVar(VarType::atom);
        auto    c = ctx.addVar(VarType::atom);
        Solver& s = ctx.startAddConstraints();
        ctx.endInit();
        s.pushRoot(posLit(a));
        REQUIRE_FALSE(s.splittable());
        s.assume(posLit(b)) && s.propagate();
        REQUIRE(s.splittable());
        s.pushTagVar(true);
        REQUIRE_FALSE(s.splittable());
        s.assume(posLit(c)) && s.propagate();
        REQUIRE(s.splittable());
        s.pushRootLevel();
        auto aux = s.pushAuxVar();
        s.assume(posLit(aux)) && s.propagate();
        REQUIRE_FALSE(s.splittable());
    }
    SECTION("testLearnStepLiteral") {
        ctx.requestStepVar();
        auto a = ctx.addVar(VarType::atom);
        ctx.addVar(VarType::atom);
        Solver& s1 = ctx.startAddConstraints();
        ctx.pushSolver();
        ctx.endInit(true);
        ClauseCreator cc(&s1);
        cc.start(ConstraintType::conflict).add(posLit(a)).add(~ctx.stepLiteral()).end();
        ctx.unfreeze();
        ctx.endInit(true);
        s1.pushRoot(negLit(a));
        REQUIRE(s1.value(ctx.stepLiteral().var()) == value_free);
    }

    SECTION("testAssignStepLiteral") {
        ctx.requestStepVar();
        ctx.addVar(VarType::atom);
        ctx.addVar(VarType::atom);
        Solver& s = ctx.startAddConstraints();
        ctx.endInit();
        REQUIRE(s.value(ctx.stepLiteral().var()) == value_free);
        ctx.addUnary(ctx.stepLiteral());
        REQUIRE(s.value(ctx.stepLiteral().var()) != value_free);
        ctx.unfreeze();
        ctx.endInit();
        REQUIRE(s.value(ctx.stepLiteral().var()) == value_free);
    }

    SECTION("testModelHeuristicIsUsed") {
        BasicSatConfig config;
        config.addSolver(0).opt.heus       = OptParams::heu_model;
        config.addSolver(0).restartOnModel = true;
        ctx.setConfiguration(&config);
        lpAdd(lp.start(ctx), "{x1;x2;x3}.\n"
                             "#minimize{x1,x2,x3}.");
        REQUIRE(lp.endProgram());
        ModelEnumerator e;
        e.init(ctx);
        ctx.endInit();
        e.start(solver);
        solver.assume(lp.getLiteral(1)) && solver.propagate();
        solver.assume(lp.getLiteral(2)) && solver.propagate();
        solver.assume(lp.getLiteral(3)) && solver.propagate();
        REQUIRE(solver.numFreeVars() == 0);
        e.commitModel(solver);

        e.update(solver);
        REQUIRE(solver.numFreeVars() == 0);
        REQUIRE(solver.isFalse(lp.getLiteral(1)));
        REQUIRE(solver.isFalse(lp.getLiteral(2)));
        REQUIRE(solver.isFalse(lp.getLiteral(3)));
    }
    SECTION("testDomCombineDef") {
        BasicSatConfig config;
        config.addSolver(0).heuId             = +HeuristicType::domain;
        config.addSolver(0).heuristic.domMod  = HeuParams::mod_false;
        config.addSolver(0).heuristic.domPref = HeuParams::pref_min | HeuParams::pref_show;
        ctx.setConfiguration(&config);
        lpAdd(lp.start(ctx), "{x1;x2;x3}.     \n"
                             "#output a : x1. \n"
                             "#output b : x2. \n"
                             "#output c : x3. \n"
                             "#minimize {not x1, not x2}.\n");
        REQUIRE(lp.endProgram());
        ModelEnumerator e;
        e.setStrategy(ModelEnumerator::strategy_record);
        e.init(ctx);
        ctx.endInit();
        e.start(solver);
        solver.search();
        REQUIRE(solver.isTrue(lp.getLiteral(1)));
        REQUIRE(solver.isTrue(lp.getLiteral(2)));
    }
    SECTION("testDomRecComplementShow") {
        BasicSatConfig config;
        config.addSolver(0).heuId             = +HeuristicType::domain;
        config.addSolver(0).heuristic.domMod  = HeuParams::mod_false;
        config.addSolver(0).heuristic.domPref = HeuParams::pref_show;
        ctx.setConfiguration(&config);
        lpAdd(lp.start(ctx), "{x1}.\n"
                             "#output a : x1.\n"
                             "#output b : not x1.\n");
        REQUIRE(lp.endProgram());
        ModelEnumerator e;
        e.setStrategy(ModelEnumerator::strategy_record, ModelEnumerator::project_dom_lits);
        e.init(ctx);
        ctx.endInit();
        REQUIRE(e.project(lp.getLiteral(1).var()));
        Literal models[][1] = {{~lp.getLiteral(1)}, {lp.getLiteral(1)}};
        e.start(solver);
        REQUIRE_NOTHROW(checkModels(solver, e, 2, models));
    }
    SECTION("testDomRecComplementAll") {
        BasicSatConfig config;
        config.addSolver(0).heuId             = +HeuristicType::domain;
        config.addSolver(0).heuristic.domMod  = HeuParams::mod_false;
        config.addSolver(0).heuristic.domPref = HeuParams::pref_atom;
        ctx.setConfiguration(&config);
        lpAdd(lp.start(ctx), "{x1}.\n"
                             "#output a : x1.\n"
                             "#output b : not x1.\n");
        REQUIRE(lp.endProgram());
        ModelEnumerator e;
        e.setStrategy(ModelEnumerator::strategy_record, ModelEnumerator::project_dom_lits);
        e.init(ctx);
        ctx.endInit();
        REQUIRE(e.project(lp.getLiteral(1).var()));
        Literal models[][1] = {{~lp.getLiteral(1)}, {lp.getLiteral(1)}};
        e.start(solver);
        REQUIRE_NOTHROW(checkModels(solver, e, 2, models));
    }
    SECTION("testDomRecAssume") {
        BasicSatConfig config;
        config.addSolver(0).heuId = +HeuristicType::domain;
        ctx.setConfiguration(&config);
        lp.start(ctx);
        lp.update();
        lpAdd(lp, "#external x3.\n"
                  "{x1;x2}.\n"
                  ":- not x1, not x2.\n"
                  "#heuristic x1 : x3.     [2,false]\n"
                  "#heuristic x2 : x3.     [1,false]\n"
                  "#heuristic x1 : not x3. [2,true]\n"
                  "#heuristic x2 : not x3. [1,true]\n");
        REQUIRE(lp.endProgram());
        Literal x1 = lp.getLiteral(1);
        Literal x2 = lp.getLiteral(2);
        Literal x3 = lp.getLiteral(3);
        LitVec  assume;
        lp.getAssumptions(assume);
        ctx.requestStepVar();
        ModelEnumerator e;
        e.setStrategy(ModelEnumerator::strategy_record, ModelEnumerator::project_dom_lits);
        Literal model[][2] = {
            {x1, x2},
            {~x1, x2},
            {~x2, x1},
        };
        {
            REQUIRE((assume.size() == 1 && assume[0] == ~x3));
            ctx.heuristic.assume = &assume;
            e.init(ctx);
            ctx.endInit();
            e.start(solver, assume);
            REQUIRE_NOTHROW(checkModels(solver, e, 1, model));
        }
        lp.update();
        lpAdd(lp, "#external x3. [true]\n");
        REQUIRE(lp.endProgram());
        assume.clear();
        lp.getAssumptions(assume);
        ctx.heuristic.assume = &assume;
        REQUIRE((assume.size() == 1 && assume[0] == x3));
        e.init(ctx);
        ctx.endInit();
        e.start(solver, assume);
        REQUIRE_NOTHROW(checkModels(solver, e, 2, model + 1));
    }
    SECTION("testNotAttached") {
        ctx.addVar(VarType::atom);
        ctx.addVar(VarType::atom);
        Solver& s = ctx.startAddConstraints();
        ctx.endInit();
        ModelEnumerator e;
        REQUIRE_THROWS_AS(e.start(s), std::logic_error);
    }
    SECTION("testSequentialSolve") {
        lpAdd(lp.start(ctx), "a :- not b. b :- not a.");
        REQUIRE(lp.endProgram());
        struct LogModel : ModelHandler {
            explicit LogModel(LogicProgram& lp) : prg(lp) {}
            bool onModel(const Solver&, const Model& m) override {
                auto a = prg.getLiteral(1);
                auto b = prg.getLiteral(2);
                if (m.isTrue(a)) {
                    models += "a";
                }
                if (m.isTrue(b)) {
                    models += "b";
                }
                models += "\n";
                return true;
            }
            std::string   models;
            LogicProgram& prg;
        };
        LogModel        onModel{lp};
        ModelEnumerator e;
        e.init(ctx);
        ctx.endInit();
        SequentialSolve solve;
        REQUIRE_FALSE(solve.solve(e, ctx, {}, &onModel));
        REQUIRE(onModel.models == "a\nb\n");
    }
}
} // namespace Clasp::Test
