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

#include <clasp/heuristics.h>

#include <clasp/clause.h>
#include <clasp/logic_program.h>
#include <clasp/lookahead.h>
#include <clasp/solver.h>

#include <catch2/catch_test_macros.hpp>

namespace Clasp::Test {
using namespace Clasp::Asp;
/////////////////////////////////////////////////////////////////////////////////////////
// Lookahead
/////////////////////////////////////////////////////////////////////////////////////////
TEST_CASE("Lookahead", "[heuristic][pp]") {
    SharedContext ctx;
    LogicProgram  lp;
    SECTION("body lookahead") {
        Solver& s = ctx.pushSolver();
        lpAdd(lp.start(ctx, LogicProgram::AspOptions().noEq().noScc()), "x1 :- not x1.\n"
                                                                        "x1 :- not x2, not x5.\n"
                                                                        "x2 :- not x5.\n"
                                                                        "x5 :- not x2.\n"
                                                                        "x1 :- not x3, not x6.\n"
                                                                        "x3 :- not x6.\n"
                                                                        "x6 :- not x3.\n"
                                                                        "x1 :- not x4, not x7.\n"
                                                                        "x4 :- not x7.\n"
                                                                        "x7 :- not x4.\n");

        REQUIRE((lp.endProgram() && ctx.endInit()) == true);
        s.addPost(new Lookahead(Lookahead::Params(VarType::body).addImps(false)));
        REQUIRE_FALSE(ctx.attach(s));
        ctx.detach(s, true);
        s.addPost(new Lookahead(Lookahead::Params(VarType::atom).addImps(false)));
        REQUIRE(ctx.attach(s));
        ctx.detach(s, true);
        s.addPost(new Lookahead(Lookahead::Params(VarType::hybrid).addImps(false)));
        REQUIRE_FALSE(ctx.attach(s));
    }
    SECTION("atom lookahead") {
        Solver& s = ctx.pushSolver();
        lpAdd(lp.start(ctx, LogicProgram::AspOptions().noEq().noScc()), "x1 :- x2, x3, x4, not x1.\n"
                                                                        "x2 :- not x5.\n"
                                                                        "x2 :- not x8.\n"
                                                                        "x5 :- not x8.\n"
                                                                        "x8 :- not x5.\n"
                                                                        "x3 :- not x6.\n"
                                                                        "x3 :- not x9.\n"
                                                                        "x6 :- not x9.\n"
                                                                        "x9 :- not x6.\n"
                                                                        "x4 :- not x7.\n"
                                                                        "x4 :- not x10.\n"
                                                                        "x7 :- not x10.\n"
                                                                        "x10 :- not x7.\n");

        REQUIRE((lp.endProgram() && ctx.endInit()) == true);
        Lookahead::Params p;
        p.addImps(false);
        s.addPost(new Lookahead(p.lookahead(VarType::body)));
        REQUIRE(ctx.attach(s));
        ctx.detach(s, true);
        s.addPost(new Lookahead(p.lookahead(VarType::atom)));
        REQUIRE_FALSE(ctx.attach(s));
        ctx.detach(s, true);
        s.addPost(new Lookahead(p.lookahead(VarType::hybrid)));
        REQUIRE_FALSE(ctx.attach(s));
    }

    SECTION("test lookahead bug: ") {
        UnitHeuristic* unit;
        ctx.master()->setHeuristic(unit = new UnitHeuristic());
        Literal a = posLit(ctx.addVar(VarType::atom));
        Literal b = posLit(ctx.addVar(VarType::atom));
        Literal c = posLit(ctx.addVar(VarType::atom));
        Literal e = posLit(ctx.addVar(VarType::atom));
        Literal f = posLit(ctx.addVar(VarType::atom));
        Solver& s = ctx.startAddConstraints(5);
        SECTION("simplify") {
            ctx.addBinary(a, b);
            s.addPost(new Lookahead(VarType::atom));
            ctx.endInit();
            ctx.addBinary(a, ~b);
            s.assume(e) && s.propagate();
            REQUIRE(unit->select(s));
            REQUIRE(s.isTrue(a));
            REQUIRE(s.seen(a.var()));
            REQUIRE(s.decisionLevel() == 1);
        }
        SECTION("deps are cleared") {
            ctx.addBinary(a, b);
            ctx.addBinary(b, c);
            ctx.addBinary(c, f);
            ctx.addUnary(e);
            s.addPost(new Lookahead(VarType::atom));
            ctx.endInit();
            // Assume without using lookahead (e.g. a random choice)
            s.assume(b);
            s.propagate();
            // Deps not cleared
            REQUIRE(unit->select(s));
            REQUIRE((s.isFalse(c) || s.isFalse(f)));
        }
        SECTION("no deps") {
            s.addPost(new Lookahead(VarType::atom));
            ctx.addBinary(a, b);
            ctx.addBinary(b, c);
            ctx.addUnary(e);
            ctx.endInit();
            REQUIRE(unit->select(s));
            REQUIRE(s.isFalse(b));
            s.undoUntil(0);
            s.simplify();
            REQUIRE(unit->select(s));
            REQUIRE(s.isFalse(b));
        }
        SECTION("no nant") {
            Lookahead::Params p(VarType::atom);
            p.restrictNant = true;
            s.addPost(new Lookahead(p));
            ctx.addBinary(a, b);
            ctx.addBinary(b, c);
            ctx.addBinary(~a, ~b);
            ctx.addBinary(~b, ~c);
            ctx.endInit();
            uint32_t n = s.numFreeVars();
            REQUIRE((unit->select(s) && s.numFreeVars() != n));
        }
        SECTION("stop conflict") {
            ctx.addBinary(a, b);
            s.addPost(new Lookahead(VarType::atom));
            ctx.endInit();
            struct StopConflict
                : public PostPropagator{bool propagateFixpoint(Solver & s, PostPropagator*)
                                            override{s.setStopConflict();
            return false;
        }
        [[nodiscard]] uint32_t priority() const override { return PostPropagator::priority_class_simple; }
    }
    *x = new StopConflict;
    s.addPost(x);
    REQUIRE((not unit->select(s) && s.hasConflict()));
    REQUIRE(s.search(0, 0) == value_false);
}
} // namespace Clasp::Test
SECTION("test strange seq") {
    Lookahead::Params p(VarType::body);
    p.limit(3);
    ctx.master()->setHeuristic(UnitHeuristic::restricted(new SelectFirst));
    Literal a = posLit(ctx.addVar(VarType::body));
    Literal b = posLit(ctx.addVar(VarType::atom));
    Solver& s = ctx.startAddConstraints();
    s.addPost(new Lookahead(p));
    ctx.endInit();
    s.force(a);
    s.simplify();
    bool x = s.decideNextBranch();
    REQUIRE((x == true && s.value(b.var()) != value_free));
}
SECTION("test strange seq2") {
    Lookahead::Params p(VarType::atom);
    p.limit(2);
    ctx.master()->setHeuristic(UnitHeuristic::restricted(new SelectFirst));
    Literal a = posLit(ctx.addVar(VarType::atom));
    Literal b = posLit(ctx.addVar(VarType::atom));
    Solver& s = ctx.startAddConstraints();
    s.addPost(new Lookahead(p));
    ctx.addBinary(a, b);
    ctx.addBinary(a, ~b);
    ctx.addBinary(~a, b);
    ctx.endInit();
    bool x = ctx.master()->decideNextBranch();
    REQUIRE((x == false && s.decisionLevel() == 0 && s.numFreeVars() == 0));
}
SECTION("test restricted heuristic is detached") {
    Lookahead::Params p(VarType::atom);
    p.limit(3);
    ctx.master()->setHeuristic(UnitHeuristic::restricted(new SelectFirst));
    Literal a = posLit(ctx.addVar(VarType::atom));
    Literal b = posLit(ctx.addVar(VarType::atom));
    posLit(ctx.addVar(VarType::atom));
    posLit(ctx.addVar(VarType::atom));
    Solver& s = ctx.startAddConstraints();
    s.addPost(new Lookahead(p));
    ctx.addBinary(a, b);
    ctx.endInit();
    bool x = ctx.master()->decideNextBranch();
    REQUIRE((x == true && s.decisionLevel() == 1));
    s.propagate();
    REQUIRE(s.getPost(PostPropagator::priority_reserved_look) != 0);
    s.setHeuristic(new SelectFirst);
    while (s.getPost(PostPropagator::priority_reserved_look) != nullptr) {
        s.propagate();
        s.decideNextBranch();
    }
}
} // namespace Clasp
/////////////////////////////////////////////////////////////////////////////////////////
// Lookback
/////////////////////////////////////////////////////////////////////////////////////////
TEST_CASE("Lookback heuristics", "[heuristic]") {
    SharedContext      ctx;
    DecisionHeuristic* heu;
    SECTION("test berkmin") {
        ctx.master()->setHeuristic(heu = new ClaspBerkmin());
        Literal a = posLit(ctx.addVar(VarType::atom));
        Literal b = posLit(ctx.addVar(VarType::atom));
        Literal c = posLit(ctx.addVar(VarType::atom));
        Literal d = posLit(ctx.addVar(VarType::atom));
        Literal e = posLit(ctx.addVar(VarType::atom));
        Literal f = posLit(ctx.addVar(VarType::atom));
        Literal g = posLit(ctx.addVar(VarType::atom));
        Solver& s = ctx.startAddConstraints();
        ctx.endInit();
        s.stats.conflicts = 1;
        LitVec up;
        heu->updateReason(s, up, Literal());
        up.push_back(a);
        heu->updateReason(s, up, a);
        up.clear();
        up.push_back(b);
        up.push_back(b);
        heu->updateReason(s, up, b);
        up.clear();
        heu->updateReason(s, up, e);
        s.assume(~b);
        s.assume(~c);
        s.assume(~d);
        ClauseCreator cc(&s);
        cc.start(ConstraintType::conflict).add(a).add(b).add(c).add(d).end();
        s.undoUntil(0);
        s.assume(~e);
        s.assume(~f);
        s.assume(~g);
        cc.start(ConstraintType::loop).add(d).add(e).add(f).add(g).end();
        s.undoUntil(0);
        REQUIRE(0u == s.numAssignedVars());
        REQUIRE(heu->select(s));
        REQUIRE(b == s.decision(1)); // from conflict clause
        s.propagate();
        REQUIRE(heu->select(s));
        REQUIRE(e == s.decision(2)); // from loop clause
        s.propagate();
        REQUIRE(heu->select(s));
        REQUIRE(a.var() == s.decision(3).var()); // highest activity
    }
    SECTION("test vmtf") {
        ctx.master()->setHeuristic(heu = new ClaspVmtf());
        LitVec lits;
        lits.push_back(posLit(ctx.addVar(VarType::atom)));
        lits.push_back(posLit(ctx.addVar(VarType::atom)));
        Solver& s = ctx.startAddConstraints();
        ctx.endInit();
        REQUIRE(heu->select(s));
        s.propagate();
        REQUIRE(heu->select(s));
        s.propagate();
        REQUIRE_FALSE(heu->select(s));
        s.undoUntil(0);
        REQUIRE(heu->selectRange(s, lits) == lits[0]);
        heu->updateReason(s, {}, lits[1]);
        REQUIRE(heu->selectRange(s, lits) == lits[1]);
    }
    SECTION("test vsids") {
        ctx.master()->setHeuristic(heu = new ClaspVsids());
        Literal a = posLit(ctx.addVar(VarType::atom));
        Literal b = posLit(ctx.addVar(VarType::atom));
        Solver& s = ctx.startAddConstraints();
        ctx.endInit();
        LitVec up;
        up.push_back(a);
        heu->updateReason(s, up, a);
        REQUIRE(heu->select(s));
        REQUIRE((s.decision(1) == ~a && s.propagate()));
        REQUIRE(heu->select(s));
        REQUIRE((s.decision(2) == ~b && s.propagate()));
        REQUIRE_FALSE(heu->select(s));
        s.undoUntil(0);
        up.resize(2);
        up[0] = a;
        up[1] = b;
        REQUIRE(heu->selectRange(s, up) == up[0]);
        WeightLitVec wlits;
        wlits.push_back({b, 3});
        heu->bump(s, wlits, 1.0);
        REQUIRE(heu->selectRange(s, up) == up[1]);
    }
    SECTION("test vsids aux") {
        ctx.master()->setHeuristic(heu = new ClaspVsids());
        ctx.addVar(VarType::atom);
        ctx.addVar(VarType::atom);
        Solver& s = ctx.startAddConstraints();
        ctx.endInit();
        auto   v = s.pushAuxVar();
        LitVec up;
        heu->updateReason(s, up, posLit(v));
        REQUIRE(heu->select(s));
        REQUIRE(s.value(v) != value_free);
        s.popAuxVar(1);
        REQUIRE(heu->select(s));
        REQUIRE(s.decision(1).var() != v);
    }
}
/////////////////////////////////////////////////////////////////////////////////////////
// Domain heuristic
/////////////////////////////////////////////////////////////////////////////////////////
inline Literal getDomLiteral(const LogicProgram& lp, Var_t a) { return lp.getLiteral((a), MapLit::refined); }
TEST_CASE("Domain Heuristic", "[heuristic][asp]") {
    SharedContext    ctx;
    LogicProgram     lp;
    DomainHeuristic* dom;
    ctx.master()->setHeuristic(dom = new DomainHeuristic);
    Solver& s = *ctx.master();
    SECTION("test sign") {
        Var_t a = 1;
        lp.start(ctx).addRule(HeadType::choice, {&a, 1u}, {});
        SECTION("pos") {
            lp.addDomHeuristic(a, DomModType::sign, 1, 1);
            REQUIRE((lp.endProgram() && ctx.endInit()));
            REQUIRE(s.decideNextBranch());
            REQUIRE(s.isTrue(lp.getLiteral(a)));
        }
        SECTION("neg") {
            lp.addDomHeuristic(a, DomModType::sign, -1, 1);
            REQUIRE((lp.endProgram() && ctx.endInit()));
            REQUIRE(s.decideNextBranch());
            REQUIRE(s.isTrue(~lp.getLiteral(a)));
        }
        SECTION("inv") {
            lpAdd(lp.start(ctx), "a :- not b.\n"
                                 "b :- not a.\n");
            lp.addDomHeuristic(a, DomModType::sign, 1, 1);
            REQUIRE((lp.endProgram() && ctx.endInit()));
            REQUIRE(s.decideNextBranch());
            REQUIRE(s.isTrue(lp.getLiteral(a)));
        }
    }
    SECTION("test level") {
        Var_t a = 1, b = 2;
        lpAdd(lp.start(ctx), "{a;b}.");
        lp.addDomHeuristic(a, DomModType::sign, 1, 1);
        lp.addDomHeuristic(b, DomModType::sign, 1, 1);
        lp.addDomHeuristic(a, DomModType::level, 10, 10);
        REQUIRE((lp.endProgram() && ctx.endInit()));

        REQUIRE(s.decideNextBranch());
        REQUIRE(s.isTrue(lp.getLiteral(a)));
    }
    SECTION("test dynamic rules") {
        Var_t a = 1, b = 2, c = 3;
        lpAdd(lp.start(ctx), "{a;b;c}.\n"
                             "d :- a, b.\n"
                             ":- d.\n");

        lp.addDomHeuristic(a, DomModType::sign, 1, 1);
        lp.addDomHeuristic(b, DomModType::sign, 1, 1);
        lp.addDomHeuristic(a, DomModType::level, 10, 10);
        lp.addDomHeuristic(c, DomModType::sign, 1, 1, b);
        lp.addDomHeuristic(c, DomModType::sign, -1, 1, Asp::id(Potassco::neg(b)));

        REQUIRE((lp.endProgram() && ctx.endInit()));
        REQUIRE(s.decideNextBranch());
        REQUIRE(s.isTrue(lp.getLiteral(a)));
        s.propagate();
        REQUIRE(s.isFalse(lp.getLiteral(b)));

        REQUIRE(s.decideNextBranch());
        REQUIRE(s.isTrue(~lp.getLiteral(c)));

        s.clearAssumptions();
        uint32_t n = s.numWatches(posLit(2));
        // test removal of watches
        ctx.master()->setHeuristic(new SelectFirst());
        REQUIRE(s.numWatches(posLit(2)) != n);
    }
    SECTION("test priority") {
        Var_t a = 1, b = 2, c = 3;
        SECTION("test 1") {
            lpAdd(lp.start(ctx), "{a;b;c}.\n"
                                 "d :- a, b.\n"
                                 ":- d.\n"
                                 "#heuristic b.         [1@1,sign]\n"
                                 "#heuristic a.         [10@10,true]\n"
                                 "#heuristic c.         [1@10,sign]\n"
                                 "#heuristic c : not b. [-1@20,sign]\n");
            REQUIRE((lp.endProgram() && ctx.endInit()));
            REQUIRE(s.decideNextBranch());
            REQUIRE(s.isTrue(lp.getLiteral(a)));
            s.propagate();
            REQUIRE(s.isFalse(lp.getLiteral(b)));

            REQUIRE(s.decideNextBranch());
            REQUIRE(s.isTrue(~lp.getLiteral(c)));
        }
        SECTION("test 2") {
            lpAdd(lp.start(ctx), "{a;b;c}.\n"
                                 "d :- a, b.\n"
                                 ":- d.\n"
                                 "#heuristic b.         [1@1,sign]\n"
                                 "#heuristic a.         [10@10,true]\n"
                                 "#heuristic c.         [1@30,sign]\n"
                                 "#heuristic c : not b. [-1@20,sign]\n");
            REQUIRE((lp.endProgram() && ctx.endInit()));
            REQUIRE(s.decideNextBranch());
            REQUIRE(s.isTrue(lp.getLiteral(a)));
            s.propagate();
            REQUIRE(s.isFalse(lp.getLiteral(b)));
            REQUIRE(s.decideNextBranch());
            REQUIRE(s.isTrue(lp.getLiteral(c)));
        }
        SECTION("test 3") {
            lpAdd(lp.start(ctx), "{a;c}.\n"
                                 "b :- a.\n"
                                 "#heuristic a.     [1@30,true]\n"
                                 "#heuristic a.     [1@20,false]\n"
                                 "#heuristic b.     [2@10,true]\n"
                                 "#heuristic b : c. [2@25,false]\n");
            REQUIRE((lp.endProgram() && ctx.endInit()));
            s.assume(lp.getLiteral(c)) && s.propagate();
            REQUIRE(s.decideNextBranch());
            REQUIRE(s.isTrue(~getDomLiteral(lp, b)));
        }
    }
    SECTION("test init") {
        Var_t a = 1, b = 2;
        lpAdd(lp.start(ctx), "{a;b}.\n"
                             "#heuristic a. [10@20,init]\n"
                             "#heuristic a. [50@10,init]\n"
                             "#heuristic b. [10@10,init]\n"
                             "#heuristic b. [30@20,init]\n");
        REQUIRE(lp.endProgram());
        ctx.heuristic.add(lp.getLiteral(a).var(), DomModType::init, 21, 20, lit_true);
        ctx.endInit();
        REQUIRE(s.decideNextBranch());
        REQUIRE(s.value(lp.getLiteral(b).var()) != value_free);
    }

    SECTION("test incremental") {
        lp.start(ctx).updateProgram();
        SECTION("test simple") {
            Var_t a = 1, b = 2, c = 3, d = 4, e = 5;
            ctx.master()->setHeuristic(new SelectFirst());
            lpAdd(lp, "{a;b;c;d}.\n");
            lp.addDomHeuristic(a, DomModType::level, 1, 1, c);
            lp.addDomHeuristic(b, DomModType::level, 1, 1, d);
            REQUIRE((lp.endProgram() && ctx.endInit()));
            uint32_t n = s.numWatches(posLit(c));
            ctx.master()->setHeuristic(dom = new DomainHeuristic);
            dom->startInit(s);
            dom->endInit(s);
            REQUIRE(s.numWatches(posLit(c)) > n);
            REQUIRE(lp.updateProgram());
            lpAdd(lp, "{e}.");
            lp.addDomHeuristic(e, DomModType::level, 1, 1, c);
            REQUIRE((lp.endProgram() && ctx.endInit()));
            s.setHeuristic(new SelectFirst());
            REQUIRE(s.numWatches(posLit(c)) == n);
        }
        SECTION("test increase priority") {
            lpAdd(lp, "{a}.");
            Var_t a = 1, b = 2;
            lp.addDomHeuristic(a, DomModType::false_, 3, 3);
            REQUIRE((lp.endProgram() && ctx.endInit()));
            REQUIRE((s.decideNextBranch() && s.isFalse(lp.getLiteral(a))));
            s.undoUntil(0);
            REQUIRE(lp.updateProgram());
            lpAdd(lp, "{b}.\n");
            lp.addDomHeuristic(a, DomModType::false_, 1, 1);
            lp.addDomHeuristic(b, DomModType::false_, 2, 2);
            REQUIRE((lp.endProgram() && ctx.endInit()));
            REQUIRE((s.decideNextBranch() && s.isFalse(lp.getLiteral(a))));
        }
        SECTION("test increase dynamic priority") {
            Var_t a = 1, b = 2;
            lpAdd(lp, "{a;b}.");
            lp.addDomHeuristic(a, DomModType::true_, 1, 10);
            lp.addDomHeuristic(a, DomModType::false_, 1, 20, b);
            REQUIRE((lp.endProgram() && ctx.endInit()));
            REQUIRE((s.decideNextBranch() && s.isTrue(lp.getLiteral(a))));
            s.undoUntil(0);

            REQUIRE(lp.updateProgram());
            lp.addDomHeuristic(a, DomModType::true_, 1, 30);
            lp.addDomHeuristic(b, DomModType::true_, 2, 2);
            REQUIRE((lp.endProgram() && ctx.endInit()));
            REQUIRE((s.decideNextBranch() && s.isTrue(lp.getLiteral(b))));
            REQUIRE(s.propagate());
            REQUIRE((s.decideNextBranch() && s.isTrue(lp.getLiteral(a))));
        }
        SECTION("test reinit") {
            Var_t b = 2;
            lpAdd(lp, "{a;b}.");
            lp.addDomHeuristic(b, DomModType::level, 1, 1);
            REQUIRE((lp.endProgram() && ctx.endInit()));
            REQUIRE((s.decideNextBranch() && s.value(lp.getLiteral(b).var()) != value_free));
            REQUIRE(lp.updateProgram());
            ctx.master()->setHeuristic(new DomainHeuristic);
            lpAdd(lp, "{c}.");
            REQUIRE((lp.endProgram() && ctx.endInit()));

            REQUIRE((s.decideNextBranch() && s.value(lp.getLiteral(b).var()) != value_free));
        }
        SECTION("test init modifier") {
            Var_t a = 1, b = 2;
            lpAdd(lp, "{a;b;c}."
                      "#heuristic a. [10@10,init]\n"
                      "#heuristic b. [20@20,init]\n");

            REQUIRE((lp.endProgram() && ctx.endInit()));
            REQUIRE(lp.updateProgram());
            lpAdd(lp, "#heuristic a. [30@30,init]\n"
                      "#heuristic b. [10@10,init]\n");
            REQUIRE((lp.endProgram() && ctx.endInit()));
            REQUIRE(dom->score(lp.getLiteral(a).var()).value == 40.0);
            REQUIRE(dom->score(lp.getLiteral(b).var()).value == 20.0);

            REQUIRE(lp.updateProgram());
            ctx.master()->setHeuristic(dom = new DomainHeuristic);
            REQUIRE((lp.endProgram() && ctx.endInit()));
            REQUIRE(dom->score(lp.getLiteral(a).var()).value == 30.0);
            REQUIRE(dom->score(lp.getLiteral(b).var()).value == 20.0);
        }
    }
    SECTION("test min bug") {
        Var_t a = 1, b = 2;
        lpAdd(lp.start(ctx), "a :- not b. b :- not a.");
        lp.addDomHeuristic(a, DomModType::false_, 1, 1);
        lp.addDomHeuristic(b, DomModType::false_, 1, 1);
        REQUIRE((lp.endProgram() && ctx.endInit()));
        REQUIRE((s.pref(lp.getLiteral(a, MapLit::refined).var()).get(ValueSet::user_value) == value_false));
        REQUIRE((s.pref(lp.getLiteral(b, MapLit::refined).var()).get(ValueSet::user_value) == value_false));
    }
    SECTION("test default modification") {
        auto v1 = ctx.addVar(VarType::atom);
        auto v2 = ctx.addVar(VarType::body);
        ctx.startAddConstraints();
        dom->setDefaultMod(HeuParams::mod_level, 0);
        ctx.endInit();
        REQUIRE(dom->score(v1).level == 1);
        REQUIRE(dom->score(v2).level == 0);
        ctx.unfreeze();
        auto v3 = ctx.addVar(VarType::atom);
        ctx.output.add("v1", posLit(v1));
        ctx.output.add("v3", posLit(v3));
        ctx.startAddConstraints();
        dom->setDefaultMod(HeuParams::mod_level, HeuParams::pref_show);
        ctx.endInit();
        REQUIRE(dom->score(v1).level == dom->score(v3).level);
        REQUIRE(dom->score(v2).level == 0);
    }
}
TEST_CASE("Domain Heuristic with eq-preprocessing", "[heuristic][asp]") {
    SharedContext ctx;
    LogicProgram  lp;
    ctx.master()->setHeuristic(new DomainHeuristic);
    Solver& s = *ctx.master();
    Var_t   a = 1, b = 2, c = 3;
    SECTION("test map to one var") {
        lpAdd(lp.start(ctx), "a :- not b. b :- not a.");
        lp.addDomHeuristic(a, DomModType::true_, 2, 2);
        lp.addDomHeuristic(b, DomModType::true_, 1, 1);
        REQUIRE((lp.endProgram() && ctx.endInit()));
        REQUIRE((s.decideNextBranch() && s.isTrue(lp.getLiteral(a))));
    }
    SECTION("test level") {
        lpAdd(lp.start(ctx), "{a;c}.\n"
                             "b :- a.\n");
        lp.addDomHeuristic(a, DomModType::level, 1, 3);
        lp.addDomHeuristic(b, DomModType::level, 3, 2);
        lp.addDomHeuristic(c, DomModType::level, 2, 1);
        REQUIRE((lp.endProgram() && ctx.endInit()));
        REQUIRE(s.decideNextBranch());
        REQUIRE(s.value(getDomLiteral(lp, b).var()) != value_free);
    }
    SECTION("test sign") {
        lpAdd(lp.start(ctx), "{a}. b :- a.");
        lp.addDomHeuristic(a, DomModType::sign, 1, 1);
        lp.addDomHeuristic(b, DomModType::sign, -1, 1);
        REQUIRE((lp.endProgram() && ctx.endInit()));

        REQUIRE((s.pref(getDomLiteral(lp, a).var()).has(ValueSet::user_value)));
        REQUIRE((s.pref(getDomLiteral(lp, b).var()).has(ValueSet::user_value)));
    }
    SECTION("test complementary atom level") {
        lpAdd(lp.start(ctx), "{a;c}. b :- not a.");
        lp.addDomHeuristic(a, DomModType::level, 1, 3);
        lp.addDomHeuristic(b, DomModType::level, 3, 2);
        lp.addDomHeuristic(c, DomModType::level, 2, 1);
        REQUIRE((lp.endProgram() && ctx.endInit()));
        REQUIRE(s.decideNextBranch());
        REQUIRE(s.value(getDomLiteral(lp, b).var()) != value_free);
    }
    SECTION("test complementary atom sign") {
        lpAdd(lp.start(ctx), "{a}. b :- not a.");
        lp.addDomHeuristic(a, DomModType::sign, 1, 1);
        lp.addDomHeuristic(b, DomModType::sign, 1, 1);
        REQUIRE((lp.endProgram() && ctx.endInit()));
        REQUIRE((s.pref(getDomLiteral(lp, a).var()).has(ValueSet::user_value)));
        REQUIRE((s.pref(getDomLiteral(lp, b).var()).has(ValueSet::user_value)));
    }
    SECTION("test complementary atom true/false") {
        lpAdd(lp.start(ctx), "a :- not b. b :- not a. {c}.");
        lp.addDomHeuristic(a, DomModType::true_, 10, 10);
        lp.addDomHeuristic(b, DomModType::true_, 20, 20);
        REQUIRE((lp.endProgram() && ctx.endInit()));
        REQUIRE(s.decideNextBranch());
        REQUIRE(s.isTrue(getDomLiteral(lp, b)));
    }

    SECTION("test same var different level") {
        lp.start(ctx);
        lp.updateProgram();
        lpAdd(lp, "{a;c}. b :- a.");
        lp.addDomHeuristic(a, DomModType::level, 2, 1);
        lp.addDomHeuristic(c, DomModType::level, 2, 1);
        lp.addDomHeuristic(c, DomModType::init, 10, 1);
        SECTION("once") {
            lp.addDomHeuristic(b, DomModType::init, 20, 1);
            REQUIRE((lp.endProgram() && ctx.endInit()));
            REQUIRE(s.value(lp.getLiteral(c).var()) == value_free);
            REQUIRE(s.decideNextBranch());
            REQUIRE(s.value(lp.getLiteral(c).var()) != value_free);
        }
        SECTION("incremental") {
            REQUIRE((lp.endProgram() && ctx.endInit()));
            REQUIRE(s.decideNextBranch());
            REQUIRE(s.value(lp.getLiteral(c).var()) != value_free);
            s.undoUntil(0);
            REQUIRE(lp.updateProgram());
            lp.addDomHeuristic(b, DomModType::init, 20, 1);
            REQUIRE((lp.endProgram() && ctx.endInit()));
            REQUIRE(s.decideNextBranch());
            REQUIRE(s.value(lp.getLiteral(c).var()) != value_free);
        }
    }
    SECTION("test same var diff level cond") {
        Var_t d = 4;
        lp.start(ctx);
        lpAdd(lp, "{a;b;c;d}. b :- a.");
        lp.addDomHeuristic(b, DomModType::init, 40, 1);
        lp.addDomHeuristic(d, DomModType::init, 50, 1);
        lp.addDomHeuristic(d, DomModType::sign, 1, 1);
        lp.addDomHeuristic(a, DomModType::true_, 2, 1, d);
        lp.addDomHeuristic(c, DomModType::true_, 2, 1, d);
        lp.addDomHeuristic(c, DomModType::init, 30, 1);

        REQUIRE((lp.endProgram() && ctx.endInit()));
        REQUIRE(s.decideNextBranch());
        REQUIRE(s.isTrue(lp.getLiteral(d)));
        s.propagate();
        REQUIRE(s.decideNextBranch());
        REQUIRE(s.value(lp.getLiteral(c).var()) != value_free);
    }
    SECTION("test same var diff prio") {
        lp.start(ctx).updateProgram();
        lpAdd(lp, "{a}. b :- a.");
        lp.addDomHeuristic(a, DomModType::false_, 2, 3);
        lp.addDomHeuristic(b, DomModType::false_, 1, 1);
        REQUIRE((lp.endProgram() && ctx.endInit()));
        REQUIRE((s.decideNextBranch() && s.isFalse(getDomLiteral(lp, a))));
        s.undoUntil(0);
        REQUIRE(lp.updateProgram());
        lp.addDomHeuristic(b, DomModType::true_, 3, 2);
        REQUIRE((lp.endProgram() && ctx.endInit()));
        REQUIRE((s.decideNextBranch() && s.isTrue(getDomLiteral(lp, b))));
    }
}
}
