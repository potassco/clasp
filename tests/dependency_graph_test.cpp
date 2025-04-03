//
// Copyright (c) 2009-present Benjamin Kaufmann
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
#include <clasp/dependency_graph.h>

#include <clasp/solver.h>

#include <catch2/catch_test_macros.hpp>

namespace Clasp::Test {
using namespace Clasp::Asp;

TEST_CASE("Dependency graph", "[asp][propagator]") {
    SharedContext ctx;
    LogicProgram  lp;
    SECTION("test Tight Program") {
        lp.start(ctx);
        lpAdd(lp, "x1 :- not x2.");
        lp.endProgram();
        REQUIRE(lp.stats.sccs == 0);
        REQUIRE(ctx.sccGraph.get() == 0);
    }

    SECTION("test Init Order") {
        lp.start(ctx, LogicProgram::AspOptions().noEq());
        lpAdd(lp, "x4 :- x3.\n"
                  "x3 :- x4.\n"
                  "x2 :- x3.\n"
                  "x2 :- x1.\n"
                  "x1 :- x2.\n"
                  "x3 :- not a.\n");
        lp.endProgram();

        REQUIRE(lp.stats.sccs == 2);

        auto* graph = ctx.sccGraph.get();

        REQUIRE(uint32_t(10) == graph->nodes());

        const auto& b = graph->getAtom(lp.getAtom(2)->id());
        const auto& x = graph->getAtom(lp.getAtom(3)->id());

        REQUIRE(graph->getBody(b.body(0)).scc != b.scc);
        REQUIRE(graph->getBody(b.body(1)).scc == b.scc);
        REQUIRE(b.bodies().size() == 2);

        REQUIRE(graph->getBody(x.body(0)).scc != x.scc);
        REQUIRE(graph->getBody(x.body(1)).scc == x.scc);
        REQUIRE(x.bodies().size() == 2);

        const auto& xBody = graph->getBody(b.body(0));
        REQUIRE(xBody.heads().size() == 2);
        REQUIRE(graph->getAtom(xBody.heads()[0]).scc == xBody.scc);
        REQUIRE(graph->getAtom(xBody.heads()[1]).scc != xBody.scc);
    }

    SECTION("test Program With Loops") {
        lpAdd(lp.start(ctx), "a :- not f.\n"
                             "b :- a.\n"
                             "a :- b, d.\n"
                             "b :- not e.\n"
                             "c :- f.\n"
                             "d :- c.\n"
                             "c :- d.\n"
                             "d :- not e.\n"
                             "g :- not e.\n"
                             "f :- g.\n"
                             "e :- not g.\n");
        lp.endProgram();

        auto* graph = ctx.sccGraph.get();
        REQUIRE(lp.getLiteral(6) == lp.getLiteral(7));
        REQUIRE(~lp.getLiteral(6) == lp.getLiteral(5));

        REQUIRE(graph->getAtom(lp.getAtom(1)->id()).scc == 0);
        REQUIRE(graph->getAtom(lp.getAtom(2)->id()).scc == 0);
        REQUIRE(graph->getAtom(lp.getAtom(3)->id()).scc == 1);
        REQUIRE(graph->getAtom(lp.getAtom(4)->id()).scc == 1);
        constexpr uint32_t noId = PrgNode::no_node;
        REQUIRE(lp.getAtom(5)->id() == noId);
        REQUIRE((lp.getAtom(6)->eq() || lp.getAtom(6)->id() == noId));
        REQUIRE(lp.getAtom(7)->id() == noId);

        REQUIRE(uint32_t(11) == graph->nodes());
        // check that lists are partitioned by component number
        const auto& a = graph->getAtom(lp.getAtom(1)->id());
        REQUIRE(graph->getBody(a.body(0)).scc == +PrgNode::no_scc);
        REQUIRE(graph->getBody(a.body(1)).scc == a.scc);
        REQUIRE(a.bodies().size() == 2);
        REQUIRE(ctx.varInfo(a.lit.var()).frozen());

        const auto& bd = graph->getBody(a.body(1));
        REQUIRE(ctx.varInfo(bd.lit.var()).frozen());
        REQUIRE(bd.countPreds() == 1);
        LitVec predLits;
        for (const auto& x : bd.predecessors()) { predLits.push_back(x.lit(*graph)); }
        REQUIRE(predLits == LitVec{1, lp.getLiteral(2)});
        REQUIRE(bd.heads().size() == 1);
        REQUIRE(bd.heads()[0] == graph->id(a));
    }

    SECTION("test With Simple Cardinality Constraint") {
        lpAdd(lp.start(ctx), "{x2}.\n"
                             "x1 :- 1 {x1, x2}.\n");
        REQUIRE(lp.endProgram());
        auto* graph = ctx.sccGraph.get();
        REQUIRE(uint32_t(3) == graph->nodes());
        const auto& a    = graph->getAtom(lp.getAtom(1)->id());
        const auto& body = graph->getBody(a.body(0));

        REQUIRE(body.countPreds() == 2);
        REQUIRE(body.extended());
        REQUIRE(body.extBound() == 1);
        std::vector<uint32_t> predIds;
        for (const auto& x : body.predecessors()) { predIds.push_back(x.id()); }
        REQUIRE(predIds == std::vector<uint32_t>{graph->id(a), lp.getLiteral(2).rep()});
        REQUIRE(body.predWeight(0, false) == 1);
        REQUIRE(body.predWeight(1, true) == 1);

        REQUIRE(a.inExtended());
        unsigned nSuccs = 0;
        for (const auto& x : a.successors()) {
            REQUIRE(x.id() == a.body(nSuccs));
            REQUIRE_FALSE(x.normal());
            REQUIRE(x.position() == 0);
            ++nSuccs;
        }
        REQUIRE(nSuccs == 1);
    }

    SECTION("test With Simple Weight Constraint") {
        lpAdd(lp.start(ctx), "{x2;x3}.\n"
                             "x1 :- 2 {x2 = 2, x3 = 1, x1 = 2}.\n");
        REQUIRE(lp.endProgram());
        auto* graph = ctx.sccGraph.get();
        REQUIRE(uint32_t(3) == graph->nodes());

        const auto& a    = graph->getAtom(lp.getAtom(1)->id());
        const auto& body = graph->getBody(a.body(0));

        REQUIRE(body.countPreds() == 3);
        REQUIRE(body.extended());
        REQUIRE(body.extBound() == 2);
        std::vector<uint32_t> preds;
        for (const auto& x : body.predecessors()) {
            preds.push_back(x.id());
            preds.push_back(static_cast<uint32_t>(x.weight()));
        }
        REQUIRE(preds ==
                std::vector<uint32_t>{graph->id(a), 2u, lp.getLiteral(2).rep(), 2u, lp.getLiteral(3).rep(), 1u});

        REQUIRE(body.predWeight(0, false) == 2);
        REQUIRE(body.predWeight(1, true) == 2);
        REQUIRE(body.predWeight(2, true) == 1);

        REQUIRE(a.inExtended());
        unsigned nSuccs = 0;
        for (const auto& x : a.successors()) {
            REQUIRE(x.id() == a.body(nSuccs));
            REQUIRE_FALSE(x.normal());
            REQUIRE(x.position() == 0);
            REQUIRE(graph->getBody(x.id()).extended());
            REQUIRE(graph->getBody(x.id()).findPred(graph->id(a)) == x.position());
            ++nSuccs;
        }
        REQUIRE(nSuccs == 1);
    }

    SECTION("test Ignore Atoms From Prev Steps") {
        lp.start(ctx, LogicProgram::AspOptions().noEq());
        lp.updateProgram();
        lpAdd(lp, "{x1;x2;x3}.\n"
                  "x4 :- x5.\n"
                  "x5 :- x4.\n"
                  "x4 :- x1.\n");
        REQUIRE(lp.endProgram());
        auto*    graph = ctx.sccGraph.get();
        uint32_t nA    = lp.getAtom(4)->id();
        {
            const auto& a = graph->getAtom(nA);
            REQUIRE(a.bodies().size() == 2);
        }

        lp.update();
        lpAdd(lp, "x6|x7.\n"
                  "x7 :- x6.\n"
                  "x6 :- x7.\n");
        REQUIRE(lp.endProgram());
        {
            const auto& a = graph->getAtom(nA);
            REQUIRE(a.bodies().size() == 2);
        }
        const auto& c = graph->getAtom(lp.getAtom(6)->id());
        REQUIRE(c.bodies().size() == 2);
    }
}

TEST_CASE("Acyclicity checking", "[asp][propagator]") {
    SharedContext ctx;
    ExtDepGraph   graph;
    SECTION("test Self Loop") {
        Literal x1 = posLit(ctx.addVar(VarType::atom));
        graph.addEdge(x1, 0, 0);
        graph.finalize(ctx);
        ctx.startAddConstraints();
        ctx.master()->addPost(new AcyclicityCheck(&graph));
        ctx.endInit();
        REQUIRE(ctx.master()->isFalse(x1));
    }
    SECTION("test Simple Loop") {
        Literal x1 = posLit(ctx.addVar(VarType::atom));
        Literal x2 = posLit(ctx.addVar(VarType::atom));
        graph.addEdge(x1, 0, 1);
        graph.addEdge(x2, 1, 0);
        graph.finalize(ctx);
        ctx.startAddConstraints();
        AcyclicityCheck* check;
        ctx.master()->addPost(check = new AcyclicityCheck(&graph));
        ctx.endInit();
        REQUIRE(ctx.master()->topValue(x1.var()) == value_free);
        REQUIRE(ctx.master()->topValue(x2.var()) == value_free);
        REQUIRE(ctx.master()->hasWatch(x1, check));
        REQUIRE(ctx.master()->hasWatch(x2, check));
        REQUIRE((ctx.master()->assume(x1) && ctx.master()->propagate()));

        REQUIRE(ctx.master()->isFalse(x2));
        ctx.master()->removePost(check);
        check->destroy(ctx.master(), true);
        REQUIRE_FALSE(ctx.master()->hasWatch(x1, check));
        REQUIRE_FALSE(ctx.master()->hasWatch(x2, check));
    }
    SECTION("test No Outgoing Edge") {
        Literal x1 = posLit(ctx.addVar(VarType::atom));
        Literal x2 = posLit(ctx.addVar(VarType::atom));
        graph.addEdge(x1, 0, 1);
        graph.finalize(ctx);
        ctx.startAddConstraints();
        AcyclicityCheck* check;
        ctx.master()->addPost(check = new AcyclicityCheck(&graph));
        ctx.endInit();
        REQUIRE((ctx.master()->assume(x1) && ctx.master()->propagate()));

        REQUIRE_FALSE(ctx.master()->isFalse(x2));
        ctx.master()->removePost(check);
        check->destroy(ctx.master(), true);
        REQUIRE_FALSE(ctx.master()->hasWatch(x1, check));
    }
    SECTION("test Logic Program") {
        Asp::LogicProgram lp;
        lpAdd(lp.start(ctx), "{x1;x2}.\n"
                             "x3 :- x1.\n"
                             "x4 :- x2.\n"
                             "#edge (0,1) : x3.\n"
                             "#edge (1,0) : x4.\n"
                             "% ignore because x5 is false\n"
                             "#edge (1,0) : x5.\n");
        REQUIRE(lp.endProgram());
        REQUIRE((ctx.extGraph.get() && ctx.extGraph->nodes() == 2));
        ctx.master()->addPost(new AcyclicityCheck(nullptr));
        REQUIRE(ctx.endInit());

        ctx.master()->assume(lp.getLiteral(1));
        ctx.master()->propagate();
        REQUIRE(ctx.master()->isFalse(lp.getLiteral(2)));
    }

    SECTION("test Incremental Only New") {
        Asp::LogicProgram lp;
        lp.start(ctx);
        lp.updateProgram();
        lpAdd(lp, "{x1;x2}.\n"
                  "#edge (0,1) : x1.\n"
                  "#edge (1,0) : x2.\n");

        REQUIRE(lp.endProgram());

        AcyclicityCheck* check;
        ctx.master()->addPost(check = new AcyclicityCheck(nullptr));
        REQUIRE(ctx.endInit());

        lp.updateProgram();
        lpAdd(lp, "{x3;x4}.\n"
                  "#edge (2,3) : x3.\n"
                  "#edge (3,2) : x4.\n");

        REQUIRE(lp.endProgram());
        REQUIRE((ctx.extGraph.get() && ctx.extGraph->nodes() == 4));
        REQUIRE(ctx.endInit());
        Literal lit = lp.getLiteral(3);
        REQUIRE(ctx.master()->hasWatch(lit, check));
    }

    SECTION("test Incremental Extend") {
        Asp::LogicProgram lp;
        lp.start(ctx);
        lp.updateProgram();
        lpAdd(lp, "{x1;x2}.\n"
                  "#edge (1,2) : x1.\n"
                  "#edge (2,1) : x2.\n");
        REQUIRE(lp.endProgram());

        ctx.master()->addPost(new AcyclicityCheck(nullptr));
        REQUIRE(ctx.endInit());

        lp.updateProgram();
        lpAdd(lp, "{x3;x4;x5;x6;x7}.\n"
                  "#edge (2,3) : x3.\n"
                  "#edge (3,4) : x4.\n"
                  "#edge (4,1) : x5.\n"
                  "#edge (1,5) : x6.\n"
                  "#edge (5,3) : x7.\n");

        REQUIRE(lp.endProgram());
        REQUIRE((ctx.extGraph.get() && ctx.extGraph->edges() == 7));
        REQUIRE(ctx.endInit());
        Var_t   x1 = 1, x2 = 2, x3 = 3, x4 = 4, x5 = 5, x6 = 6, x7 = 7;
        Solver& s = *ctx.master();
        REQUIRE((s.assume(lp.getLiteral(x1)) && s.propagate()));
        REQUIRE(s.isFalse(lp.getLiteral(x2)));
        REQUIRE((s.assume(lp.getLiteral(x3)) && s.propagate()));
        REQUIRE((s.assume(lp.getLiteral(x4)) && s.propagate()));
        REQUIRE(s.isFalse(lp.getLiteral(x5)));
        s.undoUntil(0);
        REQUIRE((s.assume(lp.getLiteral(x4)) && s.propagate()));
        REQUIRE((s.assume(lp.getLiteral(x7)) && s.propagate()));
        REQUIRE((s.assume(lp.getLiteral(x5)) && s.propagate()));
        REQUIRE(s.isFalse(lp.getLiteral(x6)));
    }
}
} // namespace Clasp::Test
