// 
// Copyright (c) 2009, Benjamin Kaufmann
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
#include <clasp/dependency_graph.h>
#include <clasp/solver.h>
namespace Clasp { namespace Test {
using namespace Clasp::Asp;
class DependencyGraphTest : public CppUnit::TestFixture {
	CPPUNIT_TEST_SUITE(DependencyGraphTest);
	CPPUNIT_TEST(testTightProgram);
	CPPUNIT_TEST(testInitOrder);
	CPPUNIT_TEST(testProgramWithLoops);
	CPPUNIT_TEST(testWithSimpleCardinalityConstraint);
	CPPUNIT_TEST(testWithSimpleWeightConstraint);
	CPPUNIT_TEST(testIgnoreAtomsFromPrevSteps);
	CPPUNIT_TEST_SUITE_END(); 
public:
	DependencyGraphTest() {
	}
	void setUp() {
		ctx = new SharedContext();
	}
	void tearDown() {
		delete ctx;
	}
	void testTightProgram() { 
		lp.start(*ctx);
		lpAdd(lp, "x1 :- not x2.");
		lp.endProgram();
		CPPUNIT_ASSERT_EQUAL(true, lp.stats.sccs == 0);
		CPPUNIT_ASSERT(ctx->sccGraph.get() == 0);
	}
	
	void testInitOrder() {
		lp.start(*ctx, LogicProgram::AspOptions().noEq());
		lpAdd(lp, 
			"x4 :- x3.\n"
			"x3 :- x4.\n"
			"x2 :- x3.\n"
			"x2 :- x1.\n"
			"x1 :- x2.\n"
			"x3 :- not a.\n");
		lp.endProgram();
		
		CPPUNIT_ASSERT_EQUAL(true, lp.stats.sccs == 2);
		
		DG* graph = ctx->sccGraph.get();

		CPPUNIT_ASSERT_EQUAL(uint32(10), graph->nodes());
		
		const DG::AtomNode& b = graph->getAtom(lp.getAtom(2)->id());
		const DG::AtomNode& x = graph->getAtom(lp.getAtom(3)->id());
		
		CPPUNIT_ASSERT(graph->getBody(b.body(0)).scc != b.scc);
		CPPUNIT_ASSERT(graph->getBody(b.body(1)).scc == b.scc);
		CPPUNIT_ASSERT(b.bodies_begin()+2 == b.bodies_end());

		CPPUNIT_ASSERT(graph->getBody(x.body(0)).scc != x.scc);
		CPPUNIT_ASSERT(graph->getBody(x.body(1)).scc == x.scc);
		CPPUNIT_ASSERT(x.bodies_begin()+2 == x.bodies_end());

		const DG::BodyNode& xBody = graph->getBody(b.body(0));
		CPPUNIT_ASSERT(graph->getAtom(xBody.heads_begin()[0]).scc == xBody.scc);
		CPPUNIT_ASSERT(graph->getAtom(xBody.heads_begin()[1]).scc != xBody.scc);
		CPPUNIT_ASSERT(xBody.heads_begin()+2 == xBody.heads_end());
	}

	void testProgramWithLoops() {
		lpAdd(lp.start(*ctx),
			"a :- not f.\n"
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
		
		DG* graph = ctx->sccGraph.get();
		CPPUNIT_ASSERT_EQUAL(lp.getLiteral(6), lp.getLiteral(7));
		CPPUNIT_ASSERT_EQUAL(~lp.getLiteral(6), lp.getLiteral(5));
		
		CPPUNIT_ASSERT( graph->getAtom(lp.getAtom(1)->id()).scc == 0 );
		CPPUNIT_ASSERT( graph->getAtom(lp.getAtom(2)->id()).scc == 0 );
		CPPUNIT_ASSERT( graph->getAtom(lp.getAtom(3)->id()).scc == 1 );
		CPPUNIT_ASSERT( graph->getAtom(lp.getAtom(4)->id()).scc == 1 );
		CPPUNIT_ASSERT( lp.getAtom(5)->id() == PrgNode::noNode );
		CPPUNIT_ASSERT( lp.getAtom(6)->eq() || lp.getAtom(6)->id() == PrgNode::noNode );
		CPPUNIT_ASSERT( lp.getAtom(7)->id() == PrgNode::noNode );
		
		CPPUNIT_ASSERT(uint32(11) == graph->nodes());
		// check that lists are partitioned by component number
		const DG::AtomNode& a =  graph->getAtom(lp.getAtom(1)->id());
		CPPUNIT_ASSERT(graph->getBody(a.body(0)).scc == PrgNode::noScc);
		CPPUNIT_ASSERT(graph->getBody(a.body(1)).scc == a.scc);
		CPPUNIT_ASSERT(a.bodies_begin()+2 == a.bodies_end());
		CPPUNIT_ASSERT_EQUAL(true, ctx->varInfo(a.lit.var()).frozen());

		const DG::BodyNode& bd = graph->getBody(a.body(1));
		CPPUNIT_ASSERT_EQUAL(true, ctx->varInfo(bd.lit.var()).frozen());
		CPPUNIT_ASSERT(graph->getAtom(bd.preds()[0]).lit == lp.getLiteral(2));
		CPPUNIT_ASSERT(bd.preds()[1]== idMax);
		CPPUNIT_ASSERT(bd.heads_begin()[0] == graph->id(a));
		CPPUNIT_ASSERT(bd.heads_begin()+1 == bd.heads_end());
	}

	void testWithSimpleCardinalityConstraint() {
		lpAdd(lp.start(*ctx),
			"{x2}.\n"
			"x1 :- 1 {x1, x2}.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		DG* graph = ctx->sccGraph.get();
		CPPUNIT_ASSERT( uint32(3) == graph->nodes() );
		const DG::AtomNode& a    = graph->getAtom(lp.getAtom(1)->id());
		const DG::BodyNode& body = graph->getBody(a.body(0));

		CPPUNIT_ASSERT(body.num_preds() == 2);
		CPPUNIT_ASSERT(body.extended());
		CPPUNIT_ASSERT(body.ext_bound() == 1);
		CPPUNIT_ASSERT(body.pred_inc() == 1);
		CPPUNIT_ASSERT(body.preds()[0] == graph->id(a));
		CPPUNIT_ASSERT(body.preds()[1] == idMax);
		CPPUNIT_ASSERT(body.preds()[2] == lp.getLiteral(2).rep());
		CPPUNIT_ASSERT(body.preds()[3] == idMax);
		CPPUNIT_ASSERT(body.pred_weight(0,false) == 1);
		CPPUNIT_ASSERT(body.pred_weight(1,true) == 1);

		CPPUNIT_ASSERT(a.inExtended());
		CPPUNIT_ASSERT(a.succs()[0] == idMax);
		CPPUNIT_ASSERT(a.succs()[1] == a.body(0));
		CPPUNIT_ASSERT(a.succs()[2] == 0);
		CPPUNIT_ASSERT(a.succs()[3] == idMax);
	}

	void testWithSimpleWeightConstraint() {
		lpAdd(lp.start(*ctx), 
			"{x2;x3}.\n"
			"x1 :- 2 {x1 = 2, x2 = 2, x3 = 1}.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		DG* graph = ctx->sccGraph.get();
		CPPUNIT_ASSERT( uint32(3) == graph->nodes() );
		
		const DG::AtomNode& a    = graph->getAtom(lp.getAtom(1)->id());
		const DG::BodyNode& body = graph->getBody(a.body(0));

		CPPUNIT_ASSERT(body.num_preds() == 3);
		CPPUNIT_ASSERT(body.extended());
		CPPUNIT_ASSERT(body.ext_bound() == 2);
		CPPUNIT_ASSERT(body.pred_inc() == 2);
		CPPUNIT_ASSERT(body.preds()[0] == graph->id(a));
		CPPUNIT_ASSERT(body.preds()[2] == idMax);
		CPPUNIT_ASSERT(body.preds()[3] == lp.getLiteral(2).rep());
		CPPUNIT_ASSERT(body.preds()[5] == lp.getLiteral(3).rep());
		CPPUNIT_ASSERT(body.preds()[7] == idMax);
		CPPUNIT_ASSERT(body.pred_weight(0, false) == 2);
		CPPUNIT_ASSERT(body.pred_weight(1, true) == 2);
		CPPUNIT_ASSERT(body.pred_weight(2, true) == 1);
		
		CPPUNIT_ASSERT(a.inExtended());
		CPPUNIT_ASSERT(a.succs()[0] == idMax);
		CPPUNIT_ASSERT(a.succs()[1] == a.body(0));
		CPPUNIT_ASSERT(a.succs()[2] == 0);
		CPPUNIT_ASSERT(a.succs()[3] == idMax);
	}

	void testIgnoreAtomsFromPrevSteps() {
		lp.start(*ctx, LogicProgram::AspOptions().noEq());
		lp.updateProgram();
		lpAdd(lp,
			"{x1;x2;x3}.\n"
			"x4 :- x5.\n"
			"x5 :- x4.\n"
			"x4 :- x1.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());		
		DG* graph  = ctx->sccGraph.get();
		uint32 nA  = lp.getAtom(4)->id();
		{
			const DG::AtomNode& a = graph->getAtom(nA);
			CPPUNIT_ASSERT(std::distance(a.bodies_begin(), a.bodies_end()) == 2);
		}

		lp.update();
		lpAdd(lp, 
			"x6|x7.\n"
			"x7 :- x6.\n"
			"x6 :- x7.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		{
			const DG::AtomNode& a = graph->getAtom(nA);
			CPPUNIT_ASSERT(std::distance(a.bodies_begin(), a.bodies_end()) == 2);
		}
		const DG::AtomNode& c = graph->getAtom(lp.getAtom(6)->id());
		CPPUNIT_ASSERT(std::distance(c.bodies_begin(), c.bodies_end()) == 2);
	}
private:
	typedef Asp::PrgDepGraph DG;
	SharedContext* ctx;
	LogicProgram   lp;
};
CPPUNIT_TEST_SUITE_REGISTRATION(DependencyGraphTest);

class AcycGraphTest : public CppUnit::TestFixture {
	CPPUNIT_TEST_SUITE(AcycGraphTest);
	CPPUNIT_TEST(testSelfLoop);
	CPPUNIT_TEST(testSimpleLoop);
	CPPUNIT_TEST(testNoOutgoingEdge);
	CPPUNIT_TEST(testLogicProgram);
	CPPUNIT_TEST(testIncrementalOnlyNew);
	CPPUNIT_TEST(testIncrementalExtend);
	CPPUNIT_TEST_SUITE_END(); 
public:
	AcycGraphTest() {}
	void testSelfLoop() {
		SharedContext ctx;
		Literal x1 = posLit(ctx.addVar(Var_t::Atom));
		ExtDepGraph graph;
		graph.addEdge(x1, 0, 0);
		graph.finalize(ctx);
		ctx.startAddConstraints();
		AcyclicityCheck* check;
		ctx.master()->addPost(check = new AcyclicityCheck(&graph));
		ctx.endInit();
		CPPUNIT_ASSERT(ctx.master()->isFalse(x1));
	}
	void testSimpleLoop() {
		SharedContext ctx;
		Literal x1 = posLit(ctx.addVar(Var_t::Atom));
		Literal x2 = posLit(ctx.addVar(Var_t::Atom));
		ExtDepGraph graph;
		graph.addEdge(x1, 0, 1);
		graph.addEdge(x2, 1, 0);
		graph.finalize(ctx);
		ctx.startAddConstraints();
		AcyclicityCheck* check;
		ctx.master()->addPost(check = new AcyclicityCheck(&graph));
		ctx.endInit();
		CPPUNIT_ASSERT(ctx.master()->topValue(x1.var()) == value_free);
		CPPUNIT_ASSERT(ctx.master()->topValue(x2.var()) == value_free);
		CPPUNIT_ASSERT(ctx.master()->hasWatch(x1, check));
		CPPUNIT_ASSERT(ctx.master()->hasWatch(x2, check));
		CPPUNIT_ASSERT(ctx.master()->assume(x1) && ctx.master()->propagate());
		
		CPPUNIT_ASSERT(ctx.master()->isFalse(x2));
		ctx.master()->removePost(check);
		check->destroy(ctx.master(), true);
		CPPUNIT_ASSERT(!ctx.master()->hasWatch(x1, check));
		CPPUNIT_ASSERT(!ctx.master()->hasWatch(x2, check));
	}
	void testNoOutgoingEdge() {
		SharedContext ctx;
		Literal x1 = posLit(ctx.addVar(Var_t::Atom));
		Literal x2 = posLit(ctx.addVar(Var_t::Atom));
		ExtDepGraph graph;
		graph.addEdge(x1, 0, 1);
		graph.finalize(ctx);
		ctx.startAddConstraints();
		AcyclicityCheck* check;
		ctx.master()->addPost(check = new AcyclicityCheck(&graph));
		ctx.endInit();
		CPPUNIT_ASSERT(ctx.master()->assume(x1) && ctx.master()->propagate());
		
		CPPUNIT_ASSERT(!ctx.master()->isFalse(x2));
		ctx.master()->removePost(check);
		check->destroy(ctx.master(), true);
		CPPUNIT_ASSERT(!ctx.master()->hasWatch(x1, check));
	}
	void testLogicProgram() {
		SharedContext     ctx;
		Asp::LogicProgram lp;
		lpAdd(lp.start(ctx), 
			"{x1;x2}.\n"
			"x3 :- x1.\n"
			"x4 :- x2.\n"
			"#edge (0,1) : x3.\n"
			"#edge (1,0) : x4.\n"
			"% ignore because x5 is false\n"
			"#edge (1,0) : x5.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(ctx.extGraph.get() && ctx.extGraph->nodes() == 2);
		AcyclicityCheck* check;
		ctx.master()->addPost(check = new AcyclicityCheck(0));
		CPPUNIT_ASSERT(ctx.endInit());

		ctx.master()->assume(lp.getLiteral(1));
		ctx.master()->propagate();
		CPPUNIT_ASSERT(ctx.master()->isFalse(lp.getLiteral(2)));
	}
	
	void testIncrementalOnlyNew() {
		SharedContext     ctx;
		Asp::LogicProgram lp;
		lp.start(ctx);
		lp.updateProgram();
		lpAdd(lp,
			"{x1;x2}.\n"
			"#edge (0,1) : x1.\n"
			"#edge (1,0) : x2.\n");

		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		
		AcyclicityCheck* check;
		ctx.master()->addPost(check = new AcyclicityCheck(0));
		CPPUNIT_ASSERT(ctx.endInit());

		lp.updateProgram();
		lpAdd(lp, 
			"{x3;x4}.\n"
			"#edge (2,3) : x3.\n"
			"#edge (3,2) : x4.\n");
		
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(ctx.extGraph.get() && ctx.extGraph->nodes() == 4);
		CPPUNIT_ASSERT(ctx.endInit());
		Literal lit = lp.getLiteral(3);
		CPPUNIT_ASSERT(ctx.master()->hasWatch(lit, check));
	}

	void testIncrementalExtend() {
		SharedContext     ctx;
		Asp::LogicProgram lp;
		lp.start(ctx);
		lp.updateProgram();
		lpAdd(lp, 
			"{x1;x2}.\n"
			"#edge (1,2) : x1.\n"
			"#edge (2,1) : x2.\n");
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		
		AcyclicityCheck* check;
		ctx.master()->addPost(check = new AcyclicityCheck(0));
		CPPUNIT_ASSERT(ctx.endInit());

		lp.updateProgram();
		lpAdd(lp, "{x3;x4;x5;x6;x7}.\n"
			"#edge (2,3) : x3.\n"
			"#edge (3,4) : x4.\n"
			"#edge (4,1) : x5.\n"
			"#edge (1,5) : x6.\n"
			"#edge (5,3) : x7.\n");
		
		CPPUNIT_ASSERT_EQUAL(true, lp.endProgram());
		CPPUNIT_ASSERT(ctx.extGraph.get() && ctx.extGraph->edges() == 7);
		CPPUNIT_ASSERT(ctx.endInit());
		Var x1 =1, x2 = 2, x3 = 3, x4 = 4, x5 = 5, x6 = 6, x7 = 7;
		Solver& s = *ctx.master();
		CPPUNIT_ASSERT(s.assume(lp.getLiteral(x1)) && s.propagate());
		CPPUNIT_ASSERT(s.isFalse(lp.getLiteral(x2)));
		CPPUNIT_ASSERT(s.assume(lp.getLiteral(x3)) && s.propagate());
		CPPUNIT_ASSERT(s.assume(lp.getLiteral(x4)) && s.propagate());
		CPPUNIT_ASSERT(s.isFalse(lp.getLiteral(x5)));
		s.undoUntil(0);
		CPPUNIT_ASSERT(s.assume(lp.getLiteral(x4)) && s.propagate());
		CPPUNIT_ASSERT(s.assume(lp.getLiteral(x7)) && s.propagate());
		CPPUNIT_ASSERT(s.assume(lp.getLiteral(x5)) && s.propagate());
		CPPUNIT_ASSERT(s.isFalse(lp.getLiteral(x6)));
	}
private:
	typedef ExtDepGraph DG;
};
CPPUNIT_TEST_SUITE_REGISTRATION(AcycGraphTest);
} } 
