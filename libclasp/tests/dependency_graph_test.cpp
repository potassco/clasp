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
		ctx   = new SharedContext();
	}
	void tearDown() {
		delete ctx;
	}
	void testTightProgram() { 
		builder.start(*ctx)
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule().addHead(1).addToBody(2, false).endRule()
		.endProgram();
		CPPUNIT_ASSERT_EQUAL(true, builder.stats.sccs == 0);
		CPPUNIT_ASSERT(ctx->sccGraph.get() == 0);
	}
	
	void testInitOrder() {
		builder.start(*ctx, LogicProgram::AspOptions().noEq())
			.setAtomName(1,"a").setAtomName(2,"b").setAtomName(3,"x").setAtomName(4,"y")
			.startRule().addHead(4).addToBody(3, true).endRule()  // y :- x.
			.startRule().addHead(3).addToBody(4, true).endRule()  // x :- y.
			.startRule().addHead(2).addToBody(3, true).endRule()  // b :- x.
			.startRule().addHead(2).addToBody(1, true).endRule()  // b :- a.
			.startRule().addHead(1).addToBody(2, true).endRule()  // a :- b.
			.startRule().addHead(3).addToBody(1, false).endRule() // x :- not a.
		.endProgram();
		
		CPPUNIT_ASSERT_EQUAL(true, builder.stats.sccs == 2);
		
		DG* graph = ctx->sccGraph.get();

		CPPUNIT_ASSERT_EQUAL(uint32(10), graph->nodes());
		
		const DG::AtomNode& b = graph->getAtom(builder.getAtom(2)->id());
		const DG::AtomNode& x = graph->getAtom(builder.getAtom(3)->id());
		
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
		builder.start(*ctx)
		.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c")
		.setAtomName(4, "d").setAtomName(5, "g").setAtomName(6, "x").setAtomName(7, "y")
		.startRule().addHead(1).addToBody(6, false).endRule() // a :- not x.
		.startRule().addHead(2).addToBody(1, true).endRule()  // b :- a.
		.startRule().addHead(1).addToBody(2, true).addToBody(4, true).endRule() // a :- b, d.
		.startRule().addHead(2).addToBody(5, false).endRule() // b :- not g.
		.startRule().addHead(3).addToBody(6, true).endRule()  // c :- x.
		.startRule().addHead(4).addToBody(3, true).endRule()  // d :- c.
		.startRule().addHead(3).addToBody(4, true).endRule()  // c :- d.
		.startRule().addHead(4).addToBody(5, false).endRule() // d :- not g.
		.startRule().addHead(7).addToBody(5, false).endRule() // y :- not g.
		.startRule().addHead(6).addToBody(7, true).endRule()  // x :- y.
		.startRule().addHead(5).addToBody(7, false).endRule() // g :- not y.
		.endProgram();
		
		SymbolTable& index = ctx->symbolTable();
		DG* graph          = ctx->sccGraph.get();
		CPPUNIT_ASSERT_EQUAL(index[6].lit, index[7].lit);
		CPPUNIT_ASSERT_EQUAL(~index[6].lit, index[5].lit);
		
		CPPUNIT_ASSERT( graph->getAtom(builder.getAtom(1)->id()).scc == 0 );
		CPPUNIT_ASSERT( graph->getAtom(builder.getAtom(2)->id()).scc == 0 );
		CPPUNIT_ASSERT( graph->getAtom(builder.getAtom(3)->id()).scc == 1 );
		CPPUNIT_ASSERT( graph->getAtom(builder.getAtom(4)->id()).scc == 1 );
		CPPUNIT_ASSERT( builder.getAtom(5)->id() == PrgNode::maxVertex );
		CPPUNIT_ASSERT( builder.getAtom(6)->eq() || builder.getAtom(6)->id() == PrgNode::maxVertex );
		CPPUNIT_ASSERT( builder.getAtom(7)->id() == PrgNode::maxVertex );
		
		CPPUNIT_ASSERT(uint32(11) == graph->nodes());
		// check that lists are partitioned by component number
		const DG::AtomNode& a =  graph->getAtom(builder.getAtom(1)->id());
		CPPUNIT_ASSERT(graph->getBody(a.body(0)).scc == PrgNode::noScc);
		CPPUNIT_ASSERT(graph->getBody(a.body(1)).scc == a.scc);
		CPPUNIT_ASSERT(a.bodies_begin()+2 == a.bodies_end());
		CPPUNIT_ASSERT_EQUAL(true, ctx->varInfo(a.lit.var()).frozen());

		const DG::BodyNode& bd = graph->getBody(a.body(1));
		CPPUNIT_ASSERT_EQUAL(true, ctx->varInfo(bd.lit.var()).frozen());
		CPPUNIT_ASSERT(graph->getAtom(bd.preds()[0]).lit == index[2].lit);
		CPPUNIT_ASSERT(bd.preds()[1]== idMax);
		CPPUNIT_ASSERT(bd.heads_begin()[0] == graph->id(a));
		CPPUNIT_ASSERT(bd.heads_begin()+1 == bd.heads_end());
	}

	void testWithSimpleCardinalityConstraint() {
		builder.start(*ctx)
			.setAtomName(1, "a").setAtomName(2, "b")
			.startRule(CHOICERULE).addHead(2).endRule()
			.startRule(CONSTRAINTRULE, 1).addHead(1).addToBody(1, true).addToBody(2,true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		DG* graph = ctx->sccGraph.get();
		CPPUNIT_ASSERT( uint32(3) == graph->nodes() );
		SymbolTable& index = ctx->symbolTable();
		const DG::AtomNode& a    = graph->getAtom(builder.getAtom(1)->id());
		const DG::BodyNode& body = graph->getBody(a.body(0));

		CPPUNIT_ASSERT(body.num_preds() == 2);
		CPPUNIT_ASSERT(body.extended());
		CPPUNIT_ASSERT(body.ext_bound() == 1);
		CPPUNIT_ASSERT(body.pred_inc() == 1);
		CPPUNIT_ASSERT(body.preds()[0] == graph->id(a));
		CPPUNIT_ASSERT(body.preds()[1] == idMax);
		CPPUNIT_ASSERT(body.preds()[2] == index[2].lit.asUint());
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
		builder.start(*ctx)
			.setAtomName(1, "a").setAtomName(2, "b").setAtomName(3, "c")
			.startRule(CHOICERULE).addHead(2).addHead(3).endRule()
			.startRule(WEIGHTRULE, 2).addHead(1).addToBody(1, true, 2).addToBody(2,true, 2).addToBody(3, true, 1).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		DG* graph = ctx->sccGraph.get();
		CPPUNIT_ASSERT( uint32(3) == graph->nodes() );
		
		SymbolTable& index = ctx->symbolTable();
		const DG::AtomNode& a    = graph->getAtom(builder.getAtom(1)->id());
		const DG::BodyNode& body = graph->getBody(a.body(0));

		CPPUNIT_ASSERT(body.num_preds() == 3);
		CPPUNIT_ASSERT(body.extended());
		CPPUNIT_ASSERT(body.ext_bound() == 2);
		CPPUNIT_ASSERT(body.pred_inc() == 2);
		CPPUNIT_ASSERT(body.preds()[0] == graph->id(a));
		CPPUNIT_ASSERT(body.preds()[2] == idMax);
		CPPUNIT_ASSERT(body.preds()[3] == index[2].lit.asUint());
		CPPUNIT_ASSERT(body.preds()[5] == index[3].lit.asUint());
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
		builder.start(*ctx, LogicProgram::AspOptions().noEq());
		builder.updateProgram();
		builder.setAtomName(1, "x").setAtomName(2, "y").setAtomName(3, "z").setAtomName(4, "a").setAtomName(5, "b");
		builder
			.startRule(CHOICERULE).addHead(1).addHead(2).addHead(3).endRule()
			.startRule().addHead(4).addToBody(5, true).endRule()
			.startRule().addHead(5).addToBody(4, true).endRule()
			.startRule().addHead(4).addToBody(1, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());		
		DG* graph  = ctx->sccGraph.get();
		uint32 nA  = builder.getAtom(4)->id();
		{
			const DG::AtomNode& a = graph->getAtom(nA);
			CPPUNIT_ASSERT(std::distance(a.bodies_begin(), a.bodies_end()) == 2);
		}

		builder.update();
		builder.setAtomName(6, "c").setAtomName(7, "d")
			.startRule(DISJUNCTIVERULE).addHead(6).addHead(7).endRule()
			.startRule().addHead(7).addToBody(6, true).endRule()
			.startRule().addHead(6).addToBody(7, true).endRule()
		;
		CPPUNIT_ASSERT_EQUAL(true, builder.endProgram());
		{
			const DG::AtomNode& a = graph->getAtom(nA);
			CPPUNIT_ASSERT(std::distance(a.bodies_begin(), a.bodies_end()) == 2);
		}
		const DG::AtomNode& c = graph->getAtom(builder.getAtom(6)->id());
		CPPUNIT_ASSERT(std::distance(c.bodies_begin(), c.bodies_end()) == 2);
	}
private:
	typedef SharedDependencyGraph DG;
	SharedContext* ctx;
	LogicProgram   builder;
};
CPPUNIT_TEST_SUITE_REGISTRATION(DependencyGraphTest);
} } 
