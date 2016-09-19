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
#include <clasp/solver_types.h>

namespace Clasp { namespace Test {

class LiteralTest : public CppUnit::TestFixture {
  CPPUNIT_TEST_SUITE(LiteralTest);
	CPPUNIT_TEST(testCtor);
	CPPUNIT_TEST(testId);
	CPPUNIT_TEST(testIdIgnoresFlag);
	CPPUNIT_TEST(testFromId);
	CPPUNIT_TEST(testFlag);
	CPPUNIT_TEST(testFlagCopy);
	CPPUNIT_TEST(testComplement);
	CPPUNIT_TEST(testComplementIsNotFlagged);
	CPPUNIT_TEST(testEquality);
	CPPUNIT_TEST(testValue);
	CPPUNIT_TEST(testLess);

	CPPUNIT_TEST(testAntecedentNullPointer);
	CPPUNIT_TEST(testAntecedentPointer);
	CPPUNIT_TEST(testAntecedentBin);
	CPPUNIT_TEST(testAntecedentTern);
	CPPUNIT_TEST_SUITE_END();
public:
	LiteralTest() {
		min = lit_true(), mid = posLit(varMax / 2),  max = posLit(varMax - 1);
	}
	void testCtor() {
		Literal p, q(42, true);
		CPPUNIT_ASSERT_EQUAL(Var(0), p.var());
		CPPUNIT_ASSERT_EQUAL(false, p.sign());
		CPPUNIT_ASSERT_EQUAL(false, p.flagged());

		CPPUNIT_ASSERT_EQUAL(Var(42), q.var());
		CPPUNIT_ASSERT_EQUAL(true, q.sign());
		CPPUNIT_ASSERT_EQUAL(false, q.flagged());

		Literal x = posLit(7);
		Literal y = negLit(7);
		CPPUNIT_ASSERT(x.var() == y.var() && y.var() == Var(7));
		CPPUNIT_ASSERT_EQUAL(false, x.sign());
		CPPUNIT_ASSERT_EQUAL(true, y.sign());
	}
	void testId() {
		uint32 minIdx	= min.id();
		uint32 maxIdx	= max.id();
		uint32 midIdx	= mid.id();

		CPPUNIT_ASSERT_EQUAL(uint32(0), minIdx);
		CPPUNIT_ASSERT_EQUAL(uint32(1), (~min).id());
		
		CPPUNIT_ASSERT_EQUAL(uint32((max.var()*2)), maxIdx);
		CPPUNIT_ASSERT_EQUAL(uint32((max.var()*2)+1), (~max).id());
		
		CPPUNIT_ASSERT_EQUAL(uint32((mid.var()*2)), midIdx);
		CPPUNIT_ASSERT_EQUAL(uint32((mid.var()*2)+1), (~mid).id());

	}
	void testIdIgnoresFlag() {
		Literal maxW = max;
		maxW.flag();
		CPPUNIT_ASSERT_EQUAL(max.id(), maxW.id());
	}
	void testFromId() {
		CPPUNIT_ASSERT(min == Literal::fromId(min.id()));
		CPPUNIT_ASSERT(max == Literal::fromId(max.id()));
		CPPUNIT_ASSERT(mid == Literal::fromId(mid.id()));
	}
	void testFlag() {
		Literal p = posLit(42);
		p.flag();
		CPPUNIT_ASSERT_EQUAL(true, p.flagged());
		p.unflag();
		CPPUNIT_ASSERT_EQUAL(false, p.flagged());
	}
	void testFlagCopy() {
		Literal p = posLit(42);
		p.flag();
		Literal q = p;
		CPPUNIT_ASSERT_EQUAL(true, q.flagged());
	}
	void testComplement() {
		Literal lit = posLit(7);
		Literal cLit = ~lit;
		CPPUNIT_ASSERT_EQUAL(lit.var(), cLit.var());
		CPPUNIT_ASSERT_EQUAL(false, lit.sign());
		CPPUNIT_ASSERT_EQUAL(true, cLit.sign());
		CPPUNIT_ASSERT_EQUAL(true, lit == ~~lit);
	}
	void testComplementIsNotFlagged() {
		Literal lit = posLit(7);
		lit.flag();
		Literal cLit = ~lit;
		CPPUNIT_ASSERT_EQUAL(false, cLit.flagged());
	}

	void testEquality() {
		Literal p = posLit(42);
		Literal q = negLit(42);
		CPPUNIT_ASSERT_EQUAL(p, p);
		CPPUNIT_ASSERT_EQUAL(p, ~q);
		CPPUNIT_ASSERT_EQUAL(false, p == q);
		CPPUNIT_ASSERT_EQUAL(Literal(), Literal());
	}

	void testValue() {
		CPPUNIT_ASSERT_EQUAL(value_true, trueValue(lit_true()));
		CPPUNIT_ASSERT_EQUAL(value_false, trueValue(lit_false()));
		CPPUNIT_ASSERT_EQUAL(value_false, falseValue(lit_true()));
		CPPUNIT_ASSERT_EQUAL(value_true, falseValue(lit_false()));
	}

	void testLess() {
		Literal p = posLit(42), q = negLit(42);
		CPPUNIT_ASSERT_EQUAL(false, p < p);
		CPPUNIT_ASSERT_EQUAL(false, q < q);
		CPPUNIT_ASSERT_EQUAL(true, p < q);
		CPPUNIT_ASSERT_EQUAL(false, q < p);

		Literal one(1, false);
		Literal two(2, true);
		Literal negOne = ~one;
		CPPUNIT_ASSERT_EQUAL(true, one < two);
		CPPUNIT_ASSERT_EQUAL(true, negOne < two);
		CPPUNIT_ASSERT_EQUAL(false, two < negOne);
	}
	
	void testAntecedentNullPointer() {
		Antecedent a;
		Antecedent b( (Constraint*) 0 );
		CPPUNIT_ASSERT_EQUAL(true, a.isNull());
		CPPUNIT_ASSERT_EQUAL(true, b.isNull());
	}

	void testAntecedentPointer() {
		struct Con : Constraint {
			PropResult propagate(Solver&, Literal, uint32&) { return PropResult(true, true); }
			void reason(Solver&, Literal, LitVec&) {}
			Constraint* cloneAttach(Solver&) { return 0; }
		};
		
		Constraint* c = new Con;
		Antecedent a(c);
		CPPUNIT_ASSERT_EQUAL(false, a.isNull());
		CPPUNIT_ASSERT_EQUAL(Antecedent::Generic, a.type());
		CPPUNIT_ASSERT_EQUAL(c, a.constraint());
		c->destroy();
	}

	void testAntecedentBin() {
		CPPUNIT_ASSERT_EQUAL(true, testBin(max));
		CPPUNIT_ASSERT_EQUAL(true, testBin(min));
		CPPUNIT_ASSERT_EQUAL(true, testBin(mid));
	}

	void testAntecedentTern() {
		CPPUNIT_ASSERT_EQUAL(true, testTern(max, max));
		CPPUNIT_ASSERT_EQUAL(true, testTern(max, mid));
		CPPUNIT_ASSERT_EQUAL(true, testTern(max, min));
		CPPUNIT_ASSERT_EQUAL(true, testTern(mid, max));
		CPPUNIT_ASSERT_EQUAL(true, testTern(mid, mid));
		CPPUNIT_ASSERT_EQUAL(true, testTern(mid, min));
		CPPUNIT_ASSERT_EQUAL(true, testTern(min, max));
		CPPUNIT_ASSERT_EQUAL(true, testTern(min, mid));
		CPPUNIT_ASSERT_EQUAL(true, testTern(min, min));
	}
private:
	Literal min, mid, max;
	bool testBin(const Literal& p) {
		Antecedent ap(p);
		Antecedent aNotp(~p);
		CPPUNIT_ASSERT_EQUAL(false, ap.isNull());
		CPPUNIT_ASSERT_EQUAL(Antecedent::Binary, ap.type());
		CPPUNIT_ASSERT(p == ap.firstLiteral());

		CPPUNIT_ASSERT_EQUAL(false, aNotp.isNull());
		CPPUNIT_ASSERT_EQUAL(Antecedent::Binary, aNotp.type());
		CPPUNIT_ASSERT(~p == aNotp.firstLiteral());
		return true;
	}
	bool testTern(const Literal& p, const Literal& q) {
		Antecedent app(p, q);
		Antecedent apn(p, ~q);
		Antecedent anp(~p, q);
		Antecedent ann(~p, ~q);

		CPPUNIT_ASSERT_EQUAL(false, app.isNull());
		CPPUNIT_ASSERT_EQUAL(Antecedent::Ternary, app.type());
		CPPUNIT_ASSERT_EQUAL(false, apn.isNull());
		CPPUNIT_ASSERT_EQUAL(Antecedent::Ternary, apn.type());
		CPPUNIT_ASSERT_EQUAL(false, anp.isNull());
		CPPUNIT_ASSERT_EQUAL(Antecedent::Ternary, anp.type());
		CPPUNIT_ASSERT_EQUAL(false, ann.isNull());
		CPPUNIT_ASSERT_EQUAL(Antecedent::Ternary, ann.type());
		
		CPPUNIT_ASSERT(p == app.firstLiteral() && q == app.secondLiteral());
		CPPUNIT_ASSERT(p == apn.firstLiteral() && ~q == apn.secondLiteral());
		CPPUNIT_ASSERT(~p == anp.firstLiteral() && q == anp.secondLiteral());
		CPPUNIT_ASSERT(~p == ann.firstLiteral() && ~q == ann.secondLiteral());
		return true;
	}
};

CPPUNIT_TEST_SUITE_REGISTRATION(LiteralTest);
} } 
