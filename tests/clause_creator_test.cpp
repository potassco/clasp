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
#include <clasp/clause.h>
#include <clasp/solver.h>

#include <catch2/catch_test_macros.hpp>

#include <algorithm>

namespace Clasp::Test {
using namespace Clasp::mt;

TEST_CASE("ClauseCreator create", "[constraint][core]") {
    SharedContext ctx;
    ClauseCreator creator;
    Literal       a, b, c, d, e;
    a = posLit(ctx.addVar(VarType::atom));
    b = posLit(ctx.addVar(VarType::atom));
    c = posLit(ctx.addVar(VarType::atom));
    d = posLit(ctx.addVar(VarType::atom));
    e = posLit(ctx.addVar(VarType::atom));
    creator.setSolver(*ctx.master());
    ctx.startAddConstraints(1);
    Solver& s = *ctx.master();
    SECTION("test empty clause is false") { REQUIRE_FALSE((bool) creator.start().end()); }
    SECTION("test facts are asserted") {
        REQUIRE((bool) creator.start().add(a).end());
        REQUIRE(s.isTrue(a));
    }
    SECTION("test top level sat clauses are not added") {
        s.force(a, nullptr);
        REQUIRE((bool) creator.start().add(a).add(b).end());
        REQUIRE(0u == ctx.numConstraints());
    }
    SECTION("test top level false lits are removed") {
        s.force(~a, nullptr);
        REQUIRE((bool) creator.start().add(a).add(b).end());
        REQUIRE(0u == ctx.numConstraints());
        REQUIRE(s.isTrue(b));
    }
    SECTION("test add binary clause") {
        REQUIRE((bool) creator.start().add(a).add(b).end());
        REQUIRE(1u == ctx.numConstraints());
        REQUIRE(1u == ctx.numBinary());
    }
    SECTION("test add ternary clause") {
        REQUIRE((bool) creator.start().add(a).add(b).add(c).end());
        REQUIRE(1u == ctx.numConstraints());
        REQUIRE(1u == ctx.numTernary());
    }
    SECTION("test add generic clause") {
        REQUIRE((bool) creator.start().add(a).add(b).add(c).add(d).end());
        REQUIRE(1u == ctx.numConstraints());
    }
    SECTION("test creator acquires missing vars") {
        Literal f = posLit(ctx.addVar(VarType::atom));
        Literal g = posLit(ctx.addVar(VarType::atom));
        Literal h = posLit(ctx.addVar(VarType::atom));
        REQUIRE_FALSE(s.validVar(f.var()));
        REQUIRE_FALSE(s.validVar(g.var()));
        REQUIRE_FALSE(s.validVar(h.var()));
        REQUIRE((bool) creator.start().add(a).add(b).add(g).add(f).end());
        REQUIRE(1u == ctx.numConstraints());
        REQUIRE(s.validVar(f.var()));
        REQUIRE(s.validVar(g.var()));
        REQUIRE(s.validVar(h.var()));
    }
    SECTION("test creator asserts first literal") {
        ctx.endInit();
        s.assume(~b);
        s.assume(~c);
        s.assume(~d);
        s.propagate();
        REQUIRE((bool) creator.start(ConstraintType::conflict).add(a).add(b).add(c).add(d).end());
        REQUIRE(s.isTrue(a));
        REQUIRE_FALSE(s.hasConflict());
        REQUIRE(1u == s.numLearntConstraints());
    }
    SECTION("test creator inits watches") {
        ctx.endInit();
        s.assume(~b);
        s.assume(~c);
        s.assume(~d);

        creator.start(ConstraintType::conflict).add(a).add(b).add(d).add(c);
        REQUIRE((bool) creator.end()); // asserts a
        s.undoUntil(2);                // clear a and d
        s.assume(~d);                  // hopefully d was watched.
        s.propagate();
        REQUIRE(value_true == s.value(a.var()));
    }
    SECTION("test add successive") {
        creator.start(ConstraintType::conflict).add(a);
        s.assume(b) && s.propagate();
        creator.add(~b);
        s.assume(c) && s.propagate();
        creator.add(~c);
        s.assume(d) && s.propagate();
        creator.add(~d);
        creator.end();
        REQUIRE(creator[0] == a);
    }
    SECTION("test creator simplify") {
        SECTION("creator removes duplicate literals") {
            creator.start().add(a).add(b).add(c).add(a).add(b).add(d).prepare(true);
            REQUIRE(creator.size() == 4);
            REQUIRE(creator[0] == a);
            REQUIRE(creator[1] == b);
            REQUIRE(creator[2] == c);
            REQUIRE(creator[3] == d);
        }
        SECTION("creator detects tautologies") {
            creator.start().add(a).add(b).add(c).add(a).add(b).add(~a).end(ClauseCreator::clause_force_simplify);
            REQUIRE(0 == ctx.numConstraints());
        }
        SECTION("test creator moves watches") {
            ctx.endInit();
            s.assume(a) && s.propagate();
            s.assume(b) && s.propagate();
            creator.start(ConstraintType::loop);
            creator.add(~a).add(~b).add(~b).add(~a).add(c).add(d).prepare(true);
            REQUIRE(creator.size() == 4);
            REQUIRE(c == creator[0]);
            REQUIRE(d == creator[1]);
        }
        SECTION("test regression") {
            LitVec clause;
            clause.push_back(lit_false);
            clause.push_back(a);
            clause.push_back(b);
            ClauseCreator::prepare(*ctx.master(), clause, ClauseCreator::clause_force_simplify);
            REQUIRE(clause.size() == 2);
        }
    }
    SECTION("test create non-asserting learnt clause") {
        ctx.endInit();
        s.assume(a);
        s.propagate();
        s.assume(b);
        s.propagate();
        creator.start(ConstraintType::loop);
        creator.add(~a).add(~b).add(c).add(d);
        REQUIRE(creator.end());
        REQUIRE(c == creator[0]);
        REQUIRE(d == creator[1]);
        REQUIRE(s.numLearntConstraints() == 1);

        s.undoUntil(0);
        // test with a short clause
        s.assume(a);
        s.propagate();
        creator.start(ConstraintType::loop);
        creator.add(~a).add(b).add(c);
        REQUIRE(creator.end());
        REQUIRE(b == creator[0]);
        REQUIRE(c == creator[1]);
        REQUIRE(ctx.numLearntShort() == 1);
    }
    SECTION("test create conflicting learnt clause") {
        ctx.endInit();
        s.assume(a);
        s.force(b, nullptr);
        s.propagate(); // level 1
        s.assume(c);
        s.propagate(); // level 2
        s.assume(d);
        s.propagate(); // level 3
        s.assume(e);
        s.propagate(); // level 4

        creator.start(ConstraintType::loop);
        creator.add(~c).add(~a).add(~d).add(~b); // 2 1 3 1
        REQUIRE_FALSE((bool) creator.end());
        // make sure we watch the highest levels, i.e. 3 and 2
        REQUIRE(~d == creator[0]);
        REQUIRE(~c == creator[1]);
        REQUIRE(s.numLearntConstraints() == 0);

        s.undoUntil(0);
        // test with a short clause
        s.assume(a);
        s.propagate(); // level 1
        s.assume(c);
        s.propagate(); // level 2
        creator.start(ConstraintType::loop);
        creator.add(~a).add(~c);
        REQUIRE_FALSE((bool) creator.end());
        REQUIRE(~c == creator[0]);
        REQUIRE(~a == creator[1]);
        REQUIRE(ctx.numBinary() == 0);
    }

    SECTION("test create asserting learnt clause") {
        ctx.endInit();
        s.assume(a);
        s.force(b, nullptr);
        s.propagate(); // level 1
        s.assume(c);
        s.propagate(); // level 2
        creator.start(ConstraintType::loop);
        creator.add(~c).add(~a).add(d).add(~b); // 2 1 Free 1
        REQUIRE((bool) creator.end());
        // make sure we watch the right lits, i.e. d (free) and ~c (highest DL)
        REQUIRE(d == creator[0]);
        REQUIRE(~c == creator[1]);
        REQUIRE(s.isTrue(d));
        REQUIRE(s.numLearntConstraints() == 1);
        // test with a short clause
        s.undoUntil(0);
        s.reduceLearnts(1.0f);
        s.assume(a);
        s.force(b, nullptr);
        s.propagate(); // level 1
        s.assume(c);
        s.propagate(); // level 2
        creator.start(ConstraintType::loop);
        creator.add(~c).add(~a).add(d); // 2 1 Free
        REQUIRE((bool) creator.end());
        // make sure we watch the right lits, i.e. d (free) and ~c (highest DL)
        REQUIRE(d == creator[0]);
        REQUIRE(~c == creator[1]);
        REQUIRE(s.isTrue(d));
    }

    SECTION("test create bogus unit") {
        s.assume(a) && s.propagate();
        s.assume(~b) && s.propagate();
        s.force(~d, nullptr) && s.propagate();
        s.assume(~c) && s.propagate();
        REQUIRE(s.decisionLevel() == 3);

        creator.start(ConstraintType::other).add(d).add(b).add(c).add(a);
        REQUIRE(ClauseCreator::status(s, creator.lits()) == ClauseCreator::status_sat);

        ClauseCreator::Result r = creator.end();
        REQUIRE(r.ok());
        REQUIRE(s.decisionLevel() == 3);
    }
    SECTION("test creator notifies heuristic") {
        struct FakeHeu : SelectFirst {
            void newConstraint(const Solver&, LitView lits, ConstraintType t) override {
                clSizes.push_back(size32(lits));
                clTypes.push_back(t);
            }
            std::vector<uint32_t>       clSizes;
            std::vector<ConstraintType> clTypes;
        }* heu;
        s.setHeuristic(heu = new FakeHeu());
        REQUIRE((bool) creator.start().add(a).add(b).add(c).add(d).end());
        ctx.endInit();
        s.assume(a);
        s.assume(b);
        s.propagate();

        REQUIRE((bool) creator.start(ConstraintType::conflict).add(c).add(~a).add(~b).end());

        REQUIRE((bool) creator.start(ConstraintType::loop).add(c).add(~a).add(~b).end({}));

        REQUIRE(3u == size32(heu->clSizes));
        REQUIRE(4u == heu->clSizes[0]);
        REQUIRE(3u == heu->clSizes[1]);
        REQUIRE(3u == heu->clSizes[2]);

        REQUIRE(ConstraintType::static_ == heu->clTypes[0]);
        REQUIRE(ConstraintType::conflict == heu->clTypes[1]);
        REQUIRE(ConstraintType::loop == heu->clTypes[2]);
    }
}
TEST_CASE("ClauseCreator integrate", "[constraint][core]") {
    SharedContext ctx;
    ClauseCreator creator;
    Literal       a, b, c, d, e, f;
    a = posLit(ctx.addVar(VarType::atom));
    b = posLit(ctx.addVar(VarType::atom));
    c = posLit(ctx.addVar(VarType::atom));
    d = posLit(ctx.addVar(VarType::atom));
    e = posLit(ctx.addVar(VarType::atom));
    f = posLit(ctx.addVar(VarType::atom));
    creator.setSolver(*ctx.master());
    ctx.startAddConstraints(1);
    Solver& s = *ctx.master();
    LitVec  cl;
    SECTION("test can't integrate empty clause") {
        s.assume(~a) && s.propagate();
        s.pushRootLevel(s.decisionLevel());
        SharedLiterals*       p(SharedLiterals::newShareable(cl, ConstraintType::other));
        ClauseCreator::Result r = ClauseCreator::integrate(s, p, {});
        REQUIRE_FALSE(r.ok());
        REQUIRE(s.hasConflict());
        REQUIRE_FALSE(s.clearAssumptions());
    }
    SECTION("test integrate unit clause") {
        s.assume(a) && s.propagate();
        s.assume(b) && s.propagate();
        s.assume(c) && s.propagate();
        s.assume(d) && s.propagate();
        s.pushRootLevel(s.decisionLevel());
        s.assume(e) && s.propagate();

        // ~a ~b ~c f -> Unit: f@3
        cl.push_back(~a);
        cl.push_back(f);
        cl.push_back(~c);
        cl.push_back(~b);
        SharedLiterals* p(SharedLiterals::newShareable(cl, ConstraintType::other));
        ClauseCreator::integrate(s, p, {});
        REQUIRE(s.isTrue(f));
        REQUIRE(s.decisionLevel() == s.rootLevel());
        s.popRootLevel();
        s.backtrack() && s.propagate();
        REQUIRE(s.isTrue(f));
        REQUIRE(s.decisionLevel() == s.rootLevel());
        s.popRootLevel();
        s.backtrack() && s.propagate();
        REQUIRE_FALSE(s.isTrue(f));
        REQUIRE(s.value(c.var()) == value_free);
    }

    SECTION("test integrate sat unit clause") {
        s.assume(a) && s.propagate();
        cl.push_back(a);
        SharedLiterals* p(SharedLiterals::newShareable(cl, ConstraintType::other));
        ClauseCreator::integrate(s, p, {});
        REQUIRE(s.isTrue(a));
        REQUIRE(s.decisionLevel() == 0);
    }

    SECTION("test integrate conflicting clause") {
        s.assume(a) && s.propagate();
        s.assume(b) && s.propagate();
        s.assume(c) && s.propagate();
        s.force(d, nullptr) && s.propagate();

        // ~a ~b ~c ~d -> conflicting@3
        cl.push_back(~a);
        cl.push_back(~c);
        cl.push_back(~b);
        cl.push_back(~d);
        SharedLiterals*       p(SharedLiterals::newShareable(cl, ConstraintType::other));
        ClauseCreator::Result r = ClauseCreator::integrate(s, p, {});
        REQUIRE_FALSE(r.ok());
        REQUIRE(r.local != 0);
        REQUIRE(s.hasConflict());
    }

    SECTION("test integrate asserting conflict") {
        s.assume(a) && s.propagate();
        s.assume(b) && s.propagate();
        s.assume(c) && s.propagate();
        s.assume(d) && s.propagate();

        // ~a ~b ~c -> Conflict @3
        cl.push_back(~a);
        cl.push_back(~c);
        cl.push_back(~b);
        SharedLiterals* p(SharedLiterals::newShareable(cl, ConstraintType::other));
        ClauseCreator::integrate(s, p, {});
        REQUIRE(s.decisionLevel() == 2u);
    }
    SECTION("test integrate asserting conflict below root") {
        s.assume(a) && s.propagate();
        s.assume(b) && s.propagate();
        s.assume(d) && s.propagate();
        s.pushRootLevel(s.decisionLevel());
        s.assume(c) && s.propagate();
        // ~a ~b ~c -> Conflict @3, Asserting @2
        cl.push_back(~a);
        cl.push_back(~c);
        cl.push_back(~b);
        SharedLiterals* p(SharedLiterals::newShareable(cl, ConstraintType::other));
        ClauseCreator::integrate(s, p, {});
        REQUIRE(s.decisionLevel() == 3u);
        s.popRootLevel();
        s.backtrack() && s.propagate();
        REQUIRE(s.isTrue(~c));
    }
    SECTION("test integrate conflict below root()") {
        cl.push_back(a);
        cl.push_back(b);
        cl.push_back(c);
        s.assume(~a) && s.propagate();
        s.assume(~b) && s.propagate();
        s.assume(~c) && s.propagate();
        s.assume(~d) && s.propagate();
        s.pushRootLevel(s.decisionLevel());
        SharedLiterals*       p(SharedLiterals::newShareable(cl, ConstraintType::other));
        ClauseCreator::Result r = ClauseCreator::integrate(s, p, ClauseCreator::clause_explicit);
        REQUIRE_FALSE(r.ok());
        REQUIRE(1u == s.numLearntConstraints());
    }
    SECTION("test init watches") {
        cl.push_back(a);
        cl.push_back(b);
        cl.push_back(c);
        cl.push_back(d);
        s.assume(~b) && s.propagate();
        s.force(~c, nullptr) && s.propagate();
        s.assume(~a) && s.propagate();
        s.assume(d) && s.propagate();
        // aF@2 bF@1 cF@1 dT@3 -> dT@3 aF@2 cF@1 bF@1
        LitVec temp = cl;
        ClauseCreator::prepare(s, temp, {});
        REQUIRE(temp[0] == d);
        REQUIRE(temp[1] == a);

        SharedLiterals*        p(SharedLiterals::newShareable(cl, ConstraintType::other));
        ClauseCreator::Result  r = ClauseCreator::integrate(s, p, ClauseCreator::clause_no_add);
        ClauseHead::TempBuffer buffer;
        auto                   lits = r.local->clause()->toLits(buffer);
        REQUIRE(lits[0] == d);
        REQUIRE(lits[1] == a);
        r.local->destroy(&s, true);
    }
    SECTION("test integrate unsat") {
        s.force(~a, nullptr) && s.propagate();
        s.assume(b);
        cl.push_back(a);
        SharedLiterals*       p(SharedLiterals::newShareable(cl, ConstraintType::other));
        ClauseCreator::Result r = ClauseCreator::integrate(s, p, {});
        REQUIRE_FALSE(r.ok());
        REQUIRE(0 == r.local);
        REQUIRE(0u == s.decisionLevel());
    }
    SECTION("test integrate sat") {
        cl.push_back(d);
        cl.push_back(b);
        cl.push_back(a);
        cl.push_back(c);
        SECTION("test1") {
            s.assume(~a) && s.propagate();
            s.assume(b) && s.propagate();
            s.assume(~d) && s.propagate();
            do {
                SharedLiterals*       p(SharedLiterals::newShareable(cl, ConstraintType::other));
                ClauseCreator::Result r = ClauseCreator::integrate(s, p, ClauseCreator::clause_not_sat);
                REQUIRE(r.ok());
                REQUIRE(s.numAssignedVars() == 3);
            } while (std::ranges::next_permutation(cl).found);
            REQUIRE(s.numLearntConstraints() == 0);
        }
        SECTION("bug1") {
            s.assume(~a) && s.propagate();
            s.assume(b) && s.propagate();
            s.assume(~d) && s.propagate();
            SharedLiterals*       p(SharedLiterals::newShareable(cl, ConstraintType::other));
            ClauseCreator::Result r = ClauseCreator::integrate(s, p, {});
            REQUIRE(r.ok());
            REQUIRE(3u == s.numAssignedVars());
        }
        SECTION("bug2") {
            s.assume(~a) && s.propagate();
            s.assume(b) && s.propagate();
            s.assume(~d) && s.propagate();
            s.force(c, nullptr) && s.propagate();
            SharedLiterals*       p(SharedLiterals::newShareable(cl, ConstraintType::other));
            ClauseCreator::Result r = ClauseCreator::integrate(s, p, {});
            REQUIRE(r.ok());
        }
        SECTION("bug3") {
            s.assume(~a) && s.propagate();
            s.assume(~b) && s.propagate();
            s.force(~d, nullptr) && s.propagate();
            s.assume(c) && s.propagate();
            REQUIRE(s.decisionLevel() == 3);
            SharedLiterals*       p(SharedLiterals::newShareable(cl, ConstraintType::other));
            ClauseCreator::Result r = ClauseCreator::integrate(s, p, ClauseCreator::clause_not_sat);
            REQUIRE(r.ok());
            REQUIRE(s.decisionLevel() == 2);
            REQUIRE(s.isTrue(c));
        }
        SECTION("bug4") {
            cl.clear();
            cl.push_back(a);
            cl.push_back(b);
            s.force(~a, nullptr);
            s.assume(b);
            SharedLiterals* p(SharedLiterals::newShareable(cl, ConstraintType::other));
            REQUIRE(Potassco::test(ClauseCreator::status(s, p->literals()), ClauseCreator::status_unit));
            ClauseCreator::integrate(s, p, ClauseCreator::clause_explicit);
        }
    }
    SECTION("test integrate known order") {
        cl.push_back(a);
        SharedLiterals* p(SharedLiterals::newShareable(cl, ConstraintType::other));
        REQUIRE(Potassco::test(ClauseCreator::status(s, p->literals()), ClauseCreator::status_unit));
        ClauseCreator::integrate(s, p, ClauseCreator::clause_no_prepare);
        REQUIRE(s.isTrue(a));
    }
    SECTION("test integrate not conflicting") {
        cl.push_back(a);
        cl.push_back(b);
        SharedLiterals* p(SharedLiterals::newShareable(cl, ConstraintType::other));
        s.assume(~a) && s.propagate();
        s.force(~b, nullptr) && s.propagate();
        REQUIRE(Potassco::test(ClauseCreator::status(s, p->literals()), ClauseCreator::status_unsat));
        ClauseCreator::Result r = ClauseCreator::integrate(s, p, ClauseCreator::clause_not_conflict);
        REQUIRE(r.ok() == false);
        REQUIRE(r.local == 0);
    }
    SECTION("test integrate asserting below BT") {
        s.assume(a) && s.propagate();
        s.assume(b) && s.propagate();
        s.assume(c) && s.propagate();
        s.assume(d) && s.propagate();
        s.setBacktrackLevel(s.decisionLevel());
        // ~a ~b ~c -> Conflict @3, Asserting @2
        cl.push_back(~a);
        cl.push_back(~c);
        cl.push_back(~b);
        SharedLiterals*       p(SharedLiterals::newShareable(cl, ConstraintType::other));
        ClauseCreator::Result r = ClauseCreator::integrate(s, p, {});
        REQUIRE_FALSE(r.ok());
        s.backtrack();
        REQUIRE(s.isTrue(~c));
        REQUIRE(2u == s.decisionLevel());
        s.backtrack();
        REQUIRE_FALSE(s.isTrue(~c));
    }
    SECTION("test integrate conflict below BT") {
        s.assume(a) && s.propagate();
        s.assume(b) && s.force(c, nullptr) && s.propagate();
        s.assume(d) && s.propagate();
        s.assume(e) && s.propagate();
        s.setBacktrackLevel(s.decisionLevel());
        // ~a ~b ~c -> Conflict @2
        cl.push_back(~a);
        cl.push_back(~c);
        cl.push_back(~b);
        SharedLiterals*       p(SharedLiterals::newShareable(cl, ConstraintType::other));
        ClauseCreator::Result r = ClauseCreator::integrate(s, p, {});
        REQUIRE_FALSE(r.ok());
        REQUIRE(s.resolveConflict());
        REQUIRE(1u == s.decisionLevel());
    }
    SECTION("test simplify") {
        SECTION("test1") {
            cl.push_back(a);
            cl.push_back(b);
            cl.push_back(c);
            cl.push_back(d);
            cl.push_back(e);
            cl.push_back(f);
            SharedLiterals* p(SharedLiterals::newShareable(cl, ConstraintType::other));
            s.force(~d, nullptr) && s.propagate();
            s.assume(~a) && s.propagate();
            ClauseCreator::Result r = ClauseCreator::integrate(s, p, ClauseCreator::clause_no_add);
            REQUIRE(r.ok());
            REQUIRE(r.local != 0);
            ClauseHead::TempBuffer buffer;
            auto                   lits = r.local->toLits(buffer);
            REQUIRE(lits.size() == 5);
            REQUIRE_FALSE(contains(lits, d));
        }
        SECTION("test facts are removed from learnt") {
            ctx.enableStats(1);
            ctx.addUnary(a);
            ctx.endInit();
            s.assume(~b) && s.propagate();
            creator.start(ConstraintType::conflict);
            creator.add(b).add(c).add(~a).end();

            REQUIRE(1u == ctx.numLearntShort());
            REQUIRE(s.stats.extra->lits[0] == 2);
        }
    }
}

} // namespace Clasp::Test
