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
#include <set>

namespace Clasp::Test {
static int countWatches(const Solver& s, ClauseHead* c, const LitVec& lits) {
    int w = 0;
    for (auto lit : lits) { w += s.hasWatch(~lit, c); }
    return w;
}
static ClauseHead* createClause(Solver& s, LitVec& lits, const ConstraintInfo& info = ConstraintType::static_) {
    auto flags = ClauseCreator::clause_explicit | ClauseCreator::clause_no_add | ClauseCreator::clause_no_prepare;
    return ClauseCreator::create(s, lits, flags, info).local;
}
static ClauseHead* createShared(Solver& s, LitVec& lits, const ConstraintInfo& info = ConstraintType::static_) {
    assert(lits.size() >= 2);
    auto* shared_lits = SharedLiterals::newShareable(lits, info.type());
    return Clasp::Clause::newShared(s, shared_lits, info, lits.data(), false);
}
static LitVec& makeLits(LitVec& lits, uint32_t pos, uint32_t neg) {
    lits.clear();
    for (uint32_t i : irange(pos + neg)) {
        if (pos) {
            lits.push_back(posLit(i + 1));
            --pos;
        }
        else {
            lits.push_back(negLit(i + 1));
        }
    }
    return lits;
}

TEST_CASE("Clause", "[core][constraint]") {
    using ClauseInfo = ConstraintInfo;
    SharedContext ctx;
    for ([[maybe_unused]] auto _ : irange(14u)) { ctx.addVar(VarType::atom); }
    Literal x1 = posLit(1), x2 = posLit(2), x3 = posLit(3);
    ctx.startAddConstraints(10);
    Solver&     solver = *ctx.master();
    LitVec      clLits;
    ClauseHead* cl = nullptr;
    SECTION("with simple clause") {
        makeLits(clLits, 2, 2);
        SECTION("test ctor adds watches") {
            cl = createClause(solver, clLits, ConstraintType::static_);
            solver.add(cl);
            REQUIRE(2 == countWatches(solver, cl, clLits));
        }
        SECTION("test clause types") {
            ClauseInfo t;
            SECTION("static") { t = ConstraintType::static_; }
            SECTION("conflict") { t = ConstraintType::conflict; }
            SECTION("loop") { t = ConstraintType::loop; }
            cl = createClause(solver, clLits, t);
            REQUIRE(cl->type() == t.type());
            cl->destroy();
        }
        SECTION("testPropGenericClause") {
            solver.add(cl = createClause(solver, clLits));
            solver.assume(~clLits[0]);
            solver.propagate();
            solver.assume(~clLits.back());
            solver.propagate();

            solver.assume(~clLits[1]);
            solver.propagate();

            REQUIRE(solver.isTrue(clLits[2]));
            REQUIRE(cl->locked(solver));
            Antecedent reason = solver.reason(clLits[2]);
            REQUIRE(reason == cl);

            LitVec r;
            reason.reason(solver, clLits[2], r);
            REQUIRE(contains(r, ~clLits[0]));
            REQUIRE(contains(r, ~clLits[1]));
            REQUIRE(contains(r, ~clLits[3]));
        }
        SECTION("testClauseActivity") {
            uint32_t    exp = 258;
            ClauseHead* cl1 = createClause(solver, clLits, ClauseInfo(ConstraintType::conflict).setActivity(exp));
            ClauseHead* cl2 = createClause(solver, clLits, ClauseInfo(ConstraintType::loop).setActivity(exp));
            solver.add(cl1);
            solver.add(cl2);
            while (exp != 0) {
                REQUIRE(
                    (cl1->activity().activity() == cl2->activity().activity() && cl1->activity().activity() == exp));
                exp >>= 1;
                cl1->decreaseActivity();
                cl2->decreaseActivity();
            }
            REQUIRE((cl1->activity().activity() == cl2->activity().activity() && cl1->activity().activity() == exp));
        }
        SECTION("testPropGenericClauseConflict") {
            solver.add(cl = createClause(solver, clLits));
            solver.assume(~clLits[0]);
            solver.force(~clLits[1], nullptr);
            solver.force(~clLits[2], nullptr);
            solver.force(~clLits[3], nullptr);

            REQUIRE_FALSE(solver.propagate());
            const auto& r = solver.conflict();
            REQUIRE(contains(r, ~clLits[0]));
            REQUIRE(contains(r, ~clLits[1]));
            REQUIRE(contains(r, ~clLits[2]));
            REQUIRE(contains(r, ~clLits[3]));
        }
        SECTION("testPropAlreadySatisfied") {
            solver.add(cl = createClause(solver, clLits));

            // satisfy the clause...
            solver.force(clLits[2], nullptr);
            solver.propagate();

            // ...make all but one literal false
            solver.force(~clLits[0], nullptr);
            solver.force(~clLits[1], nullptr);
            solver.propagate();

            // ...and assert that the last literal is still unassigned
            REQUIRE(value_free == solver.value(clLits[3].var()));
        }
        SECTION("testReasonBumpsActivityIfLearnt") {
            ctx.endInit();
            ClauseHead* cl1 = createClause(solver, clLits, ClauseInfo(ConstraintType::conflict));
            solver.addLearnt(cl1, size32(clLits));
            solver.assume(~clLits[0]);
            solver.propagate();
            solver.assume(~clLits[1]);
            solver.propagate();
            solver.assume(~clLits[2]);
            uint32_t a = cl1->activity().activity();
            solver.force(~clLits[3], Antecedent(nullptr));
            REQUIRE_FALSE(solver.propagate());
            REQUIRE(a + 1 == cl1->activity().activity());
        }
        SECTION("testSimplifyUnitButNotLocked") {
            solver.add(cl = createClause(solver, clLits));
            solver.force(clLits[0], nullptr); // SAT clause
            solver.force(~clLits[1], nullptr);
            solver.force(~clLits[2], nullptr);
            solver.force(~clLits[3], nullptr);
            solver.propagate();
            REQUIRE(cl->simplify(solver, false));
        }
    }

    SECTION("testSimplifySAT") {
        makeLits(clLits, 3, 2);
        solver.add(cl = createClause(solver, clLits));
        solver.force(~clLits[1], nullptr);
        solver.force(clLits[2], nullptr);
        solver.propagate();

        REQUIRE(cl->simplify(solver, false));
    }
    SECTION("testSimplifyRemovesFalseLitsBeg") {
        solver.add(cl = createClause(solver, makeLits(clLits, 3, 3)));
        REQUIRE(6 == cl->size());

        solver.force(~clLits[0], nullptr);
        solver.force(~clLits[1], nullptr);
        solver.propagate();

        REQUIRE_FALSE(cl->simplify(solver));
        REQUIRE(4 == cl->size());

        REQUIRE(2 == countWatches(solver, cl, clLits));
    }

    SECTION("testSimplifyRemovesFalseLitsMid") {
        solver.add(cl = createClause(solver, makeLits(clLits, 3, 3)));
        REQUIRE(6 == cl->size());
        solver.force(~clLits[1], nullptr);
        solver.force(~clLits[2], nullptr);
        solver.propagate();

        REQUIRE_FALSE(cl->simplify(solver));
        REQUIRE(4 == cl->size());

        REQUIRE(2 == countWatches(solver, cl, clLits));
    }

    SECTION("test simplify short") {
        solver.add(cl = createClause(solver, makeLits(clLits, 2, 3)));
        SECTION("removesFalseLitsBeg") {
            solver.force(~clLits[0], nullptr);
            solver.propagate();
        }
        SECTION("removesFalseLitsMid") {
            solver.force(~clLits[2], nullptr);
            solver.propagate();
        }
        SECTION("removesFalseLitsEnd") {
            solver.force(~clLits[4], nullptr);
            solver.propagate();
        }
        REQUIRE_FALSE(cl->simplify(solver));
        REQUIRE(4 == cl->size());
        REQUIRE(2 == countWatches(solver, cl, clLits));
    }
    SECTION("testSimplifyRemovesFalseLitsEnd") {
        solver.add(cl = createClause(solver, makeLits(clLits, 3, 3)));
        REQUIRE(6 == cl->size());

        solver.force(~clLits[4], nullptr);
        solver.force(~clLits[5], nullptr);
        solver.propagate();

        REQUIRE_FALSE(cl->simplify(solver));
        REQUIRE(4 == cl->size());

        REQUIRE(2 == countWatches(solver, cl, clLits));
    }
    SECTION("testStrengthen") {
        cl = createClause(solver, makeLits(clLits, 6, 0), ClauseInfo());
        REQUIRE_FALSE(cl->strengthen(solver, x2).removeClause);
        REQUIRE(cl->size() == 5);
        REQUIRE_FALSE(cl->strengthen(solver, x3).removeClause);
        REQUIRE(cl->size() == 4);

        REQUIRE(cl->strengthen(solver, x1).removeClause);
        REQUIRE(cl->size() == 3);
        cl->destroy(&solver, true);
    }

    SECTION("testStrengthenToUnary") {
        Literal b = posLit(ctx.addVar(VarType::atom));
        Literal x = posLit(ctx.addVar(VarType::atom));
        Literal y = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        ctx.endInit();
        Literal a = posLit(solver.pushTagVar(true));
        solver.assume(x) && solver.propagate();
        solver.assume(y) && solver.propagate();
        solver.setBacktrackLevel(solver.decisionLevel());
        clLits.clear();
        clLits.push_back(b);
        clLits.push_back(~a);
        ClauseInfo extra(ConstraintType::conflict);
        extra.setTagged(true);
        cl = ClauseCreator::create(solver, clLits, {}, extra).local;
        REQUIRE(cl->size() == 2);
        REQUIRE((solver.isTrue(b) && solver.reason(b).constraint() == cl));
        solver.backtrack() && solver.propagate();
        REQUIRE((solver.isTrue(b) && solver.reason(b).constraint() == cl));
        cl->strengthen(solver, ~a);
        solver.backtrack();
        REQUIRE(solver.isTrue(b));
        LitVec out;
        solver.reason(b, out);
        REQUIRE((out.size() == 1 && out[0] == lit_true));
        solver.clearAssumptions();
        REQUIRE(solver.isTrue(b));
    }

    SECTION("testStrengthenContracted") {
        ctx.endInit();
        LitVec lits;
        lits.push_back(x1);
        for (uint32_t i : irange(2u, 13u)) {
            solver.assume(negLit(i));
            lits.push_back(posLit(i));
        }
        solver.strategies().compress = 4;
        cl                           = ClauseCreator::create(solver, lits, {}, ConstraintType::conflict).local;
        uint32_t si                  = cl->size();
        cl->strengthen(solver, posLit(12));
        solver.undoUntil(solver.decisionLevel() - 1);
        REQUIRE((solver.value(posLit(12).var()) == value_free && si == cl->size()));
        solver.undoUntil(solver.level(posLit(9).var()) - 1);

        REQUIRE(si + 1 <= cl->size());
        si = cl->size();

        cl->strengthen(solver, posLit(2));
        cl->strengthen(solver, posLit(6));
        REQUIRE(si == cl->size());
        cl->strengthen(solver, posLit(9));

        cl->strengthen(solver, posLit(8));
        cl->strengthen(solver, posLit(5));
        cl->strengthen(solver, posLit(4));
        cl->strengthen(solver, posLit(3));

        REQUIRE_FALSE(cl->strengthen(solver, posLit(7), false).removeClause);
        REQUIRE(3u == cl->size());
        REQUIRE(cl->strengthen(solver, posLit(11)).removeClause);
        REQUIRE(uint32_t(sizeof(Clause) + (9 * sizeof(Literal))) == ((Clause*) cl)->computeAllocSize());
    }
    SECTION("testStrengthen") {
        ctx.endInit();
        LitVec clause;
        clause.push_back(x1);
        for (uint32_t i : irange(2u, 7u)) {
            solver.assume(negLit(8 - i)) && solver.propagate();
            clause.push_back(posLit(i));
        }
        SECTION("test bug") {
            cl = Clause::newContractedClause(solver, ClauseRep::create(clause, ClauseInfo(ConstraintType::conflict)), 5,
                                             true);
            solver.addLearnt(cl, 5);
            uint32_t si = cl->size();
            REQUIRE(si == 5);
            cl->strengthen(solver, posLit(4));
            LitVec clause2;
            cl->toLits(clause2);
            REQUIRE(clause2.size() == 5);
            for (auto lit : clause) { REQUIRE((contains(clause2, lit) || lit == posLit(4))); }
        }
        SECTION("test no extend") {
            ClauseRep x = ClauseRep::create(clause, ClauseInfo(ConstraintType::conflict));
            cl          = Clause::newContractedClause(solver, x, 4, false);
            solver.addLearnt(cl, 4);
            REQUIRE(cl->size() == 4);
            cl->strengthen(solver, posLit(2));
            REQUIRE(cl->size() == 4);
            solver.undoUntil(0);
            REQUIRE(cl->size() == 4);
        }
    }
    SECTION("testStrengthenLocked") {
        auto a = ctx.addVar(VarType::atom);
        auto b = ctx.addVar(VarType::atom);
        auto c = ctx.addVar(VarType::atom);
        ctx.startAddConstraints();
        ctx.endInit();
        Literal tag = posLit(solver.pushTagVar(true));
        solver.assume(posLit(a)) && solver.propagate();
        solver.assume(posLit(b)) && solver.propagate();
        ClauseCreator cc(&solver);
        cc.start(ConstraintType::conflict).add(negLit(a)).add(negLit(b)).add(negLit(c)).add(~tag);
        ClauseHead* clause = cc.end().local;
        REQUIRE(clause->locked(solver));
        REQUIRE_FALSE(clause->strengthen(solver, ~tag).removeClause);
        REQUIRE(clause->locked(solver));
        LitVec r;
        solver.reason(negLit(c), r);
        REQUIRE(r.size() == 2);
        REQUIRE(contains(r, posLit(a)));
        REQUIRE(contains(r, posLit(b)));
    }

    SECTION("testStrengthenLockedEarly") {
        Literal b = posLit(ctx.addVar(VarType::atom));
        Literal c = posLit(ctx.addVar(VarType::atom));
        Literal d = posLit(ctx.addVar(VarType::atom));
        Literal x = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        ctx.endInit();
        Literal a = posLit(solver.pushTagVar(true));
        solver.assume(b) && solver.propagate();
        solver.force(c, nullptr) && solver.propagate();
        solver.assume(x) && solver.propagate();
        solver.setBacktrackLevel(solver.decisionLevel());

        ClauseCreator cc(&solver);
        cc.start(ConstraintType::conflict).add(~a).add(~b).add(~c).add(d);
        ClauseHead* clause = cc.end().local;
        REQUIRE(clause->locked(solver));
        bool remove = clause->strengthen(solver, ~a).removeClause;
        solver.backtrack();
        REQUIRE(solver.isTrue(d));
        REQUIRE(
            (not remove || solver.reason(d).type() != Antecedent::generic || solver.reason(d).constraint() != clause));
    }

    SECTION("testSimplifyTagged") {
        auto a = ctx.addVar(VarType::atom);
        auto b = ctx.addVar(VarType::atom);
        auto c = ctx.addVar(VarType::atom);
        ctx.startAddConstraints();
        ctx.endInit();
        Literal       tag = posLit(solver.pushTagVar(true));
        ClauseCreator cc(&solver);
        // ~a ~b ~c ~tag
        cc.start(ConstraintType::conflict).add(negLit(a)).add(negLit(b)).add(negLit(c)).add(~tag);
        ClauseHead* clause = cc.end().local;

        solver.force(posLit(c));
        REQUIRE_FALSE(clause->strengthen(solver, negLit(c)).removeClause);
    }

    SECTION("testClauseSatisfied") {
        ConstraintType t = ConstraintType::conflict;
        TypeSet        ts;
        REQUIRE_FALSE(ts.contains(ConstraintType::conflict));
        ts.add(t);
        REQUIRE(ts.contains(ConstraintType::conflict));
        solver.addLearnt(cl = createClause(solver, makeLits(clLits, 2, 2), t), 4);
        LitVec free;
        REQUIRE(uint32_t(t) == cl->isOpen(solver, ts, free));
        REQUIRE(LitVec::size_type(4) == free.size());

        solver.assume(clLits[2]);
        solver.propagate();
        free.clear();
        REQUIRE(0u == cl->isOpen(solver, ts, free));
        solver.undoUntil(0);
        solver.assume(~clLits[1]);
        solver.assume(~clLits[2]);
        solver.propagate();
        free.clear();
        REQUIRE(uint32_t(t) == cl->isOpen(solver, ts, free));
        REQUIRE(LitVec::size_type(2) == free.size());
        ts = TypeSet{ConstraintType::loop};
        REQUIRE(0u == cl->isOpen(solver, ts, free));
    }

    SECTION("testContraction") {
        ctx.endInit();
        LitVec lits(1, x1);
        for (uint32_t i : irange(2u, 13u)) {
            solver.assume(negLit(i));
            lits.push_back(posLit(i));
        }
        solver.strategies().compress = 6;
        cl                           = ClauseCreator::create(solver, lits, {}, ConstraintType::conflict).local;
        uint32_t s1                  = cl->size();
        REQUIRE(s1 < lits.size());
        LitVec r;
        solver.reason(x1, r);
        REQUIRE(r.size() == lits.size() - 1);

        solver.undoUntil(0);
        REQUIRE(cl->size() == lits.size());
    }

    SECTION("testNewContractedClause") {
        ctx.endInit();
        // head
        clLits.push_back(x1);
        clLits.push_back(x2);
        clLits.push_back(x3);
        for (uint32_t i : irange(4u, 13u)) {
            solver.assume(negLit(i));
            // (false) tail
            clLits.push_back(posLit(i));
        }
        ClauseRep x = ClauseRep::create(clLits, ClauseInfo(ConstraintType::conflict));
        cl          = Clause::newContractedClause(solver, x, 3, false);
        solver.addLearnt(cl, size32(clLits));
        REQUIRE(cl->size() < clLits.size());

        solver.assume(~x1) && solver.propagate();
        solver.assume(~x3) && solver.propagate();
        REQUIRE(solver.isTrue(x2));
        LitVec r;
        solver.reason(x2, r);
        REQUIRE(r.size() == clLits.size() - 1);
    }
    SECTION("testBug") {
        solver.add(cl = createClause(solver, makeLits(clLits, 3, 3)));
        solver.assume(~clLits[1]);
        solver.propagate();
        solver.assume(~clLits[2]);
        solver.propagate();
        solver.assume(~clLits[3]);
        solver.propagate();
        solver.assume(~clLits[0]);
        solver.propagate();
        uint32_t exp = solver.numAssignedVars();
        solver.undoUntil(0);
        solver.assume(~clLits[1]);
        solver.propagate();
        solver.assume(~clLits[2]);
        solver.propagate();
        solver.assume(~clLits[3]);
        solver.propagate();
        solver.assume(~clLits[4]);
        solver.propagate();

        REQUIRE(exp == solver.numAssignedVars());
        REQUIRE(solver.hasWatch(~clLits[0], cl));
        REQUIRE(solver.hasWatch(~clLits[5], cl));
    }

    SECTION("testClone") {
        Solver& solver2 = ctx.pushSolver();
        ctx.endInit(true);
        cl           = createClause(solver, makeLits(clLits, 3, 3));
        auto*  clone = cl->cloneAttach(solver2)->clause();
        LitVec lits;
        clone->toLits(lits);
        REQUIRE(lits == clLits);
        REQUIRE(countWatches(solver2, clone, lits) == 2);
        clone->destroy(&solver2, true);

        solver.force(~clLits[0], nullptr);
        solver.force(~clLits[2], nullptr);
        solver.propagate();
        cl->simplify(solver);
        clone = cl->cloneAttach(solver2)->clause();
        lits.clear();
        clone->toLits(lits);
        REQUIRE(lits.size() == 4);
        REQUIRE(countWatches(solver2, clone, lits) == 2);
        clone->destroy(&solver2, true);
        cl->destroy(&solver, true);
    }
}
TEST_CASE("Shuffle", "[constraint][core]") {
    LitVec lits;
    Rng    rng;
    makeLits(lits, 2, 3);
    std::set<LitVec> perms;
    std::ranges::sort(lits);
    while (std::ranges::next_permutation(lits).found) { perms.insert(lits); }
    REQUIRE(std::ranges::is_sorted(lits));
    auto copy  = lits;
    auto tries = 0;
    while (not perms.empty() && tries++ < 700) {
        rng.shuffle(copy.begin(), copy.end());
        REQUIRE(std::is_permutation(copy.begin(), copy.end(), lits.begin()));
        perms.erase(copy);
    }
    REQUIRE(perms.empty());
}
TEST_CASE("Propagate random clause", "[constraint][core]") {
    LitVec lits, r;
    Rng    rng;
    for (uint32_t size : irange(2u, 12u)) {
        for (uint32_t run : irange(4u)) {
            SharedContext ctx;
            Solver&       solver = *ctx.master();
            for ([[maybe_unused]] auto _ : irange(12u)) { ctx.addVar(VarType::atom); }
            ctx.startAddConstraints(1);
            auto pos = rng(size) + 1;
            makeLits(lits, pos, size - pos);
            ClauseHead* clause = nullptr;
            if (run & 1) {
                clause = createClause(solver, lits);
            }
            else {
                clause = createShared(solver, lits);
            }
            solver.add(clause);
            rng.shuffle(lits.begin(), lits.end());
            REQUIRE(value_free == solver.value(lits.back().var()));
            for (auto i : irange(size32(lits) - 1)) {
                REQUIRE(value_free == solver.value(lits[i].var()));
                solver.force(~lits[i], nullptr);
                solver.propagate();
            }
            REQUIRE(solver.isTrue(lits.back()));
            Antecedent reason = solver.reason(lits.back());
            REQUIRE(reason == clause);
            r.clear();
            clause->reason(solver, lits.back(), r);
            for (auto i : irange(size32(lits) - 1)) {
                auto it = std::ranges::find(r, ~lits[i]);
                REQUIRE(it != r.end());
                r.erase(it);
            }
            while (not r.empty() && isSentinel(r.back())) { r.pop_back(); }
            REQUIRE(r.empty());
        }
    }
}

TEST_CASE("Loop formula", "[constraint][asp]") {
    SharedContext ctx;
    Literal       a1     = posLit(ctx.addVar(VarType::atom));
    Literal       a2     = posLit(ctx.addVar(VarType::atom));
    Literal       a3     = posLit(ctx.addVar(VarType::atom));
    Literal       b1     = posLit(ctx.addVar(VarType::body));
    Literal       b2     = posLit(ctx.addVar(VarType::body));
    Literal       b3     = posLit(ctx.addVar(VarType::body));
    Solver&       solver = ctx.startAddConstraints();
    SECTION("with init") {
        ctx.endInit();
        solver.assume(~b1);
        solver.assume(~b2);
        solver.assume(~b3);
        solver.propagate();
        Literal      lits[] = {~a1, b3, b2, b1, ~a1, ~a2, ~a3};
        LoopFormula* lf     = LoopFormula::newLoopFormula(solver, ClauseRep::prepared({lits, 4}), LitView(lits + 4, 3));
        solver.addLearnt(lf, lf->size());
        solver.force(~a1, lf);
        solver.force(~a2, lf);
        solver.force(~a3, lf);
        solver.propagate();

        SECTION("has initial watches") {
            REQUIRE(solver.hasWatch(a1, lf));
            REQUIRE(solver.hasWatch(a2, lf));
            REQUIRE(solver.hasWatch(a3, lf));
            REQUIRE(solver.hasWatch(~b3, lf));
        }
        SECTION("simplifyLFIfOneBodyTrue") {
            solver.undoUntil(0);
            solver.force(b2, nullptr);
            solver.propagate();

            REQUIRE(lf->simplify(solver));
            REQUIRE_FALSE(solver.hasWatch(a1, lf));
            REQUIRE_FALSE(solver.hasWatch(~b3, lf));
        }
        SECTION("simplifyLFIfAllAtomsFalse") {
            solver.undoUntil(0);
            solver.force(~a1, nullptr);
            solver.force(~a2, nullptr);
            solver.propagate();
            REQUIRE_FALSE(lf->simplify(solver));
            solver.assume(a3);
            solver.propagate();
            solver.backtrack();
            solver.propagate();
            REQUIRE(lf->simplify(solver));
            REQUIRE_FALSE(solver.hasWatch(~b3, lf));
            REQUIRE_FALSE(solver.hasWatch(a1, lf));
            REQUIRE_FALSE(solver.hasWatch(a2, lf));
            REQUIRE_FALSE(solver.hasWatch(a3, lf));
            solver.reduceLearnts(1.0f);
        }

        SECTION("simplifyLFRemovesFalseBodies") {
            solver.undoUntil(0);

            solver.force(~b1, nullptr);
            solver.propagate();
            REQUIRE(lf->simplify(solver));
            REQUIRE(3u == solver.sharedContext()->numLearntShort());
        }

        SECTION("simplifyLFRemovesFalseAtoms") {
            solver.undoUntil(0);
            solver.force(~a1, nullptr);
            solver.propagate();
            REQUIRE_FALSE(lf->simplify(solver));
            REQUIRE(5 == lf->size());

            solver.force(~a3, nullptr);
            solver.propagate();
            REQUIRE_FALSE(lf->simplify(solver));
            REQUIRE(4 == lf->size());

            solver.force(~a2, nullptr);
            solver.propagate();
            REQUIRE(lf->simplify(solver));
        }

        SECTION("simplifyLFRemovesTrueAtoms") {
            solver.undoUntil(0);
            solver.force(a1, nullptr);
            solver.propagate();
            REQUIRE(lf->simplify(solver));

            REQUIRE(1u == solver.sharedContext()->numLearntShort());
        }

        SECTION("loopFormulaPropagateBody") {
            solver.undoUntil(0);
            solver.assume(~b1);
            solver.propagate();
            solver.assume(~b3);
            solver.propagate();
            solver.assume(a3);
            solver.propagate();

            REQUIRE(true == solver.isTrue(b2));
            REQUIRE(Antecedent::generic == solver.reason(b2).type());
            LitVec r;
            solver.reason(b2, r);
            REQUIRE(LitVec::size_type(3) == r.size());
            REQUIRE(contains(r, a3));
            REQUIRE(contains(r, ~b3));
            REQUIRE(contains(r, ~b1));

            REQUIRE(lf->locked(solver));
        }

        SECTION("loopFormulaPropagateBody2") {
            solver.undoUntil(0);
            solver.assume(a1);
            solver.propagate();
            solver.undoUntil(0);

            solver.assume(~b1);
            solver.propagate();
            solver.assume(a2);
            solver.propagate();
            solver.assume(~b2);
            solver.propagate();

            REQUIRE(true == solver.isTrue(b3));

            REQUIRE(Antecedent::generic == solver.reason(b3).type());
            LitVec r;
            solver.reason(b3, r);
            REQUIRE(LitVec::size_type(3) == r.size());
            REQUIRE(contains(r, ~b1));
            REQUIRE(contains(r, ~b2));
            REQUIRE(contains(r, a2));

            REQUIRE(lf->locked(solver));
        }

        SECTION("loopFormulaPropagateAtoms") {
            solver.undoUntil(0);
            solver.assume(~b3);
            solver.propagate();
            solver.assume(~b1);
            solver.propagate();

            solver.assume(~a1);
            solver.propagate();

            solver.assume(~b2);
            solver.propagate();

            REQUIRE(true == solver.isTrue(~a1));
            REQUIRE(true == solver.isTrue(~a2));
            REQUIRE(true == solver.isTrue(~a3));

            REQUIRE(Antecedent::generic == solver.reason(~a2).type());
            LitVec r;
            solver.reason(~a2, r);
            REQUIRE(LitVec::size_type(3) == r.size());
            REQUIRE(contains(r, ~b1));
            REQUIRE(contains(r, ~b2));
            REQUIRE(contains(r, ~b3));

            REQUIRE(lf->locked(solver));
        }

        SECTION("loopFormulaPropagateAtoms2") {
            solver.undoUntil(0);
            solver.assume(a1);
            solver.force(a2, nullptr);
            solver.propagate();
            solver.undoUntil(0);

            solver.assume(~b3);
            solver.propagate();
            solver.assume(~b1);
            solver.propagate();
            solver.assume(~b2);
            solver.propagate();

            REQUIRE(true == solver.isTrue(~a1));
            REQUIRE(true == solver.isTrue(~a2));
            REQUIRE(true == solver.isTrue(~a3));

            REQUIRE(Antecedent::generic == solver.reason(~a1).type());
            LitVec r;
            solver.reason(~a1, r);
            REQUIRE(LitVec::size_type(3) == r.size());
            REQUIRE(contains(r, ~b1));
            REQUIRE(contains(r, ~b2));
            REQUIRE(contains(r, ~b3));

            REQUIRE(lf->locked(solver));
        }

        SECTION("loopFormulaBodyConflict") {
            solver.undoUntil(0);

            solver.assume(~b3);
            solver.propagate();
            solver.assume(~b2);
            solver.propagate();
            solver.force(a3, nullptr);
            solver.force(~b1, nullptr);

            REQUIRE(false == solver.propagate());
            const auto& r = solver.conflict();

            REQUIRE(4u == size32(r));
            REQUIRE(contains(r, a3));
            REQUIRE(contains(r, ~b3));
            REQUIRE(contains(r, ~b1));
            REQUIRE(contains(r, ~b2));
        }
        SECTION("loopFormulaAtomConflict") {
            solver.undoUntil(0);
            solver.assume(~b3);
            solver.propagate();
            solver.assume(~b1);
            solver.propagate();
            solver.force(~b2, nullptr);
            solver.force(a2, nullptr);
            REQUIRE(false == solver.propagate());

            const auto& cfl = solver.conflict();

            REQUIRE(4u == size32(cfl));
            REQUIRE(contains(cfl, a2));
            REQUIRE(contains(cfl, ~b3));
            REQUIRE(contains(cfl, ~b1));
            REQUIRE(contains(cfl, ~b2));

            REQUIRE(true == solver.isTrue(~a1));
            LitVec r;
            solver.reason(~a1, r);
            REQUIRE(3u == size32(r));
            REQUIRE(contains(r, ~b3));
            REQUIRE(contains(r, ~b1));
            REQUIRE(contains(r, ~b2));
        }

        SECTION("loopFormulaDontChangeSat") {
            solver.undoUntil(0);
            REQUIRE((solver.assume(~b1) && solver.propagate()));
            REQUIRE((solver.assume(~b3) && solver.propagate()));
            REQUIRE((solver.assume(a2) && solver.propagate()));

            REQUIRE(solver.isTrue(b2));
            LitVec rold;
            solver.reason(b2, rold);

            REQUIRE((solver.assume(a1) && solver.propagate()));
            REQUIRE(solver.isTrue(b2));
            LitVec rnew;
            solver.reason(b2, rnew);
            REQUIRE(rold == rnew);
        }

        SECTION("loopFormulaSatisfied") {
            ConstraintType t = ConstraintType::loop;
            TypeSet        ts, other;
            ts.add(t);
            other.add(ConstraintType::conflict);
            LitVec free;
            REQUIRE(0u == lf->isOpen(solver, ts, free));
            solver.undoUntil(0);
            free.clear();
            REQUIRE(uint32_t(lf->type()) == lf->isOpen(solver, ts, free));
            REQUIRE(LitVec::size_type(6) == free.size());
            REQUIRE(0u == lf->isOpen(solver, other, free));
            solver.assume(a1);
            solver.assume(~b2);
            solver.propagate();
            free.clear();
            REQUIRE(uint32_t(lf->type()) == lf->isOpen(solver, ts, free));
            REQUIRE(LitVec::size_type(4) == free.size());
            solver.assume(~b1);
            solver.propagate();
            REQUIRE(0u == lf->isOpen(solver, ts, free));
        }

        SECTION("testLoopFormulaPropTrueAtomInSatClause") {
            solver.undoUntil(0);
            solver.assume(~a1);
            solver.propagate();

            solver.assume(a2);
            solver.force(~b3, nullptr);
            solver.force(~b2, nullptr);
            solver.propagate();

            REQUIRE(true == solver.isTrue(b1));
        }
    }
    SECTION("testLoopFormulaBugEq") {
        ctx.endInit();
        Literal body1 = b1;
        Literal body2 = b2;
        Literal body3 = ~b3; // assume body3 is equivalent to some literal ~xy
        solver.assume(~body1);
        solver.assume(~body2);
        solver.assume(~body3);
        solver.propagate();
        Literal lits[4] = {~a1, body3, body2, body1};

        LoopFormula* lf = LoopFormula::newLoopFormula(solver, ClauseRep::prepared({lits, 4}), lits, true);
        solver.addLearnt(lf, lf->size());
        solver.force(~a1, lf);
        solver.propagate();
        solver.undoUntil(solver.decisionLevel() - 2);
        REQUIRE((solver.assume(~body3) && solver.propagate()));
        REQUIRE((solver.assume(a1) && solver.propagate()));
        REQUIRE(solver.isTrue(body2));
    }
}

TEST_CASE("Shared clause", "[core][constraint]") {
    static_assert(not std::is_move_constructible_v<SharedLiterals>);
    static_assert(not std::is_copy_constructible_v<SharedLiterals>);
    using ClauseInfo = ConstraintInfo;
    SharedContext ctx;
    LitVec        clLits;
    for ([[maybe_unused]] auto _ : irange(14)) { ctx.addVar(VarType::atom); }
    ctx.startAddConstraints(10);
    Solver& solver = *ctx.master();
    SECTION("testClauseCtorAddsWatches") {
        makeLits(clLits, 2, 2);
        ClauseHead* sharedCl = createShared(solver, clLits, ClauseInfo());
        ctx.add(sharedCl);
        REQUIRE(2 == countWatches(solver, sharedCl, clLits));
    }

    SECTION("testPropSharedClauseConflict") {
        makeLits(clLits, 2, 2);
        ClauseHead* cl = createShared(solver, clLits, ClauseInfo());
        solver.add(cl);
        solver.assume(~clLits[0]);
        solver.propagate();
        solver.assume(~clLits.back());
        solver.propagate();
        solver.assume(~clLits[1]);
        solver.propagate();

        REQUIRE(solver.isTrue(clLits[2]));
        REQUIRE(cl->locked(solver));
        Antecedent reason = solver.reason(clLits[2]);
        REQUIRE(reason == cl);

        LitVec r;
        reason.reason(solver, clLits[2], r);
        REQUIRE(contains(r, ~clLits[0]));
        REQUIRE(contains(r, ~clLits[1]));
        REQUIRE(contains(r, ~clLits[3]));
    }

    SECTION("testPropAlreadySatisfied") {
        ClauseHead* c1 = createShared(solver, makeLits(clLits, 2, 2), ClauseInfo());
        ctx.add(c1);

        // satisfy the clauses...
        ctx.addUnary(clLits[3]);
        solver.propagate();

        // ...make all but one literal false
        ctx.addUnary(~clLits[0]);
        ctx.addUnary(~clLits[1]);
        solver.propagate();

        // ...and assert that the last literal is still unassigned
        REQUIRE(value_free == solver.value(clLits[2].var()));
    }

    SECTION("testReasonBumpsActivityIfLearnt") {
        ctx.endInit();
        ClauseInfo  e(ConstraintType::conflict);
        ClauseHead* cl = createShared(solver, makeLits(clLits, 4, 0), e);
        solver.addLearnt(cl, size32(clLits));

        solver.assume(~clLits[0]);
        solver.propagate();
        solver.assume(~clLits[1]);
        solver.propagate();
        uint32_t a = cl->activity().activity();
        solver.assume(~clLits[2]);
        solver.force(~clLits[3], Antecedent(nullptr));
        REQUIRE_FALSE(solver.propagate());
        REQUIRE(a + 1 == cl->activity().activity());
    }

    SECTION("testSimplifySAT") {
        ClauseHead* c1 = createShared(solver, makeLits(clLits, 3, 2), ClauseInfo());
        ctx.add(c1);

        ctx.addUnary(~clLits[4]);
        ctx.addUnary(clLits[3]);
        solver.propagate();

        REQUIRE(c1->simplify(*ctx.master(), false));
    }

    SECTION("testSimplifyUnique") {
        ClauseHead* cl = createShared(solver, makeLits(clLits, 3, 3), ClauseInfo());
        ctx.add(cl);

        ctx.addUnary(~clLits[2]);
        ctx.addUnary(~clLits[3]);
        solver.propagate();

        REQUIRE_FALSE(cl->simplify(*ctx.master(), false));
        REQUIRE(4 == cl->size());
        REQUIRE(2 == countWatches(*ctx.master(), cl, clLits));
    }

    SECTION("testSimplifyShared") {
        makeLits(clLits, 3, 3);
        SharedLiterals* sLits = SharedLiterals::newShareable(clLits, ConstraintType::conflict);
        REQUIRE((sLits->unique() && sLits->type() == ConstraintType::conflict && sLits->size() == 6));
        SharedLiterals* other = sLits->share();
        REQUIRE_FALSE(sLits->unique());

        ctx.addUnary(~clLits[2]);
        ctx.addUnary(~clLits[3]);
        solver.propagate();

        REQUIRE(4u == sLits->simplify(*ctx.master()));
        REQUIRE(6u == sLits->size());
        sLits->release();
        other->release();
    }

    SECTION("testCloneShared") {
        ClauseHead* cl      = createShared(solver, makeLits(clLits, 3, 2), ClauseInfo());
        Solver&     solver2 = ctx.pushSolver();
        ctx.endInit(true);
        auto*  clone = cl->cloneAttach(solver2)->clause();
        LitVec lits;
        clone->toLits(lits);
        REQUIRE(lits == clLits);
        REQUIRE(countWatches(solver2, clone, clLits) == 2);
        cl->destroy(ctx.master(), true);

        for (auto i : irange(size32(clLits) - 1)) {
            solver2.assume(~clLits[i]);
            solver2.propagate();
        }
        REQUIRE(solver2.isTrue(clLits.back()));
        REQUIRE(solver2.reason(clLits.back()) == clone);
        clone->destroy(&solver2, true);
    }
}
} // namespace Clasp::Test
