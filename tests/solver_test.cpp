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
#include <clasp/solver.h>

#include <clasp/clause.h>
#include <clasp/statistics.h>
#include <clasp/weight_constraint.h>
#if CLASP_HAS_THREADS
#include <clasp/mt/parallel_solve.h>
#endif

#include <potassco/error.h>

#include <catch2/catch_test_macros.hpp>

#include <set>

namespace Clasp::Test {
using namespace Clasp::mt;
namespace {
struct TestingConstraint : Constraint {
    explicit TestingConstraint(bool* del = nullptr, ConstraintType t = ConstraintType::static_) : ct(t), deleted(del) {}
    Constraint* cloneAttach(Solver&) override { return new TestingConstraint(nullptr, ct); }
    PropResult  propagate(Solver&, Literal, uint32_t&) override {
        ++propagates;
        return PropResult(not setConflict, keepWatch);
    }
    void undoLevel(Solver&) override { ++undos; }
    bool simplify(Solver&, bool) override { return sat; }
    void reason(Solver&, Literal, LitVec& out) override { out = ante; }
    void destroy(Solver* s, bool b) override {
        if (deleted) {
            *deleted = true;
        }
        if (s && b) {
            for (auto v : s->vars()) {
                s->removeWatch(posLit(v), this);
                s->removeWatch(negLit(v), this);
            }
            for (auto i : irange(s->decisionLevel())) { s->removeUndoWatch(i + 1, this); }
        }
        Constraint::destroy(s, b);
    }
    [[nodiscard]] bool           locked(const Solver&) const override { return false; }
    uint32_t                     isOpen(const Solver&, const TypeSet&, LitVec&) override { return 0; }
    static uint32_t              size() { return 10u; }
    [[nodiscard]] ConstraintType type() const override { return ct; }
    LitVec                       ante;
    ConstraintType               ct;
    int                          propagates{0};
    int                          undos{0};
    bool                         sat{false};
    bool                         keepWatch{true};
    bool                         setConflict{false};
    bool*                        deleted;
};
struct TestingPostProp : PostPropagator {
    explicit TestingPostProp(bool cfl, uint32_t p = priority_class_simple) : prio(p), conflict(cfl) {}
    bool propagateFixpoint(Solver& s, PostPropagator*) override {
        ++props;
        bool ok = not conflict;
        if (deleteOnProp) {
            s.removePost(this);
            this->destroy(nullptr, false);
        }
        return ok;
    }
    void destroy(Solver* s, bool detach) override {
        if (destroyed) {
            *destroyed = true;
        }
        PostPropagator::destroy(s, detach);
    }
    bool simplify(Solver&, bool) override {
        ++simps;
        return removeOnSimplify;
    }
    void reset() override { ++resets; }
    bool init(Solver&) override {
        ++inits;
        return true;
    }
    [[nodiscard]] uint32_t priority() const override { return prio; }

    static TestingPostProp* addTo(Solver& s, bool cfl, uint32_t p = priority_class_simple) {
        auto pp = std::make_unique<TestingPostProp>(cfl, p);
        auto r  = pp.get();
        s.addPost(pp.release());
        return r;
    }

    int      props{0};
    int      resets{0};
    int      inits{0};
    int      simps{0};
    uint32_t prio;
    bool     conflict;
    bool     deleteOnProp{false};
    bool     removeOnSimplify{false};
    bool*    destroyed{nullptr};
};
} // namespace

template <typename StoreType>
static void testReasonStore() {
    StoreType store;
    store.resize(1);
    Constraint* x = new TestingConstraint(nullptr, ConstraintType::conflict);
    POTASSCO_SCOPE_EXIT({ x->destroy(); });
    store[0] = x;
    store.setData(0, 22);
    REQUIRE(store[0] == x);
    REQUIRE(store.data(0) == 22);
    Literal p(10, false), q(22, false);
    store[0]     = Antecedent(p, q);
    uint32_t old = store.data(0);
    store.setData(0, 74);
    REQUIRE(store.data(0) == 74);
    store.setData(0, old);
    REQUIRE((store[0].firstLiteral() == p && store[0].secondLiteral() == q));

    using ReasonWithData = typename StoreType::value_type;
    ReasonWithData rwd(x, 169);
    store[0] = rwd.ante();
    if (rwd.data() != UINT32_MAX) {
        store.setData(0, rwd.data());
    }
    REQUIRE(store[0] == x);
    REQUIRE(store.data(0) == 169);

    rwd      = ReasonWithData(p, UINT32_MAX);
    store[0] = rwd.ante();
    if (rwd.data() != UINT32_MAX) {
        store.setData(0, rwd.data());
    }
    REQUIRE(store[0].firstLiteral() == p);
}
static void testDefaults(SharedContext& ctx) {
    const SolverParams& x = ctx.configuration()->solver(0);
    const Solver&       s = *ctx.master();
    REQUIRE(ctx.stats().vars.frozen == 0);
    REQUIRE(x.heuId == 0);
    REQUIRE(x.ccMinRec == 0);
    REQUIRE(x.ccMinAntes == SolverStrategies::all_antes);
    REQUIRE(x.search == SolverStrategies::use_learning);
    REQUIRE(x.compress == 0);
    REQUIRE(x.initWatches == SolverStrategies::watch_rand);

    REQUIRE(x.heuristic.score == HeuParams::score_auto);
    REQUIRE(x.heuristic.other == HeuParams::other_auto);
    REQUIRE(x.heuristic.moms == 1);

    REQUIRE(0u == s.numVars());
    REQUIRE(0u == s.numAssignedVars());
    REQUIRE(0u == s.numConstraints());
    REQUIRE(0u == s.numLearntConstraints());
    REQUIRE(0u == s.decisionLevel());
    REQUIRE(0u == s.queueSize());
    ctx.setFrozen(0, true);
    REQUIRE(ctx.stats().vars.frozen == 0);
}
TEST_CASE("Solver types", "[core]") {
    SECTION("test thread safe int") {
        ThreadSafe<int>        a;
        ThreadSafe<int, false> b;
        CHECK(a == 0);
        CHECK(b == 0);
        CHECK(ThreadSafe<int>{32} == 32);
        CHECK(ThreadSafe<int, false>{32} == 32);

        CHECK(a.add(12) == 12);
        CHECK(b.add(a) == 12);
        CHECK(a.add(b) == 24);
        CHECK(b.add(a) == 36);

        CHECK(a.sub(4) == 20);
        CHECK(b.sub(b) == 0);

        a.store(17);
        b.store(83);
        CHECK(a.exchange(12) == 17);
        CHECK(b.exchange(99) == 83);

        int expected = 12;
        CHECK(a.compare_exchange_weak(expected, 32));
        CHECK_FALSE(a.compare_exchange_strong(expected, 99));
        CHECK(expected == 32);
        CHECK(a.compare_exchange_strong(expected, 64));
        CHECK(expected == 32);
        CHECK(a.load(memory_order_relaxed) == 64);

        CHECK_FALSE(b.compare_exchange_strong(expected, 103));
        CHECK(expected == 99);
        CHECK(b.compare_exchange_weak(expected, 192));
        CHECK(expected == 99);
        CHECK(b.load(memory_order_relaxed) == 192);
    }
    SECTION("test refcount") {
        RefCount count(4);
        CHECK(count == 4);
        CHECK_FALSE(count.release(2));
        CHECK(count == 2);
        count.add();
        CHECK(count == 3);
        CHECK_FALSE(count.release());
        CHECK(count == 2);
        CHECK(count.release_fetch() == 1);
        CHECK(count.release());
    }
    SECTION("test sig atomic") {
        SigAtomic sig;
        CHECK(sig.value() == 0);
        CHECK(sig == 0);
        CHECK(sig.exchange(12) == 0);
        CHECK(sig == 12);
        CHECK_FALSE(sig.set_if_unset(1));
        CHECK(sig == 12);
        CHECK(sig.exchange(0) == 12);
        CHECK(sig.set_if_unset(1));
        CHECK(sig == 1);
    }
    SECTION("test watch list") {
        WatchList wl;
        static_assert(WatchList::inline_raw_cap == 0);
        auto* dummy1 = reinterpret_cast<ClauseHead*>(0x01);
        auto* dummy2 = reinterpret_cast<ClauseHead*>(0x02);
        CHECK(wl.empty());
        CHECK(wl.left_view().empty());
        CHECK(wl.right_view().empty());

        wl.push_left(ClauseWatch(dummy1));
        CHECK_FALSE(wl.empty());
        CHECK(wl.left_size() == 1);
        CHECK(wl.right_size() == 0);
        CHECK(wl.left_view().size() == 1);
        CHECK(wl.right_view().empty());
        CHECK(wl.left(0).head == dummy1);

        wl.push_right(GenericWatch(nullptr, 0));
        CHECK(wl.right_size() == 1);
        CHECK(wl.right_view().size() == 1);
        CHECK(wl.right_view()[0].data == 0);

        wl.push_right(GenericWatch(nullptr, 1));
        CHECK(wl.right_size() == 2);
        CHECK(wl.right_view().size() == 2);
        CHECK(wl.right_view()[0].data == 0);
        CHECK(wl.right_view()[1].data == 1);
        CHECK(wl.left_size() == 1);

        wl.push_left(ClauseWatch(dummy2));
        CHECK(wl.left_size() == 2);
        CHECK(wl.left(1).head == dummy2);
        wl.push_right(GenericWatch(nullptr, 3));
        wl.push_right(GenericWatch(nullptr, 4));
        wl.push_right(GenericWatch(nullptr, 5));
        CHECK(wl.right_size() == 5);
        CHECK(wl.right_view().size() == 5);
        CHECK(wl.right_view()[3].data == 4);

        WatchList copy(wl);
        wl.pop_left();
        CHECK(wl.left_size() == 1);
        CHECK(wl.left(0).head == dummy1);
        CHECK(copy.left_size() == 2);
        WatchList move(std::move(copy));
        CHECK(copy.empty()); // NOLINT(*-use-after-move)
        CHECK(move.left_size() == 2);

        move.erase_left_unordered(move.left_begin());
        CHECK(move.left_size() == 1);
        CHECK(move.left(0).head == dummy2);

        releaseVec(move);
        CHECK(move.empty());
        CHECK(move.left_capacity() == 0);
        CHECK(move.right_capacity() == 0);
    }

    SECTION("test lr list") {
        using ListType = bk_lib::left_right_sequence<int, double, 56>;
        using BaseType = bk_lib::detail::left_right_rep<int, double>;
        static_assert(sizeof(ListType) == 56);
        static_assert(sizeof(BaseType) == (sizeof(void*) == 4 ? 16 : 24));
        static_assert(ListType::inline_raw_cap == (sizeof(void*) == 4 ? 40 : 32));
        constexpr auto cap = ListType::inline_raw_cap;
        ListType       imp;
        CHECK(imp.empty());
        CHECK(imp.left_capacity() == cap / sizeof(int));
        CHECK(imp.right_capacity() == cap / sizeof(double));

        if constexpr (sizeof(void*) == 8) {
            imp.push_left(1);
            imp.push_left(2);
            imp.push_right(3.0);
            imp.push_right(4.0);
            imp.push_right(5.0);
            // grow
            imp.push_left(6);
            constexpr auto check = [](const ListType& x, std::span<int> left, std::span<double> right) {
                REQUIRE(x.left_size() == left.size());
                REQUIRE(x.right_size() == right.size());
                CHECK(std::ranges::equal(x.left_view(), left));
                CHECK(std::ranges::equal(x.right_view(), right));
            };
            int    expLeft[]  = {1, 2, 6};
            double expRight[] = {3.0, 4.0, 5.0};
            check(imp, expLeft, expRight);

            ListType copy(imp);
            check(copy, expLeft, expRight);

            ListType move(std::move(copy));
            check(move, expLeft, expRight);
            REQUIRE(copy.empty()); // NOLINT(*-use-after-move)
            copy = imp;
            check(copy, expLeft, expRight);

            move.pop_right();
            move.try_shrink();
            check(move, expLeft, std::span(expRight).subspan(0, 2));

            move = std::move(copy);
            REQUIRE(copy.empty()); // NOLINT(*-use-after-move)
            check(move, expLeft, expRight);
        }
    }
    SECTION("test reason store") {
        if constexpr (sizeof(void*) == sizeof(uint32_t)) {
            testReasonStore<ReasonStore32>();
        }
        testReasonStore<ReasonStore64>();
    }

    SECTION("test value set") {
        ValueSet vs;
        REQUIRE(vs.empty());
        vs.set(ValueSet::pref_value, value_true);
        REQUIRE_FALSE(vs.empty());
        REQUIRE(vs.has(ValueSet::pref_value));
        REQUIRE_FALSE(vs.sign());
        vs.set(ValueSet::saved_value, value_false);
        REQUIRE(vs.has(ValueSet::saved_value));
        REQUIRE(vs.sign());

        vs.set(ValueSet::user_value, value_true);
        REQUIRE(vs.has(ValueSet::user_value));
        REQUIRE_FALSE(vs.sign());

        vs.set(ValueSet::user_value, value_free);
        REQUIRE_FALSE(vs.has(ValueSet::user_value));
        REQUIRE(vs.sign());
    }
    SECTION("test var true is sentinel") {
        Literal p = lit_true;
        REQUIRE(isSentinel(p));
        REQUIRE(isSentinel(~p));
    }
    SECTION("Constraint Score") {
        auto sc = ConstraintScore();
        REQUIRE_FALSE(sc.hasLbd());
        REQUIRE_FALSE(sc.bumped());
        REQUIRE(sc.lbd() == lbd_max);
        REQUIRE(sc.activity() == 0);

        sc.reset(100u, 4u);
        REQUIRE(sc.hasLbd());
        REQUIRE_FALSE(sc.bumped());
        REQUIRE(sc.lbd() == 4u);
        REQUIRE(sc.activity() == 100u);

        sc.bumpActivity();
        REQUIRE_FALSE(sc.bumped());
        REQUIRE(sc.activity() == 101u);
        REQUIRE(sc.lbd() == 4u);
        sc.reduce();
        REQUIRE_FALSE(sc.bumped());
        REQUIRE(sc.activity() == 50u);

        sc.bumpLbd(5u);
        REQUIRE_FALSE(sc.bumped());
        REQUIRE(sc.lbd() == 4u);
        REQUIRE(sc.activity() == 50u);

        sc.bumpLbd(3u);
        REQUIRE(sc.bumped());
        REQUIRE(sc.lbd() == 3u);
        REQUIRE(sc.activity() == 50u);

        REQUIRE(ConstraintScore::bits_used == 28);
        Potassco::store_set_bit(sc.rep, 28); // set one of the unused bits
        auto sc2 = ConstraintScore();
        sc2.assign(sc);
        REQUIRE_FALSE(Potassco::test_bit(sc2.rep, 28)); // must not copy unused bits
        REQUIRE(sc2.bumped());
        sc2.clearBumped();
        REQUIRE_FALSE(sc2.bumped());

        sc.reduce();
        REQUIRE_FALSE(sc.bumped());
        REQUIRE(sc.lbd() == 3u);
        REQUIRE(sc.activity() == 25u);

        sc.assign(ConstraintScore(100, 5)); // must not touch unused bits
        REQUIRE(sc.activity() == 100u);
        REQUIRE(sc.lbd() == 5u);
        REQUIRE(Potassco::test_bit(sc.rep, 28));
    }
    SECTION("Constraint Info") {
        ConstraintInfo s;
        ConstraintInfo c(ConstraintType::conflict);
        ConstraintInfo l(ConstraintType::loop);
        ConstraintInfo o(ConstraintType::other);
        REQUIRE(s.type() == ConstraintType::static_);
        REQUIRE(c.type() == ConstraintType::conflict);
        REQUIRE(l.type() == ConstraintType::loop);
        REQUIRE(o.type() == ConstraintType::other);
        auto noScore = ConstraintScore();
        REQUIRE_FALSE(noScore.hasLbd());
        REQUIRE(s.score() == noScore);
        REQUIRE(c.score() == noScore);
        REQUIRE(l.score() == noScore);
        REQUIRE(o.score() == noScore);

        s.setTagged(true);
        REQUIRE(s.tagged());
        s.setTagged(false);
        REQUIRE_FALSE(s.tagged());

        l.setAux(true);
        REQUIRE_FALSE(l.tagged());
        REQUIRE(l.aux());
        l.setAux(false);
        REQUIRE_FALSE(l.aux());

        REQUIRE_FALSE(c.score().hasLbd());
        c.setActivity(50);
        REQUIRE(c.activity() == 50u);
        REQUIRE(c.lbd() == lbd_max);

        o.setLbd(12);
        REQUIRE(o.activity() == 0);
        REQUIRE(o.lbd() == 12);
        REQUIRE(o.score().hasLbd());
        REQUIRE_FALSE(o.score().bumped());

        o.setScore(ConstraintScore(600, 2));
        o.setType(ConstraintType::static_);
        REQUIRE(o.type() == ConstraintType::static_);
        REQUIRE(o.score() == ConstraintScore(600, 2));
    }
    SECTION("test compare scores") {
        ReduceStrategy  rs;
        ConstraintScore a1 = ConstraintScore(100, 5), a2 = ConstraintScore(90, 3);
        REQUIRE(rs.compare(ReduceStrategy::score_act, a1, a2) > 0);
        REQUIRE(rs.compare(ReduceStrategy::score_lbd, a1, a2) < 0);
        REQUIRE(rs.compare(ReduceStrategy::score_both, a1, a2) > 0);

        REQUIRE((not a1.bumped() && not a2.bumped()));
        a1.bumpLbd(4);
        REQUIRE(rs.compare(ReduceStrategy::score_act, a1, a2) > 0);
        REQUIRE(rs.compare(ReduceStrategy::score_lbd, a1, a2) < 0);
        REQUIRE(rs.compare(ReduceStrategy::score_both, a1, a2) > 0);
        REQUIRE((a1.bumped() && a1.activity() == 100 && a1.lbd() == 4));
        a1.clearBumped();
        REQUIRE((not a1.bumped() && a1.activity() == 100 && a1.lbd() == 4));

        a1.bumpActivity();
        REQUIRE((not a1.bumped() && a1.activity() == 101 && a1.lbd() == 4));
        a1.reset(Clasp::act_max - 1, 2);
        a1.bumpActivity();
        REQUIRE((not a1.bumped() && a1.activity() == Clasp::act_max && a1.lbd() == 2));
        a1.bumpActivity();
        REQUIRE((not a1.bumped() && a1.activity() == Clasp::act_max && a1.lbd() == 2));
    }

    SECTION("Antecedent") {
        static_assert(
            [] {
                constexpr Antecedent a;
                return a.isNull() && a.type() == Antecedent::generic;
            }(),
            "must be true");
        static_assert(
            [] {
                constexpr Antecedent bin(posLit(4711));
                return not bin.isNull() && not bin.learnt() && bin.type() == Antecedent::binary &&
                       bin.firstLiteral() == posLit(4711);
            }(),
            "must be true");
        static_assert(
            [] {
                constexpr Antecedent tern(posLit(4711), negLit(3217));
                return not tern.isNull() && tern.type() == Antecedent::ternary && tern.firstLiteral() == posLit(4711) &&
                       tern.secondLiteral() == negLit(3217);
            }(),
            "must be true");
        Antecedent a(nullptr);
        REQUIRE_FALSE(a.learnt());
        Constraint* staticCon = new TestingConstraint();
        Constraint* learntCon = new TestingConstraint(nullptr, ConstraintType::conflict);
        POTASSCO_SCOPE_EXIT({
            staticCon->destroy();
            learntCon->destroy();
        });
        a = staticCon;
        REQUIRE_FALSE(a.learnt());
        a = learntCon;
        REQUIRE(a.learnt());
        a = Antecedent(posLit(4711), negLit(3217));
        REQUIRE_FALSE(a.learnt());
    }
}

TEST_CASE("Solver", "[core]") {
    SharedContext ctx;
    Solver&       s = *ctx.master();
    SECTION("testDefaults") { testDefaults(ctx); }

    SECTION("testSolverAlwaysContainsSentinelVar") {
        REQUIRE(value_true == s.value(sent_var));
        REQUIRE(s.isTrue(posLit(sent_var)));
        REQUIRE(s.isFalse(negLit(sent_var)));
        REQUIRE(s.seen(sent_var) == true);
    }
    SECTION("testSolverOwnsConstraints") {
        bool conDel  = false;
        bool lconDel = false;
        {
            SharedContext localCtx;
            Solver&       localS = localCtx.startAddConstraints();
            localCtx.add(new TestingConstraint(&conDel));
            localCtx.endInit();
            localS.addLearnt(new TestingConstraint(&lconDel, ConstraintType::conflict), TestingConstraint::size());
            REQUIRE(1u == localS.numConstraints());
            REQUIRE(1u == localS.numLearntConstraints());
        }
        REQUIRE(conDel);
        REQUIRE(lconDel);
    }

    SECTION("testAddVar") {
        auto v1 = ctx.addVar(VarType::atom);
        auto v2 = ctx.addVar(VarType::body);
        ctx.startAddConstraints();
        ctx.endInit();
        REQUIRE(2u == s.numVars());
        REQUIRE(0u == s.numAssignedVars());
        REQUIRE(2u == s.numFreeVars());
        REQUIRE(VarType::atom == ctx.varInfo(v1).type());
        REQUIRE(VarType::body == ctx.varInfo(v2).type());

        REQUIRE(true == ctx.varInfo(v1).preferredSign());
        REQUIRE(false == ctx.varInfo(v2).preferredSign());
    }

    SECTION("testEliminateVar") {
        auto v1 = ctx.addVar(VarType::atom);
        ctx.addVar(VarType::body);
        ctx.startAddConstraints();
        ctx.eliminate(v1);
        REQUIRE(uint32_t(2) == s.numVars());
        REQUIRE(uint32_t(1) == ctx.numEliminatedVars());
        REQUIRE(uint32_t(1) == s.numFreeVars());
        REQUIRE(uint32_t(0) == s.numAssignedVars());
        REQUIRE(ctx.eliminated(v1));
        // so v1 is ignored by heuristics!
        REQUIRE(s.value(v1) != value_free);

        // ignore subsequent calls
        ctx.eliminate(v1);
        REQUIRE(uint32_t(1) == ctx.numEliminatedVars());
        ctx.endInit();
    }

    SECTION("testMark") {
        auto v1 = ctx.addVar(VarType::atom, VarInfo::flag_nant | VarInfo::flag_input | VarInfo::flag_pos);
        auto v2 = ctx.addVar(VarType::body, VarInfo::flag_neg);
        auto v3 = ctx.addVar(VarType::hybrid);
        REQUIRE(ctx.varInfo(v1).type() == VarType::atom);
        REQUIRE(ctx.varInfo(v2).type() == VarType::body);
        REQUIRE(ctx.varInfo(v3).type() == VarType::hybrid);
        REQUIRE((not ctx.marked(posLit(v1)) && not ctx.marked(negLit(v1)))); // Mark flags should be ignored on add
        REQUIRE((not ctx.marked(posLit(v2)) && not ctx.marked(negLit(v2)))); // Mark flags should be ignored on add
        REQUIRE((not ctx.marked(posLit(v3)) && not ctx.marked(negLit(v3)))); // Mark flags should be ignored on add

        ctx.mark(posLit(v1));
        ctx.mark(negLit(v3));
        ctx.mark(posLit(v2));
        ctx.mark(negLit(v2));
        REQUIRE((ctx.marked(posLit(v1)) && not ctx.marked(negLit(v1))));
        REQUIRE((ctx.marked(posLit(v2)) && ctx.marked(negLit(v2))));
        REQUIRE((not ctx.marked(posLit(v3)) && ctx.marked(negLit(v3))));

        ctx.unmark(negLit(v1)); // noop
        REQUIRE((ctx.marked(posLit(v1)) && not ctx.marked(negLit(v1))));

        ctx.unmark(posLit(v1));
        ctx.unmark(negLit(v3));
        ctx.unmark(v2);
        REQUIRE((not ctx.marked(posLit(v1)) && not ctx.marked(negLit(v1))));
        REQUIRE((not ctx.marked(posLit(v2)) && not ctx.marked(negLit(v2))));
        REQUIRE((not ctx.marked(posLit(v3)) && not ctx.marked(negLit(v3))));
    }

    SECTION("testPreferredLitByType") {
        auto v1 = ctx.addVar(VarType::atom);
        auto v2 = ctx.addVar(VarType::body);
        auto v3 = ctx.addVar(VarType::hybrid);
        auto v4 = ctx.addVar(VarType::body, VarInfo::flag_eq);
        REQUIRE(true == ctx.varInfo(v1).preferredSign());
        REQUIRE(false == ctx.varInfo(v2).preferredSign());
        REQUIRE(true == ctx.varInfo(v3).preferredSign());
        REQUIRE(false == ctx.varInfo(v4).preferredSign());
    }

    SECTION("testInitSavedValue") {
        auto v1 = ctx.addVar(VarType::atom);
        auto v2 = ctx.addVar(VarType::body);
        ctx.startAddConstraints();
        ctx.endInit();
        REQUIRE(value_free == s.pref(v1).get(ValueSet::saved_value));
        REQUIRE(value_free == s.pref(v2).get(ValueSet::saved_value));

        s.setPref(v1, ValueSet::saved_value, value_true);
        s.setPref(v2, ValueSet::saved_value, value_false);

        REQUIRE(value_true == s.pref(v1).get(ValueSet::saved_value));
        REQUIRE(value_false == s.pref(v2).get(ValueSet::saved_value));
    }

    SECTION("testReset") {
        ctx.addVar(VarType::atom);
        ctx.addVar(VarType::body);
        ctx.startAddConstraints();
        s.add(new TestingConstraint(nullptr));
        ctx.endInit();
        s.addLearnt(new TestingConstraint(nullptr, ConstraintType::conflict), TestingConstraint::size());
        s.assume(posLit(1));
        ctx.reset();
        testDefaults(ctx);
        auto n = ctx.addVar(VarType::body);
        ctx.startAddConstraints();
        ctx.endInit();
        REQUIRE(VarType::body == ctx.varInfo(n).type());
    }

    SECTION("testForce") {
        auto v1 = ctx.addVar(VarType::atom);
        auto v2 = ctx.addVar(VarType::atom);
        ctx.startAddConstraints();
        ctx.endInit();
        REQUIRE(s.force(posLit(v1), nullptr));
        REQUIRE(s.force(negLit(v2), posLit(v1)));
        REQUIRE(s.isTrue(posLit(v1)));
        REQUIRE(s.isTrue(negLit(v2)));
        REQUIRE(s.reason(negLit(v2)).type() == Antecedent::binary);

        REQUIRE(2u == s.queueSize());
    }

    SECTION("testNoUpdateOnConsistentAssign") {
        auto v1 = ctx.addVar(VarType::atom);
        auto v2 = ctx.addVar(VarType::atom);
        ctx.startAddConstraints();
        s.force(posLit(v2), nullptr);
        s.force(posLit(v1), nullptr);
        uint32_t oldA = s.numAssignedVars();
        REQUIRE(s.force(posLit(v1), posLit(v2)));
        REQUIRE(oldA == s.numAssignedVars());
        REQUIRE(2u == s.queueSize());
    }

    SECTION("testAssume") {
        Literal p = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        REQUIRE(s.assume(p));
        REQUIRE(value_true == s.value(p.var()));
        REQUIRE(1u == s.decisionLevel());
        REQUIRE(1u == s.queueSize());
    }

    SECTION("testGetDecision") {
        Literal p = posLit(ctx.addVar(VarType::atom));
        Literal q = posLit(ctx.addVar(VarType::atom));
        Literal r = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        s.assume(p);
        s.assume(q);
        s.assume(~r);
        REQUIRE(p == s.decision(1));
        REQUIRE(q == s.decision(2));
        REQUIRE(~r == s.decision(3));
        REQUIRE(~r == s.decision(s.decisionLevel()));
    }
    SECTION("testAddWatch") {
        Literal p = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        TestingConstraint c;
        REQUIRE_FALSE(s.hasWatch(p, &c));
        s.addWatch(p, &c);
        REQUIRE(s.hasWatch(p, &c));
        REQUIRE(1u == s.numWatches(p));
    }

    SECTION("testRemoveWatch") {
        Literal p = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        TestingConstraint c;
        s.addWatch(p, &c);
        s.removeWatch(p, &c);
        REQUIRE_FALSE(s.hasWatch(p, &c));
    }

    SECTION("testNotifyWatch") {
        Literal           p = posLit(ctx.addVar(VarType::atom)), q = posLit(ctx.addVar(VarType::atom));
        TestingConstraint c;
        ctx.startAddConstraints();
        ctx.endInit();
        s.addWatch(p, &c);
        s.addWatch(q, &c);
        s.assume(p);
        s.propagate();
        REQUIRE(1 == c.propagates);
        s.assume(~q);
        s.propagate();
        REQUIRE(1 == c.propagates);
    }

    SECTION("testKeepWatchOnPropagate") {
        Literal p = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        ctx.endInit();
        TestingConstraint c;
        s.addWatch(p, &c);
        s.assume(p);
        s.propagate();
        REQUIRE(s.hasWatch(p, &c));
    }

    SECTION("testRemoveWatchOnPropagate") {
        Literal p = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        ctx.endInit();
        TestingConstraint c;
        c.keepWatch = false;
        s.addWatch(p, &c);
        s.assume(p);
        s.propagate();
        REQUIRE_FALSE(s.hasWatch(p, &c));
    }

    SECTION("testWatchOrder") {
        Literal p = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        ctx.endInit();
        TestingConstraint c1, c2, c3;
        c1.keepWatch   = false;
        c2.setConflict = true;
        s.addWatch(p, &c1);
        s.addWatch(p, &c2);
        s.addWatch(p, &c3);
        s.assume(p);
        REQUIRE_FALSE(s.propagate());
        REQUIRE_FALSE(s.hasWatch(p, &c1));
        REQUIRE(s.hasWatch(p, &c2));
        REQUIRE(s.hasWatch(p, &c3));
        REQUIRE(1 == c1.propagates);
        REQUIRE(1 == c2.propagates);
        REQUIRE(0 == c3.propagates);
    }

    SECTION("testUndoUntil") {
        Literal a = posLit(ctx.addVar(VarType::atom)), b = posLit(ctx.addVar(VarType::atom)),
                c = posLit(ctx.addVar(VarType::atom)), d = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        s.assume(a);
        s.force(~b, a);
        s.force(~c, a);
        s.force(d, a);
        REQUIRE(4u == s.queueSize());
        REQUIRE(4u == s.numAssignedVars());
        s.undoUntil(0u);
        REQUIRE(0u == s.numAssignedVars());
        for (auto i : irange(a.var(), d.var() + 1)) { REQUIRE(value_free == s.value(i)); }
    }

    SECTION("testUndoWatches") {
        Literal           a = posLit(ctx.addVar(VarType::atom)), b = posLit(ctx.addVar(VarType::atom));
        TestingConstraint c;
        ctx.startAddConstraints();
        ctx.endInit();
        s.assume(a);
        s.addUndoWatch(1, &c);
        s.assume(b);
        s.undoUntil(1);
        REQUIRE(0 == c.undos);
        s.undoUntil(0);
        REQUIRE(1 == c.undos);
    }
    SECTION("testLazyRemoveWatches") {
        Literal a = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        uint32_t             x = s.numWatches(a);
        Solver::ConstraintDB db;
        for (uint32_t i : irange(10u)) {
            db.push_back(new TestingConstraint);
            s.addWatch(a, db[i]);
        }
        ctx.endInit();
        s.assume(a);
        for (uint32_t i : irange(10u)) { s.addUndoWatch(1, db[i]); }
        s.destroyDB(db);
        s.undoUntil(0);
        REQUIRE(s.numWatches(a) == x);
    }

    SECTION("with binary clause") {
        LitVec bin;
        bin.push_back(posLit(ctx.addVar(VarType::atom)));
        bin.push_back(posLit(ctx.addVar(VarType::atom)));
        ctx.startAddConstraints();
        ctx.addBinary(bin[0], bin[1]);
        ctx.endInit();
        SECTION("test propagate") {
            for (auto i : irange(2u)) {
                s.assume(~bin[i]);
                REQUIRE(s.propagate());
                auto o = (i + 1) % 2;
                REQUIRE(s.isTrue(bin[o]));
                REQUIRE(Antecedent::binary == s.reason(bin[o]).type());
                LitVec r;
                s.reason(bin[o], r);
                REQUIRE(1u == size32(r));
                REQUIRE(~bin[i] == r[0]);
                s.undoUntil(0);
            }
            s.assume(~bin[0]);
            s.force(~bin[1], nullptr);
            REQUIRE_FALSE(s.propagate());
            const auto& r = s.conflict();
            REQUIRE(2u == size32(r));
            REQUIRE(contains(r, ~bin[0]));
            REQUIRE(contains(r, ~bin[1]));
        }
        SECTION("testRestartAfterUnitLitResolvedBug") {
            s.force(~bin[0], nullptr);
            s.undoUntil(0);
            s.propagate();
            REQUIRE(s.isTrue(~bin[0]));
            REQUIRE(s.isTrue(bin[1]));
        }
    }

    SECTION("testPropTernary") {
        LitVec tern;
        tern.push_back(posLit(ctx.addVar(VarType::atom)));
        tern.push_back(posLit(ctx.addVar(VarType::atom)));
        tern.push_back(posLit(ctx.addVar(VarType::atom)));
        ctx.startAddConstraints();
        ctx.addTernary(tern[0], tern[1], tern[2]);
        ctx.endInit();
        for (auto i : irange(3u)) {
            s.assume(~tern[i]);
            s.assume(~tern[(i + 1) % 3]);
            REQUIRE(s.propagate());
            auto o = (i + 2) % 3;
            REQUIRE(s.isTrue(tern[o]));
            REQUIRE(Antecedent::ternary == s.reason(tern[o]).type());
            LitVec r;
            s.reason(tern[o], r);
            REQUIRE(2u == size32(r));
            REQUIRE(contains(r, ~tern[i]));
            REQUIRE(contains(r, ~tern[(i + 1) % 3]));
            s.undoUntil(0);
        }
        s.assume(~tern[0]);
        s.force(~tern[1], nullptr);
        s.force(~tern[2], nullptr);
        REQUIRE_FALSE(s.propagate());
        const auto& r = s.conflict();
        REQUIRE(3u == size32(r));
        REQUIRE(contains(r, ~tern[0]));
        REQUIRE(contains(r, ~tern[1]));
        REQUIRE(contains(r, ~tern[2]));
    }

    SECTION("testEstimateBCP") {
        Literal a = posLit(ctx.addVar(VarType::atom));
        Literal b = posLit(ctx.addVar(VarType::atom));
        Literal c = posLit(ctx.addVar(VarType::atom));
        Literal d = posLit(ctx.addVar(VarType::atom));
        Literal e = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        ctx.addBinary(a, b);
        ctx.addBinary(~b, c);
        ctx.addBinary(~c, d);
        ctx.addBinary(~d, e);
        ctx.endInit();
        for (int i = 0; i < 4; ++i) {
            uint32_t est = s.estimateBCP(~a, i);
            REQUIRE(uint32_t(i + 2) == est);
        }
    }

    SECTION("testEstimateBCPLoop") {
        Literal a = posLit(ctx.addVar(VarType::atom));
        Literal b = posLit(ctx.addVar(VarType::atom));
        Literal c = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        ctx.addBinary(a, b);
        ctx.addBinary(~b, c);
        ctx.addBinary(~c, ~a);
        ctx.endInit();
        REQUIRE(uint32_t(3) == s.estimateBCP(~a, -1));
    }

    SECTION("testAssertImmediate") {
        Literal a = posLit(ctx.addVar(VarType::atom));
        Literal b = posLit(ctx.addVar(VarType::atom));
        Literal d = posLit(ctx.addVar(VarType::atom));
        Literal q = posLit(ctx.addVar(VarType::atom));
        Literal f = posLit(ctx.addVar(VarType::atom));
        Literal x = posLit(ctx.addVar(VarType::atom));
        Literal z = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();

        ClauseCreator cl(&s);
        cl.addDefaultFlags(ClauseCreator::clause_watch_first);
        cl.start().add(~z).add(d).end();
        cl.start().add(a).add(b).end();
        cl.start().add(a).add(~b).add(z).end();
        cl.start().add(a).add(~b).add(~z).add(d).end();
        cl.start().add(~b).add(~z).add(~d).add(q).end();
        cl.start().add(~q).add(f).end();
        cl.start().add(~f).add(~z).add(x).end();
        s.assume(~a);
        REQUIRE(true == s.propagate());

        REQUIRE(7u == s.numAssignedVars());

        Antecedent whyB = s.reason(b);
        Antecedent whyZ = s.reason(z);
        Antecedent whyD = s.reason(d);
        Antecedent whyQ = s.reason(q);
        Antecedent whyF = s.reason(f);
        Antecedent whyX = s.reason(x);

        REQUIRE((whyB.type() == Antecedent::binary && whyB.firstLiteral() == ~a));
        REQUIRE((whyZ.type() == Antecedent::ternary && whyZ.firstLiteral() == ~a && whyZ.secondLiteral() == b));
        REQUIRE(whyD.type() == Antecedent::generic);
        REQUIRE(whyQ.type() == Antecedent::generic);

        REQUIRE((whyF.type() == Antecedent::binary && whyF.firstLiteral() == q));
        REQUIRE((whyX.type() == Antecedent::ternary && whyX.firstLiteral() == f && whyX.secondLiteral() == z));
    }

    SECTION("testPreferShortBfs") {
        Literal a = posLit(ctx.addVar(VarType::atom));
        Literal b = posLit(ctx.addVar(VarType::atom));
        Literal p = posLit(ctx.addVar(VarType::atom));
        Literal q = posLit(ctx.addVar(VarType::atom));
        Literal x = posLit(ctx.addVar(VarType::atom));
        Literal y = posLit(ctx.addVar(VarType::atom));
        Literal z = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        ClauseCreator cl(&s);
        cl.addDefaultFlags(ClauseCreator::clause_watch_least);
        cl.start().add(a).add(x).add(y).add(p).end();    // c1
        cl.start().add(a).add(x).add(y).add(z).end();    // c2
        cl.start().add(a).add(p).end();                  // c3
        cl.start().add(a).add(~p).add(z).end();          // c4
        cl.start().add(~z).add(b).end();                 // c5
        cl.start().add(a).add(x).add(q).add(~b).end();   // c6
        cl.start().add(a).add(~b).add(~p).add(~q).end(); // c7

        REQUIRE(7u == s.numConstraints());
        REQUIRE(2u == ctx.numBinary());
        REQUIRE(1u == ctx.numTernary());

        s.assume(~x);
        s.propagate();
        s.assume(~y);
        s.propagate();
        REQUIRE(2u == s.numAssignedVars());
        s.assume(~a);

        REQUIRE_FALSE(s.propagate());

        REQUIRE(7u == s.numAssignedVars());

        REQUIRE(s.reason(b).type() == Antecedent::binary);
        REQUIRE(s.reason(p).type() == Antecedent::binary);
        REQUIRE(s.reason(z).type() == Antecedent::ternary);
        REQUIRE(s.reason(q).type() == Antecedent::generic);
    }
    SECTION("testPostPropInit") {
        ctx.startAddConstraints();
        auto* p = TestingPostProp::addTo(s, false);
        REQUIRE(0 == p->inits); // init is called *after* setup
        ctx.endInit();
        REQUIRE(1 == p->inits);
        ctx.startAddConstraints();
        ctx.endInit();
        REQUIRE(2 == p->inits);
    }
    SECTION("testPropagateCallsPostProp") {
        ctx.startAddConstraints();
        auto* p = TestingPostProp::addTo(s, false);
        s.propagate();
        REQUIRE(0 == p->props); // not yet enabled
        ctx.endInit();
        REQUIRE(1 == p->props);
        REQUIRE(0 == p->resets);
    }
    SECTION("testPropagateCallsResetOnConflict") {
        ctx.startAddConstraints();
        auto* p = TestingPostProp::addTo(s, true);
        ctx.endInit();
        REQUIRE(1 == p->props);
        REQUIRE(1 == p->resets);
    }

    SECTION("testPostpropPriority") {
        ctx.startAddConstraints();
        auto* p2 = TestingPostProp::addTo(s, false, 30);
        auto* p1 = TestingPostProp::addTo(s, false, 10);
        auto* p3 = TestingPostProp::addTo(s, false, 20);
        REQUIRE((p1->next == p3 && p3->next == p2));
    }

    SECTION("testPostpropPriorityExt") {
        ctx.startAddConstraints();
        auto* p3 = TestingPostProp::addTo(s, false, PostPropagator::priority_class_general);
        auto* p2 = TestingPostProp::addTo(s, false, 20);
        REQUIRE(s.getPost(PostPropagator::priority_class_general));
        REQUIRE(s.getPost(20));
        REQUIRE(p2->next == p3);
        auto* p4 = TestingPostProp::addTo(s, false, PostPropagator::priority_class_general);
        REQUIRE(p2->next == p3);
        REQUIRE(p3->next == p4);
        ctx.endInit();
        REQUIRE(p3->inits == 1);
        p3->props = 0;
        p2->props = 0;
        p4->props = 0;
        s.removePost(p2);
        s.removePost(p3);
        s.addPost(p3);
        s.propagate();
        REQUIRE((p3->props == 1 && p4->props == 1));
        auto* p1 = TestingPostProp::addTo(s, false, 10);
        REQUIRE(p1->next == p4);
        s.addPost(p2);
        REQUIRE((p1->next == p2 && p2->next == p4));
        s.removePost(p3);
        s.removePost(p4);
        s.propagate();
        REQUIRE((p3->props == 1 && p4->props == 1 && p1->props == 1 && p2->props == 1));
        s.addPost(p3);
        s.addPost(p4);
        p3->conflict = true;
        s.propagate();
        REQUIRE((p3->props == 2 && p1->props == 2 && p2->props == 2 && p4->props == 1));
    }

    SECTION("testPostpropRemove") {
        ctx.startAddConstraints();
        auto* p1 = TestingPostProp::addTo(s, false, 1);
        auto* p2 = TestingPostProp::addTo(s, false, 2);
        auto* p3 = TestingPostProp::addTo(s, false, 3);
        REQUIRE((p1->next == p2 && p2->next == p3));
        s.removePost(p2);
        std::unique_ptr<TestingPostProp> x(p2);
        REQUIRE((p1->next == p3 && p3->next == nullptr && p2->next == nullptr));
        s.removePost(p2);
        s.removePost(p3);
        std::unique_ptr<TestingPostProp> y(p3);
        REQUIRE(p1->next == 0);
        ctx.endInit();
        REQUIRE(p1->props == 1);
    }

    SECTION("testPostpropRemoveOnProp") {
        ctx.startAddConstraints();
        auto* p1 = TestingPostProp::addTo(s, false);
        auto* p2 = TestingPostProp::addTo(s, false);
        auto* p3 = TestingPostProp::addTo(s, false);
        ctx.endInit();
        p2->deleteOnProp = true;
        s.propagate();
        REQUIRE((p1->props == 2 && p3->props == 2));
    }

    SECTION("testPostpropBug") {
        ctx.startAddConstraints();
        auto* p1 = TestingPostProp::addTo(s, false);
        ctx.endInit();
        // later
        ctx.startAddConstraints();
        s.removePost(p1);
        std::unique_ptr<TestingPostProp> x(p1);
        ctx.endInit();
        s.removePost(p1);
        REQUIRE(p1->inits == 1);
    }

    SECTION("testPostpropAddAfterInitBug") {
        ctx.startAddConstraints();
        ctx.endInit();
        auto* p1 = TestingPostProp::addTo(s, false);
        REQUIRE(p1->inits == 1);
        s.propagate();
        REQUIRE(p1->props == 1);
    }

    SECTION("testPostpropRemoveSimplify") {
        Literal a = posLit(ctx.addVar(VarType::atom));
        Literal b = posLit(ctx.addVar(VarType::atom));
        Literal c = posLit(ctx.addVar(VarType::atom));
        Literal d = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        auto* p1             = TestingPostProp::addTo(s, false);
        auto* p2             = TestingPostProp::addTo(s, false);
        auto* p3             = TestingPostProp::addTo(s, false);
        bool  pDestroyed     = false;
        p2->removeOnSimplify = true;
        p2->destroyed        = &pDestroyed;
        s.force(d, nullptr);
        s.simplify();
        REQUIRE(p2->simps == 0);
        REQUIRE_FALSE(pDestroyed);

        ctx.endInit();

        s.force(a, nullptr);
        s.simplify();
        REQUIRE(p1->simps == 1);
        REQUIRE(p3->simps == 1);
        REQUIRE(p1->next == p3);
        REQUIRE(p3->next == nullptr);
        REQUIRE(pDestroyed);

        pDestroyed           = false;
        p1->destroyed        = &pDestroyed;
        p1->removeOnSimplify = true;
        s.force(b, nullptr);
        s.simplify();
        REQUIRE(p3->simps == 2);
        REQUIRE(p3->next == nullptr);
        REQUIRE(pDestroyed);

        pDestroyed           = false;
        p3->destroyed        = &pDestroyed;
        p3->removeOnSimplify = true;
        s.force(c, nullptr);
        s.simplify();
        REQUIRE(pDestroyed);
    }

    SECTION("testSimplifyRemovesSatBinClauses") {
        Literal a = posLit(ctx.addVar(VarType::atom));
        Literal b = posLit(ctx.addVar(VarType::atom));
        Literal c = posLit(ctx.addVar(VarType::atom));
        Literal d = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        ctx.addBinary(a, b);
        ctx.addBinary(a, c);
        ctx.addBinary(~a, d);
        s.force(a, nullptr);
        s.simplify();
        REQUIRE(0u == ctx.numBinary());
    }

    SECTION("testSimplifyRemovesSatTernClauses") {
        Literal a = posLit(ctx.addVar(VarType::atom));
        Literal b = posLit(ctx.addVar(VarType::atom));
        Literal c = posLit(ctx.addVar(VarType::atom));
        Literal d = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        ctx.addTernary(a, b, d);
        ctx.addTernary(~a, b, c);
        s.force(a, nullptr);
        s.simplify();
        s.assume(~b);
        REQUIRE(0u == ctx.numTernary());

        // simplify transformed the tern-clause ~a b c to the bin clause b c
        // because ~a is false on level 0
        REQUIRE(1u == ctx.numBinary());
        s.propagate();
        REQUIRE(s.isTrue(c));
    }

    SECTION("testSimplifyRemovesSatConstraints") {
        Literal a = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        TestingConstraint* t1;
        TestingConstraint* t2;
        TestingConstraint* t3;
        TestingConstraint* t4;
        bool               t2Del = false, t3Del = false;
        s.add(t1 = new TestingConstraint);
        s.add(t2 = new TestingConstraint(&t2Del));
        ctx.endInit();
        s.addLearnt(t3 = new TestingConstraint(&t3Del, ConstraintType::conflict), TestingConstraint::size());
        s.addLearnt(t4 = new TestingConstraint(nullptr, ConstraintType::conflict), TestingConstraint::size());
        t1->sat = false;
        t2->sat = true;
        t3->sat = true;
        t4->sat = false;
        REQUIRE(2u == s.numLearntConstraints());
        REQUIRE(2u == s.numLearntConstraints());
        s.force(a, nullptr);
        s.simplify();
        REQUIRE(1u == s.numLearntConstraints());
        REQUIRE(1u == s.numLearntConstraints());
        REQUIRE(t2Del);
        REQUIRE(t3Del);
    }

    SECTION("testRemoveConditional") {
        auto a = ctx.addVar(VarType::atom);
        auto b = ctx.addVar(VarType::atom);
        auto c = ctx.addVar(VarType::atom);
        ctx.startAddConstraints();
        ctx.endInit();
        Literal       tag = posLit(s.pushTagVar(false));
        ClauseCreator cc(&s);
        cc.start(ConstraintType::conflict).add(posLit(a)).add(posLit(b)).add(posLit(c)).add(~tag).end();
        REQUIRE(s.numLearntConstraints() == 1);
        s.removeConditional();
        REQUIRE(s.numLearntConstraints() == 0);
    }

    SECTION("testStrengthenConditional") {
        auto a = ctx.addVar(VarType::atom);
        auto b = ctx.addVar(VarType::atom);
        auto c = ctx.addVar(VarType::atom);
        ctx.startAddConstraints();
        ctx.endInit();
        ClauseCreator cc(&s);
        Literal       tag = posLit(s.pushTagVar(false));
        cc.start(ConstraintType::conflict).add(posLit(a)).add(posLit(b)).add(posLit(c)).add(~tag).end();
        REQUIRE(s.numLearntConstraints() == 1);
        s.strengthenConditional();
        REQUIRE((ctx.numLearntShort() == 1 || ctx.numTernary() == 1));
    }

    SECTION("testLearnConditional") {
        auto b = ctx.addVar(VarType::atom);
        ctx.startAddConstraints();
        ctx.endInit();
        Literal tag = posLit(s.pushTagVar(true));
        s.assume(posLit(b));
        s.propagate();
        auto* cfl = new TestingConstraint;
        cfl->ante.push_back(tag);
        cfl->ante.push_back(posLit(b));
        s.force(lit_false, cfl);
        cfl->destroy(&s, true);
        s.resolveConflict();
        REQUIRE((ctx.numLearntShort() == 0 && ctx.numBinary() == 0));
        REQUIRE(((s.numLearntConstraints() == 1 && s.decisionLevel() == 1)));
        s.strengthenConditional();
        s.clearAssumptions();
        REQUIRE(s.isTrue(negLit(b)));
    }

    SECTION("testResolveUnary") {
        ctx.enableStats(1);
        auto a = ctx.addVar(VarType::atom);
        auto b = ctx.addVar(VarType::atom);
        auto c = ctx.addVar(VarType::atom);
        ctx.startAddConstraints();
        ctx.addBinary(posLit(a), posLit(b));
        ctx.addBinary(negLit(b), posLit(c));
        ctx.addBinary(negLit(a), posLit(c));
        s.assume(negLit(c));
        REQUIRE_FALSE(s.propagate());
        REQUIRE(s.resolveConflict());
        REQUIRE_FALSE(s.hasConflict());
        REQUIRE(s.isTrue(posLit(c)));
        REQUIRE(0u == s.decisionLevel());
        REQUIRE(s.stats.extra->learnts[ExtendedStats::index(ConstraintType::conflict)] == 1);
    }

    SECTION("testResolveConflict") {
        Literal x1  = posLit(ctx.addVar(VarType::atom));
        Literal x2  = posLit(ctx.addVar(VarType::atom));
        Literal x3  = posLit(ctx.addVar(VarType::atom));
        Literal x4  = posLit(ctx.addVar(VarType::atom));
        Literal x5  = posLit(ctx.addVar(VarType::atom));
        Literal x6  = posLit(ctx.addVar(VarType::atom));
        Literal x7  = posLit(ctx.addVar(VarType::atom));
        Literal x8  = posLit(ctx.addVar(VarType::atom));
        Literal x9  = posLit(ctx.addVar(VarType::atom));
        Literal x10 = posLit(ctx.addVar(VarType::atom));
        Literal x11 = posLit(ctx.addVar(VarType::atom));
        Literal x12 = posLit(ctx.addVar(VarType::atom));
        Literal x13 = posLit(ctx.addVar(VarType::atom));
        Literal x14 = posLit(ctx.addVar(VarType::atom));
        Literal x15 = posLit(ctx.addVar(VarType::atom));
        Literal x16 = posLit(ctx.addVar(VarType::atom));
        Literal x17 = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        ClauseCreator cl(&s);
        cl.start().add(~x11).add(x12).end();
        cl.start().add(x1).add(~x12).add(~x13).end();
        cl.start().add(~x4).add(~x12).add(x14).end();
        cl.start().add(x13).add(~x14).add(~x15).end();
        cl.start().add(~x2).add(x15).add(x16).end();
        cl.start().add(x3).add(x15).add(~x17).end();
        cl.start().add(~x6).add(~x16).add(x17).end();
        cl.start().add(~x2).add(x9).add(x10).end();
        cl.start().add(~x4).add(~x7).add(~x8).end();
        cl.start().add(x5).add(x6).end();
        REQUIRE(ctx.endInit());
        REQUIRE(0u == s.queueSize());

        REQUIRE((s.assume(~x1) && s.propagate()));
        REQUIRE((s.assume(x2) && s.propagate()));
        REQUIRE((s.assume(~x3) && s.propagate()));
        REQUIRE((s.assume(x4) && s.propagate()));
        REQUIRE((s.assume(~x5) && s.propagate()));
        REQUIRE((s.assume(x7) && s.propagate()));
        REQUIRE((s.assume(~x9) && s.propagate()));

        REQUIRE_FALSE((s.assume(x11) && s.propagate()));

        REQUIRE(s.resolveConflict());
        REQUIRE(s.isTrue(x15)); // UIP
        REQUIRE(5u == s.decisionLevel());
        REQUIRE(Antecedent::generic == s.reason(x15).type());

        LitVec cflClause;
        s.reason(x15, cflClause);
        cflClause.push_back(x15);
        REQUIRE(LitVec::size_type(4) == cflClause.size());
        REQUIRE(contains(cflClause, x2));
        REQUIRE(contains(cflClause, ~x3));
        REQUIRE(contains(cflClause, x6));
        REQUIRE(contains(cflClause, x15));
    }

    SECTION("testResolveConflictBounded") {
        Literal x1  = posLit(ctx.addVar(VarType::atom));
        Literal x2  = posLit(ctx.addVar(VarType::atom));
        Literal x3  = posLit(ctx.addVar(VarType::atom));
        Literal x4  = posLit(ctx.addVar(VarType::atom));
        Literal x5  = posLit(ctx.addVar(VarType::atom));
        Literal x6  = posLit(ctx.addVar(VarType::atom));
        Literal x7  = posLit(ctx.addVar(VarType::atom));
        Literal x8  = posLit(ctx.addVar(VarType::atom));
        Literal x9  = posLit(ctx.addVar(VarType::atom));
        Literal x10 = posLit(ctx.addVar(VarType::atom));
        Literal x11 = posLit(ctx.addVar(VarType::atom));
        Literal x12 = posLit(ctx.addVar(VarType::atom));
        Literal x13 = posLit(ctx.addVar(VarType::atom));
        Literal x14 = posLit(ctx.addVar(VarType::atom));
        Literal x15 = posLit(ctx.addVar(VarType::atom));
        Literal x16 = posLit(ctx.addVar(VarType::atom));
        Literal x17 = posLit(ctx.addVar(VarType::atom));
        Literal x18 = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        ClauseCreator cl(&s);
        cl.start().add(~x11).add(x12).end();
        cl.start().add(x1).add(~x12).add(~x13).end();
        cl.start().add(~x4).add(~x12).add(x14).end();
        cl.start().add(x13).add(~x14).add(~x15).end();
        cl.start().add(~x2).add(x15).add(x16).end();
        cl.start().add(x3).add(x15).add(~x17).end();
        cl.start().add(~x6).add(~x16).add(x17).end();
        cl.start().add(~x2).add(x9).add(x10).end();
        cl.start().add(~x4).add(~x7).add(~x8).end();
        cl.start().add(x5).add(x6).end();
        REQUIRE(ctx.endInit());
        REQUIRE(0u == s.queueSize());

        REQUIRE((s.assume(~x1) && s.propagate()));
        REQUIRE((s.assume(x2) && s.propagate()));
        REQUIRE((s.assume(~x3) && s.propagate()));
        REQUIRE((s.assume(x4) && s.propagate()));
        REQUIRE((s.assume(~x5) && s.propagate()));
        REQUIRE((s.assume(x7) && s.propagate()));

        // force backtrack-level to 6
        REQUIRE((s.assume(x18) && s.propagate()));
        REQUIRE(s.backtrack());

        REQUIRE((s.assume(~x9) && s.propagate()));
        REQUIRE_FALSE((s.assume(x11) && s.propagate()));

        REQUIRE(s.resolveConflict());
        REQUIRE(s.isTrue(x15));           // UIP
        REQUIRE(6u == s.decisionLevel()); // Jump was bounded!
        Antecedent ante = s.reason(x15);
        REQUIRE(Antecedent::generic == ante.type());
        auto*  cflClause = static_cast<ClauseHead*>(ante.constraint());
        LitVec r;
        cflClause->reason(s, x15, r);
        REQUIRE(contains(r, x2));
        REQUIRE(contains(r, ~x3));
        REQUIRE(contains(r, x6));

        REQUIRE(s.hasWatch(x6, cflClause));

        REQUIRE(s.backtrack());
        REQUIRE(s.isTrue(x15)); // still true, because logically implied on level 5
        REQUIRE(s.backtrack());
        REQUIRE(value_free == s.value(x15.var()));
    }

    SECTION("testSearchKeepsAssumptions") {
        auto a = ctx.addVar(VarType::atom);
        auto b = ctx.addVar(VarType::atom);
        auto c = ctx.addVar(VarType::atom);
        auto d = ctx.addVar(VarType::atom);
        ctx.startAddConstraints();
        ClauseCreator cl(&s);
        ctx.addBinary(posLit(a), posLit(b));
        ctx.addBinary(negLit(b), posLit(c));
        ctx.addBinary(negLit(a), posLit(c));
        ctx.addBinary(negLit(c), negLit(d));
        ctx.endInit();
        s.simplify();
        s.assume(posLit(d));
        s.pushRootLevel();
        REQUIRE(value_false == s.search(UINT64_MAX, UINT32_MAX, 0));
        REQUIRE(1u == s.decisionLevel());
    }
    SECTION("testSearchAddsLearntFacts") {
        auto a = ctx.addVar(VarType::atom);
        auto b = ctx.addVar(VarType::atom);
        auto c = ctx.addVar(VarType::atom);
        auto d = ctx.addVar(VarType::atom);
        struct Dummy : DecisionHeuristic {
            Dummy(Literal first, Literal second) {
                lit[0] = first;
                lit[1] = second;
            }
            void    updateVar(const Solver&, Var_t, uint32_t) override {}
            Literal doSelect(Solver& s) override {
                for (auto l : lit) {
                    if (s.value(l.var()) == value_free) {
                        return l;
                    }
                }
                return {};
            }
            Literal lit[2];
        };
        ctx.master()->setHeuristic(new Dummy(negLit(c), negLit(a)));
        ctx.startAddConstraints();
        ClauseCreator cl(&s);
        ctx.addBinary(posLit(a), posLit(b));
        ctx.addBinary(negLit(b), posLit(c));
        ctx.addBinary(negLit(a), posLit(c));
        ctx.endInit();
        s.assume(posLit(d));
        s.pushRootLevel();
        REQUIRE(value_true == s.search(UINT64_MAX, UINT32_MAX, 0));
        s.clearAssumptions();
        REQUIRE(0u == s.decisionLevel());
        REQUIRE(s.isTrue(posLit(c)));
    }

    SECTION("testSearchMaxConflicts") {
        auto a = ctx.addVar(VarType::atom);
        auto b = ctx.addVar(VarType::atom);
        auto c = ctx.addVar(VarType::atom);
        ctx.addVar(VarType::atom);
        ctx.startAddConstraints();
        ctx.addBinary(posLit(a), negLit(b));
        ctx.addBinary(negLit(a), posLit(b));
        ctx.addBinary(negLit(a), negLit(b));
        ctx.endInit();
        s.simplify();
        s.assume(posLit(c));
        s.pushRootLevel();
        s.assume(posLit(a));
        REQUIRE(value_free == s.search(1, UINT32_MAX, 0));
        REQUIRE(1u == s.decisionLevel());
    }

    SECTION("testClearAssumptions") {
        auto a = ctx.addVar(VarType::atom);
        auto b = ctx.addVar(VarType::atom);
        ctx.addVar(VarType::atom);
        ctx.startAddConstraints();
        ctx.addBinary(negLit(a), negLit(b));
        ctx.addBinary(negLit(a), posLit(b));
        ctx.endInit();
        s.assume(posLit(a));
        s.pushRootLevel();
        REQUIRE_FALSE(s.propagate());
        REQUIRE(s.clearAssumptions());
        REQUIRE(0u == s.decisionLevel());

        s.force(posLit(a), nullptr);
        REQUIRE_FALSE(s.propagate());
        REQUIRE_FALSE(s.clearAssumptions());
    }

    SECTION("testStopConflict") {
        auto a = ctx.addVar(VarType::atom);
        auto b = ctx.addVar(VarType::atom);
        auto c = ctx.addVar(VarType::atom);
        auto d = ctx.addVar(VarType::atom);
        ctx.startAddConstraints();
        ctx.addBinary(negLit(a), negLit(b));
        ctx.addBinary(negLit(a), posLit(b));
        ctx.endInit();
        s.assume(posLit(a)) && not s.propagate() && s.resolveConflict();
        REQUIRE((s.decisionLevel() == 0 && s.queueSize() == 1 && not s.hasConflict()));
        s.setStopConflict();
        REQUIRE((s.hasConflict() && not s.resolveConflict()));
        s.clearStopConflict();
        REQUIRE((s.decisionLevel() == 0 && s.queueSize() == 1 && not s.hasConflict()));
        s.propagate();
        s.assume(posLit(c)) && s.propagate();
        s.pushRootLevel(1);
        REQUIRE(s.rootLevel() == 1);
        s.assume(posLit(d));
        s.setStopConflict();
        REQUIRE(s.rootLevel() == 2);
        s.clearStopConflict();
        REQUIRE((s.rootLevel() == 1 && s.queueSize() == 1));
    }

    SECTION("testClearStopConflictResetsBtLevel") {
        auto a = ctx.addVar(VarType::atom);
        auto b = ctx.addVar(VarType::atom);
        auto c = ctx.addVar(VarType::atom);
        auto d = ctx.addVar(VarType::atom);
        ctx.startAddConstraints();
        ctx.addBinary(negLit(c), posLit(d));
        ctx.endInit();
        s.assume(posLit(a)) && s.propagate();
        s.assume(posLit(b)) && s.propagate();
        s.assume(posLit(c)) && s.propagate();
        REQUIRE(s.numFreeVars() == 0);
        s.setBacktrackLevel(s.decisionLevel());
        s.backtrack();
        uint32_t bt = s.backtrackLevel();
        s.assume(posLit(d)) && s.propagate();
        REQUIRE(bt != s.decisionLevel());
        s.setStopConflict();
        REQUIRE(s.backtrackLevel() == s.decisionLevel());
        s.clearStopConflict();
        REQUIRE(s.backtrackLevel() == bt);
    }

    SECTION("testProblemStats") {
        ProblemStats p1, p2;
        REQUIRE(uint32_t(0) == p1.vars.num);
        REQUIRE(uint32_t(0) == p2.vars.eliminated);
        REQUIRE(uint32_t(0) == p1.constraints.other);
        REQUIRE(uint32_t(0) == p2.constraints.binary);
        REQUIRE(uint32_t(0) == p2.constraints.ternary);

        p1.vars.num            = 100;
        p2.vars.num            = 150;
        p1.vars.eliminated     = 20;
        p2.vars.eliminated     = 30;
        p1.constraints.other   = 150;
        p2.constraints.other   = 150;
        p1.constraints.binary  = 0;
        p2.constraints.binary  = 100;
        p1.constraints.ternary = 100;
        p2.constraints.ternary = 0;
        p1.diff(p2);

        REQUIRE(uint32_t(50) == p1.vars.num);
        REQUIRE(uint32_t(10) == p1.vars.eliminated);
        REQUIRE(uint32_t(0) == p1.constraints.other);
        REQUIRE(uint32_t(100) == p1.constraints.binary);
        REQUIRE(uint32_t(100) == p1.constraints.ternary);

        StatisticObject st = StatisticObject::map(&p1);
        REQUIRE(st.size() == p1.size());
        REQUIRE(st.at("vars").value() == double(p1.vars.num));
        REQUIRE(st.at("constraints").value() == (double) p1.constraints.other);
        REQUIRE(st.at("constraints_binary").value() == (double) p1.constraints.binary);
        REQUIRE(st.at("constraints_ternary").value() == (double) p1.constraints.ternary);
    }

    SECTION("testSolverStats") {
        SolverStats st, st2;
        st.enableExtended();
        st2.enableExtended();

        st.conflicts  = 12;
        st2.conflicts = 3;
        st.choices    = 100;
        st2.choices   = 99;
        st.restarts   = 7;
        st2.restarts  = 8;

        st.extra->models      = 10;
        st2.extra->models     = 2;
        st.extra->learnts[0]  = 6;
        st2.extra->learnts[0] = 4;
        st.extra->learnts[1]  = 5;
        st2.extra->learnts[1] = 4;
        st.extra->lits[0]     = 15;
        st2.extra->lits[0]    = 14;
        st.extra->lits[1]     = 5;
        st2.extra->lits[1]    = 4;
        st.extra->binary      = 6;
        st2.extra->ternary    = 5;
        st.extra->deleted     = 10;

        st.accu(st2);

        REQUIRE(uint64_t(15) == st.conflicts);
        REQUIRE(uint64_t(199) == st.choices);
        REQUIRE(uint64_t(15) == st.restarts);
        REQUIRE(uint64_t(12) == st.extra->models);
        REQUIRE(uint64_t(29) == st.extra->lits[0]);
        REQUIRE(uint64_t(9) == st.extra->lits[1]);
        REQUIRE(uint64_t(10) == st.extra->learnts[0]);
        REQUIRE(uint64_t(9) == st.extra->learnts[1]);
        REQUIRE(uint32_t(6) == st.extra->binary);
        REQUIRE(uint32_t(5) == st.extra->ternary);
        REQUIRE(uint64_t(10) == st.extra->deleted);

        StatisticObject so = StatisticObject::map(&st);
        REQUIRE(double(15) == so.at("conflicts").value());
        REQUIRE(double(199) == so.at("choices").value());
        REQUIRE(double(15) == so.at("restarts").value());
        StatisticObject e = so.at("extra");
        REQUIRE(double(12) == e.at("models").value());
        REQUIRE(double(29) == e.at("lits_conflict").value());
        REQUIRE(double(9) == e.at("lemmas_loop").value());
        REQUIRE(double(6) == e.at("lemmas_binary").value());
        REQUIRE(double(5) == e.at("lemmas_ternary").value());
        REQUIRE(double(10) == e.at("lemmas_deleted").value());
    }
    SECTION("testClaspStats") {
        using Key_t = ClaspStatistics::Key_t;
        SolverStats st;
        st.enableExtended();
        st.choices           = 100;
        st.extra->learnts[1] = 5;
        st.extra->binary     = 6;
        ClaspStatistics stats(StatisticObject::map(&st));
        Key_t           root = stats.root();
        REQUIRE(stats.type(root) == Potassco::StatisticsType::map);
        REQUIRE(stats.writable(root) == false);
        Key_t choices = stats.get(root, "choices");
        REQUIRE(stats.type(choices) == Potassco::StatisticsType::value);
        REQUIRE(stats.value(choices) == (double) 100);
        Key_t extra = stats.get(root, "extra");
        REQUIRE(stats.type(extra) == Potassco::StatisticsType::map);
        Key_t bin = stats.get(extra, "lemmas_binary");
        REQUIRE(stats.type(bin) == Potassco::StatisticsType::value);
        REQUIRE(stats.value(bin) == (double) 6);

        Key_t binByPath = stats.get(root, "extra.lemmas_binary");
        REQUIRE(binByPath == bin);
    }

    SECTION("testSplitInc") {
        Literal a = posLit(ctx.addVar(VarType::atom));
        Literal b = posLit(ctx.addVar(VarType::atom));
        Literal c = posLit(ctx.addVar(VarType::atom));
        Literal d = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        ctx.endInit();
        s.assume(a) && s.propagate();
        s.assume(b) && s.propagate();
        s.assume(c) && s.propagate();
        s.assume(d) && s.propagate();
        LitVec gp;
        s.copyGuidingPath(gp);
        s.pushRootLevel();
        gp.push_back(~a);
        REQUIRE((gp.size() == 1 && gp[0] == ~a && s.rootLevel() == 1));
        gp.pop_back();

        s.copyGuidingPath(gp);
        s.pushRootLevel();
        gp.push_back(~b);
        REQUIRE((gp.size() == 2 && gp[1] == ~b && s.rootLevel() == 2));
        gp.pop_back();

        s.copyGuidingPath(gp);
        s.pushRootLevel();
        gp.push_back(~c);
        REQUIRE((gp.size() == 3 && gp[2] == ~c && s.rootLevel() == 3));
        gp.pop_back();
    }

    SECTION("testSplitFlipped") {
        Literal a = posLit(ctx.addVar(VarType::atom));
        Literal b = posLit(ctx.addVar(VarType::atom));
        Literal c = posLit(ctx.addVar(VarType::atom));
        Literal d = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        ctx.endInit();

        LitVec gp;

        s.assume(a) && s.propagate();
        s.pushRootLevel();
        s.assume(b) && s.propagate();
        s.backtrack();

        s.assume(c) && s.propagate();
        s.backtrack();

        s.assume(d) && s.propagate();
        s.copyGuidingPath(gp);
        REQUIRE(contains(gp, ~b));
        REQUIRE(contains(gp, ~c));
    }

    SECTION("testSplitFlipToNewRoot") {
        Literal a = posLit(ctx.addVar(VarType::atom));
        Literal b = posLit(ctx.addVar(VarType::atom));
        Literal c = posLit(ctx.addVar(VarType::atom));
        Literal d = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        ctx.endInit();

        LitVec gp;
        s.assume(a) && s.propagate();
        s.copyGuidingPath(gp);
        s.pushRootLevel();

        s.assume(b) && s.propagate();
        s.assume(c) && s.propagate();

        s.backtrack(); // bt-level now 2, rootLevel = 1

        s.copyGuidingPath(gp);
        s.pushRootLevel();
        REQUIRE(s.rootLevel() == s.backtrackLevel());
        s.assume(d) && s.propagate();
        s.copyGuidingPath(gp);
        s.pushRootLevel();
        REQUIRE(contains(gp, ~c));
    }

    SECTION("testSplitImplied") {
        Literal a = posLit(ctx.addVar(VarType::atom));
        Literal b = posLit(ctx.addVar(VarType::atom));
        Literal c = posLit(ctx.addVar(VarType::atom));
        Literal d = posLit(ctx.addVar(VarType::atom));
        Literal e = posLit(ctx.addVar(VarType::atom));
        Literal f = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        ctx.endInit();

        s.assume(a) && s.propagate();
        s.assume(b) && s.propagate();
        s.pushRootLevel(2);

        s.assume(c);
        s.setBacktrackLevel(s.decisionLevel());
        auto x = std::make_unique<TestingConstraint>();
        s.force(~d, 2, x.get());

        LitVec gp;
        s.copyGuidingPath(gp);

        REQUIRE(contains(gp, ~d));
        s.pushRootLevel();
        s.assume(e);
        s.setBacktrackLevel(s.decisionLevel());
        s.force(~f, 2, x.get());

        s.copyGuidingPath(gp);
        REQUIRE(contains(gp, ~f));
    }

    SECTION("testAddShortIncremental") {
        Literal a = posLit(ctx.addVar(VarType::atom));
        Literal b = posLit(ctx.addVar(VarType::atom));
        ctx.setConcurrency(2);
        ctx.startAddConstraints();
        ctx.addBinary(a, b);
        ctx.endInit();
        REQUIRE(ctx.numBinary() == 1);
        ctx.startAddConstraints();
        ctx.addBinary(~a, ~b);
        ctx.endInit();
        REQUIRE(ctx.numBinary() == 2);
    }

    SECTION("testSwitchToMtIncremental") {
        Literal a = posLit(ctx.addVar(VarType::atom));
        Literal b = posLit(ctx.addVar(VarType::atom));
        Literal c = posLit(ctx.addVar(VarType::atom));
        Literal d = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        ClauseCreator cl(&s);
        cl.start().add(a).add(b).add(c).add(d).end();
        ctx.endInit(true);
        REQUIRE((s.numVars() == 4 && s.numConstraints() == 1));
        ctx.unfreeze();
        Solver& s2 = ctx.pushSolver();
        REQUIRE(ctx.concurrency() == 2);
        ctx.startAddConstraints();
        cl.start().add(~a).add(~b).add(~c).add(~d).end();
        ctx.endInit(true);
        REQUIRE((s.numVars() == 4 && s.numConstraints() == 2));
        REQUIRE((s2.numVars() == 4 && s2.numConstraints() == 2));
    }
    SECTION("testPushAux") {
        Literal a = posLit(ctx.addVar(VarType::atom));
        Literal b = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        ctx.endInit();
        REQUIRE(s.numVars() == s.sharedContext()->numVars());

        auto aux = s.pushAuxVar();
        REQUIRE(s.numVars() > s.sharedContext()->numVars());
        REQUIRE((s.validVar(aux) && not s.sharedContext()->validVar(aux)));
        LitVec clause;
        clause.push_back(posLit(aux));
        clause.push_back(a);
        clause.push_back(b);
        ClauseCreator::create(s, clause, {}, ConstraintType::conflict);
        REQUIRE(s.sharedContext()->numTernary() == 0);
        REQUIRE(s.numLearntConstraints() == 1);
        s.assume(~a) && s.propagate();
        s.assume(~b) && s.propagate();
        REQUIRE(s.isTrue(posLit(aux)));
        s.popAuxVar();
        REQUIRE(s.decisionLevel() < 2u);
        REQUIRE(s.numVars() == s.sharedContext()->numVars());
    }
    SECTION("testPushAuxFact") {
        Literal a = posLit(ctx.addVar(VarType::atom));
        Literal b = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        ctx.endInit();
        auto   aux = s.pushAuxVar();
        LitVec clause;
        clause.push_back(posLit(aux));
        clause.push_back(a);
        ClauseCreator::create(s, clause, {}, ConstraintType::conflict);
        s.force(~a) && s.propagate();
        s.force(b) && s.simplify();
        REQUIRE(s.numFreeVars() == 0);
        s.popAuxVar();
        REQUIRE((s.numFreeVars() == 0 && s.validVar(aux) == false));
    }
    SECTION("testPopAuxRemovesConstraints") {
        Literal a = posLit(ctx.addVar(VarType::atom));
        Literal b = posLit(ctx.addVar(VarType::atom));
        Literal c = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        ctx.endInit();
        auto   aux = s.pushAuxVar();
        LitVec clause;
        clause.push_back(a);
        clause.push_back(b);
        clause.push_back(c);
        clause.push_back(posLit(aux));
        ClauseCreator::create(s, clause, {}, ConstraintType::conflict);
        clause.clear();
        clause.push_back(a);
        clause.push_back(b);
        clause.push_back(~c);
        clause.push_back(negLit(aux));
        ClauseCreator::create(s, clause, {}, ConstraintType::conflict);
        REQUIRE(s.numLearntConstraints() == 2);
        s.popAuxVar();
        REQUIRE(s.numLearntConstraints() == 0);
    }
    SECTION("testPopAuxRemovesConstraintsRegression") {
        Literal a = posLit(ctx.addVar(VarType::atom));
        Literal b = posLit(ctx.addVar(VarType::atom));
        Literal c = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        ctx.endInit();
        auto         aux = s.pushAuxVar();
        WeightLitVec lits;
        lits.push_back(WeightLiteral{a, 1});
        lits.push_back(WeightLiteral{b, 1});
        lits.push_back(WeightLiteral{c, 1});
        lits.push_back(WeightLiteral{posLit(aux), 1});
        Solver::ConstraintDB t;
        t.push_back(WeightConstraint::create(s, lit_false, lits, 3,
                                             WeightConstraint::create_explicit | WeightConstraint::create_no_add |
                                                 WeightConstraint::create_no_freeze | WeightConstraint::create_no_share)
                        .first());
        s.force(posLit(aux)) && s.propagate();
        s.popAuxVar(1, &t);
    }
    SECTION("testPopAuxMaintainsQueue") {
        Literal a = posLit(ctx.addVar(VarType::atom));
        Literal b = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        ctx.endInit();
        auto aux = s.pushAuxVar();
        s.force(a, nullptr);
        s.propagate();
        s.force(posLit(aux), nullptr);
        s.force(b, nullptr);
        s.popAuxVar();
        REQUIRE((s.isTrue(a) && s.isTrue(b) && s.queueSize() == 1 && s.assignment().units() == 1));
    }

    SECTION("testIncrementalAux") {
        Literal a = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        Solver& s2 = ctx.pushSolver();
        ctx.endInit(true);
        auto aux = s2.pushAuxVar();
        REQUIRE((not ctx.validVar(aux) && not s.validVar(aux)));
        LitVec clause;
        clause.push_back(a);
        clause.push_back(posLit(aux));
        ClauseCreator::create(s2, clause, {}, ConstraintType::conflict);
        ctx.unfreeze();
        auto n = ctx.addVar(VarType::atom);
        ctx.startAddConstraints();
        ctx.endInit(true);
        s2.assume(negLit(n)) && s2.propagate();
        REQUIRE(s2.value(a.var()) == value_free);
    }

    SECTION("testUnfreezeStepBug") {
        Literal a = posLit(ctx.addVar(VarType::atom));
        Literal b = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        Solver& s2 = ctx.pushSolver();
        ctx.addBinary(~a, b);
        ctx.endInit(true);
        s2.force(b);
        ctx.unfreeze();
        ctx.endInit(true);
        REQUIRE(((s.force(a) && s.propagate())));
        REQUIRE(s.isTrue(b));
    }
    SECTION("testRemoveConstraint") {
        ctx.startAddConstraints();
        Solver& s2 = ctx.pushSolver();
        ctx.add(new TestingConstraint());
        ctx.endInit(true);
        REQUIRE(s2.numConstraints() == 1);
        ctx.removeConstraint(0, true);
        REQUIRE(s.numConstraints() == 0);
        REQUIRE(s2.numConstraints() == 1);
        ctx.unfreeze();
        ctx.startAddConstraints();
        ctx.add(new TestingConstraint());
        ctx.add(new TestingConstraint());
        ctx.endInit(true);
        REQUIRE(s.numConstraints() == 2);
        REQUIRE(s2.numConstraints() == 3);
    }
    SECTION("testPopVars") {
        ctx.addVar(VarType::atom);
        ctx.addVar(VarType::atom);
        ctx.addVar(VarType::atom);
        REQUIRE(ctx.numVars() == 3u);
        REQUIRE(ctx.master()->numVars() == 0u);
        ctx.popVars(2);
        REQUIRE(ctx.numVars() == 1u);
    }
    SECTION("testPopVarsAfterCommit") {
        ctx.addVar(VarType::atom);
        ctx.addVar(VarType::atom);
        ctx.addVar(VarType::atom);
        ctx.startAddConstraints();
        REQUIRE(ctx.master()->numVars() == 3u);
        REQUIRE(ctx.master()->numFreeVars() == 3u);
        ctx.popVars(2);
        REQUIRE(ctx.numVars() == 1u);
        ctx.endInit();
        REQUIRE(ctx.master()->numVars() == 1u);
        REQUIRE(ctx.master()->numFreeVars() == 1u);
    }
    SECTION("testPopVarsIncremental") {
        ctx.requestStepVar();
        auto v1 = ctx.addVar(VarType::atom);
        ctx.addVar(VarType::atom);
        auto v3 = ctx.addVar(VarType::atom);
        ctx.startAddConstraints();
        ctx.endInit();
        REQUIRE(ctx.numVars() == 4u);
        REQUIRE(ctx.stepLiteral().var() == 4u);
        ctx.addUnary(posLit(v3));
        ctx.addUnary(posLit(v1));
        REQUIRE(ctx.master()->numAssignedVars() == 2u);
        REQUIRE(ctx.master()->trailLit(0) == posLit(v3));
        REQUIRE(ctx.master()->trailLit(1) == posLit(v1));
        ctx.unfreeze();
        ctx.popVars(2u);
        INFO("step var is not counted");
        REQUIRE(ctx.numVars() == 1u);
        REQUIRE(ctx.stepLiteral().var() == 0u);
        REQUIRE(ctx.master()->numAssignedVars() == 1u);
        REQUIRE(ctx.master()->trailLit(0) == posLit(v1));
        ctx.endInit();
        ctx.unfreeze();
        auto v = ctx.addVar(VarType::atom);
        ctx.setFrozen(v, true);
        ctx.startAddConstraints();
        ctx.endInit();
        REQUIRE(ctx.numVars() == 3u);
        ctx.unfreeze();
        ctx.popVars(2u);
        INFO("step var is not counted");
        REQUIRE(ctx.stepLiteral().var() == 0u);
        REQUIRE(ctx.stats().vars.frozen == 0u);
    }
    SECTION("testPopVarsIncrementalBug") {
        ctx.requestStepVar();
        ctx.addVar(VarType::atom);
        ctx.addVar(VarType::atom);
        ctx.startAddConstraints();
        ctx.endInit();
        ctx.unfreeze();
        auto c = ctx.addVar(VarType::atom);
        ctx.addVar(VarType::atom);
        ctx.startAddConstraints();
        ctx.addUnary(posLit(c));
        ctx.popVars(1);
        ctx.endInit();
        REQUIRE(ctx.master()->isTrue(posLit(c)));
        REQUIRE(ctx.master()->numFreeVars() == 3);
        REQUIRE(ctx.master()->numAssignedVars() == 1);
    }
    SECTION("testPopVarsMT") {
        ctx.requestStepVar();
        ctx.addVar(VarType::atom);
        ctx.addVar(VarType::atom);
        auto    c  = ctx.addVar(VarType::atom);
        Solver& s2 = ctx.pushSolver();
        ctx.startAddConstraints();
        ctx.endInit(true);
        s2.force(posLit(c));
        ctx.unfreeze();
        REQUIRE((ctx.master()->isTrue(posLit(c)) && s2.isTrue(posLit(c))));
        ctx.popVars(2); // pop c, b
        auto d = ctx.addVar(VarType::atom);
        ctx.startAddConstraints();
        REQUIRE(ctx.master()->value(d) == value_free);
        ctx.endInit(true);
        REQUIRE(s2.value(d) == value_free);
    }

    SECTION("testPopAuxVarKeepsQueueSize") {
        auto v1 = ctx.addVar(VarType::atom);
        auto v2 = ctx.addVar(VarType::atom);
        ctx.startAddConstraints();
        ctx.endInit(true);
        auto a1 = s.pushAuxVar();
        auto a2 = s.pushAuxVar();
        s.force(posLit(a1));
        s.force(posLit(v1));
        s.force(posLit(a2));
        s.propagate();
        s.force(posLit(v2));
        REQUIRE(s.assignment().units() == 3u);
        REQUIRE(s.queueSize() == 1u);
        REQUIRE(s.numAssignedVars() == 4u);
        s.popAuxVar();
        REQUIRE_FALSE(s.validVar(a1));
        REQUIRE_FALSE(s.validVar(a2));
        REQUIRE(s.numAssignedVars() == 2u);
        REQUIRE(s.queueSize() == 1u);
        REQUIRE(s.assignment().units() == 1u);
    }

    SECTION("testPopAuxVarCountsCorrectly") {
        Var_t v[5];
        for (Var_t& x : v) { x = ctx.addVar(VarType::atom); }
        ctx.startAddConstraints();
        ctx.endInit(true);
        Var_t a[6];
        for (Var_t& x : a) { x = s.pushAuxVar(); }
        SECTION("with empty queue") {
            s.force(posLit(v[0]));
            s.force(posLit(v[1]));
            s.force(posLit(a[0]));
            s.force(posLit(a[1]));
            s.force(posLit(a[2]));
            s.force(posLit(v[2]));
            s.force(posLit(a[3]));
            s.force(posLit(v[3]));
            s.force(posLit(a[4]));
            s.force(posLit(a[5]));
            s.force(posLit(v[4]));
            s.propagate() && s.simplify();
            REQUIRE(s.assignment().units() == 11u);
            REQUIRE(s.queueSize() == 0u);
            REQUIRE(s.numAssignedVars() == 11u);
            s.popAuxVar();
            REQUIRE(s.queueSize() == 0u);
            REQUIRE(s.assignment().units() == 5u);
        }
        SECTION("with non-empty queue") {
            s.force(posLit(v[0]));
            s.force(posLit(v[1]));
            s.force(posLit(a[0]));
            s.force(posLit(a[1]));
            s.force(posLit(a[2]));
            s.force(posLit(v[2]));
            s.force(posLit(a[3]));
            s.force(posLit(v[3]));
            s.force(posLit(a[4]));
            s.propagate() && s.simplify();
            s.force(posLit(a[5]));
            s.force(posLit(v[4]));
            REQUIRE(s.assignment().units() == 9u);
            REQUIRE(s.queueSize() == 2u);
            REQUIRE(s.numAssignedVars() == 11u);
            s.popAuxVar();
            REQUIRE(s.queueSize() == 1u);
            REQUIRE(s.assignment().units() == 4u);
        }
        REQUIRE(s.numAssignedVars() == 5u);
        REQUIRE(s.numAuxVars() == 0u);
    }
}
TEST_CASE("once", "[.once]") {
    SECTION("testScheduleAdvance") {
        ScheduleStrategy r1 = ScheduleStrategy::geom(100, 1.5, 13);
        for (uint32_t i = 0, m = (1u << 15) - 1; i != m; ++i, r1.next()) {
            ScheduleStrategy r2 = ScheduleStrategy::geom(100, 1.5, 13);
            r2.advanceTo(i);
            REQUIRE((r1.idx == r2.idx && r1.len == r2.len));
        }
    }
    SECTION("testLubyAdvance") {
        ScheduleStrategy r1 = ScheduleStrategy::luby(64, 10);
        for (uint32_t i = 0, m = (1u << 15) - 1; i != m; ++i, r1.next()) {
            ScheduleStrategy r2 = ScheduleStrategy::luby(64, 10);
            r2.advanceTo(i);
            REQUIRE((r1.idx == r2.idx && r1.len == r2.len));
        }
    }
    SECTION("testScheduleOverflow") {
        ScheduleStrategy g = ScheduleStrategy::geom(100, 0.0);
        REQUIRE(g.grow == 1.0);
        REQUIRE(g.current() == 100);

        g = ScheduleStrategy::geom(1, 2.0);
        REQUIRE(g.current() == 1);
        REQUIRE(g.next() == 2);
        REQUIRE(g.next() == 4);
        g.advanceTo(12);
        REQUIRE(g.current() == 4096);
        g.advanceTo(63);
        REQUIRE(g.current() == (uint64_t(1) << 63));
        g.advanceTo(64);
        REQUIRE(g.current() == UINT64_MAX);
    }
}

#if CLASP_HAS_THREADS
static void integrateGp(Solver& s, LitVec& gp) {
    s.clearAssumptions();
    for (auto lit : gp) {
        if (s.value(lit.var()) == value_free) {
            s.assume(lit) && s.propagate();
            s.pushRootLevel();
        }
    }
}

TEST_CASE("Solver mt", "[core][mt]") {
    SharedContext ctx;
    Literal       a = posLit(ctx.addVar(VarType::atom));
    Literal       b = posLit(ctx.addVar(VarType::atom));
    Literal       c = posLit(ctx.addVar(VarType::atom));
    Literal       d = posLit(ctx.addVar(VarType::atom));
    ctx.setConcurrency(2);
    Solver& s = *ctx.master();
    SECTION("testLockedValue") {
        std::vector<std::thread> t;
        SECTION("uint") {
            LockedValue<> value;
            REQUIRE(value.try_lock());
            REQUIRE_FALSE(value.try_lock());
            REQUIRE(value.value() == 0);
            uint32_t expected = 0xCAFEA00;
            for (uint32_t i : irange(1u, 64u)) {
                t.emplace_back([&value, id = i, &expected]() {
                    std::this_thread::sleep_for(std::chrono::nanoseconds(100 - id));
                    auto x = value.lock();
                    CHECK(x == expected);
                    expected += id;
                    value.store_unlock(expected);
                });
                if (i == 20) {
                    value.store_unlock(expected);
                }
            }
            while (not t.empty()) {
                t.back().join();
                t.pop_back();
            }
            REQUIRE(expected == 0xCAFF1E0);
            REQUIRE(value.value() == expected);
        }
        SECTION("pointer") {
            LockedValue<uint32_t*> value;
            REQUIRE(value.value() == nullptr);
            REQUIRE(value.try_lock());
            REQUIRE(value.value() == nullptr);
            auto active = std::make_unique<uint32_t>(0xCAFEA00);
            for (uint32_t i : irange(1u, 64u)) {
                t.emplace_back([&value, id = i, &active]() {
                    std::this_thread::sleep_for(std::chrono::nanoseconds(100 - id));
                    auto x = value.lock();
                    CHECK(active.get() == x);
                    active = std::make_unique<uint32_t>(*x + id);
                    value.store_unlock(active.get());
                });
                if (i == 17) {
                    value.store_unlock(active.get());
                }
            }
            while (not t.empty()) {
                t.back().join();
                t.pop_back();
            }
            REQUIRE(active);
            CHECK(*active == 0xCAFF1E0);
        }
    }
    SECTION("testLearntShort") {
        ctx.setShareMode(ContextParams::share_problem);
        ctx.startAddConstraints();
        ctx.endInit();
        ClauseCreator cc(&s);
        REQUIRE(cc.start(ConstraintType::conflict).add(a).add(b).end());
        REQUIRE(cc.start(ConstraintType::conflict).add(~a).add(~b).add(c).end());
        REQUIRE(ctx.numLearntShort() == 2);
        REQUIRE(ctx.numBinary() == 0);
        REQUIRE(ctx.numTernary() == 0);

        cc.start(ConstraintType::conflict).add(a).add(b).add(c).end();
        cc.start(ConstraintType::conflict).add(c).add(~b).add(~a).end();
        // ignore subsumed/duplicate clauses
        REQUIRE(ctx.numLearntShort() == 2);

        auto checkClauses = [&](std::vector<std::vector<Literal>> clauses,
                                std::source_location              loc = std::source_location::current()) {
            INFO(loc.file_name() << ":" << loc.line() << ": checkClause");
            std::vector<std::vector<Literal>> got;
            std::set<Literal>                 seen;
            for (auto& clause : clauses) {
                std::ranges::sort(clause);
                CAPTURE(clause);
                for (auto lit : clause) {
                    if (seen.insert(lit).second) {
                        CAPTURE(lit);
                        ctx.shortImplications().forEach(~lit, [&](Literal x, Literal y, Literal z = lit_false) {
                            REQUIRE(x == ~lit);
                            if (x.flagged() || y.flagged() || z.flagged()) {
                                std::vector nc{~x, y, z};
                                if (z == lit_false) {
                                    nc.pop_back();
                                }
                                std::ranges::sort(nc);
                                got.push_back(nc);
                            }
                            return true;
                        });
                    }
                }
                REQUIRE(erase(got, clause) >= clause.size());
            }
            REQUIRE(got.empty());
        };

        checkClauses({{~a, ~b, c}, {a, b}});

        s.assume(~b);
        s.propagate();
        REQUIRE(((s.isTrue(a) && s.reason(a).firstLiteral() == ~b)));
        s.undoUntil(0);
        s.assume(a);
        s.propagate();
        s.assume(b);
        s.propagate();
        REQUIRE(s.isTrue(c));
        LitVec res;
        s.reason(c, res);
        REQUIRE(contains(res, a));
        REQUIRE(contains(res, b));

        s.undoUntil(0);
        REQUIRE(cc.start(ConstraintType::conflict).add(d).add(b).end());
        REQUIRE(cc.start(ConstraintType::conflict).add(~d).add(~b).add(c).end());
        REQUIRE(ctx.numLearntShort() == 4);
        s.force(a) && s.propagate();
        ctx.unfreeze();
        REQUIRE(ctx.numLearntShort() == 3);
        checkClauses({{d, b}, {~b, c}, {~d, ~b, c}});

        SECTION("default") {
            REQUIRE((s.force(d) && s.propagate() && s.simplify()));
            REQUIRE(ctx.numLearntShort() == 2);
            checkClauses({{~b, c}});
        }
        SECTION("no duplicates") {
            ctx.setShortMode(ContextParams::short_implicit, ContextParams::simp_learnt);
            REQUIRE((s.force(d) && s.propagate() && s.simplify()));
            REQUIRE(ctx.numLearntShort() == 1);
            checkClauses({{~b, c}});
        }
    }

    SECTION("testLearntShortAreDistributed") {
        struct Dummy : public Distributor {
            Dummy() : Distributor(Policy(UINT32_MAX, UINT32_MAX, UINT32_MAX)) {}
            void publish(const Solver&, SharedLiterals* lits) override {
                uint32_t size  = lits->size();
                unary         += size == 1;
                binary        += size == 2;
                ternary       += size == 3;
                shared.push_back(lits);
            }
            uint32_t receive(const Solver&, SharedLiterals** out, uint32_t num) override {
                uint32_t r = 0;
                while (not shared.empty() && num--) {
                    out[r++] = shared.back();
                    shared.pop_back();
                }
                return r;
            }
            uint32_t                     unary{0};
            uint32_t                     binary{0};
            uint32_t                     ternary{0};
            PodVector_t<SharedLiterals*> shared;
        }* dummy;
        ctx.distributor.reset(dummy = new Dummy());
        ctx.startAddConstraints();
        ctx.endInit();
        LitVec lits;
        lits.resize(2);
        lits[0] = a;
        lits[1] = b;
        ClauseCreator::create(s, lits, {}, ConstraintInfo(ConstraintType::conflict));
        lits.resize(3);
        lits[0] = ~a;
        lits[1] = ~b;
        lits[2] = ~c;
        ClauseCreator::create(s, lits, {}, ConstraintInfo(ConstraintType::loop));
        lits.resize(1);
        lits[0] = d;
        ClauseCreator::create(s, lits, {}, ConstraintInfo(ConstraintType::conflict));
        REQUIRE(dummy->unary == 1);
        REQUIRE(dummy->binary == 1);
        REQUIRE(dummy->ternary == 1);
        SharedLiterals* rec[3];
        REQUIRE(dummy->receive(s, rec, 3) == 3);
        REQUIRE(ClauseCreator::integrate(s, rec[0], {}).ok() == true);
        REQUIRE(ClauseCreator::integrate(s, rec[1], {}).ok() == true);
        REQUIRE(ClauseCreator::integrate(s, rec[2], {}).ok() == true);
    }

    SECTION("testAuxAreNotDistributed") {
        struct Dummy : public Distributor {
            Dummy() : Distributor(Policy(UINT32_MAX, UINT32_MAX, UINT32_MAX)) {}
            void     publish(const Solver&, SharedLiterals* lits) override { shared.push_back(lits); }
            uint32_t receive(const Solver&, SharedLiterals**, uint32_t) override { return 0; }
            PodVector_t<SharedLiterals*> shared;
        }* dummy;
        ctx.distributor.reset(dummy = new Dummy());
        ctx.startAddConstraints();
        ctx.endInit();
        auto aux = s.pushAuxVar();

        LitVec lits;
        lits.resize(2);
        lits[0] = a;
        lits[1] = posLit(aux);
        ClauseCreator::create(s, lits, {}, ConstraintInfo(ConstraintType::conflict));
        lits.resize(4);
        lits[0] = ~a;
        lits[1] = posLit(aux);
        lits[2] = b;
        lits[3] = c;
        ClauseCreator::create(s, lits, {}, ConstraintInfo(ConstraintType::conflict));
        REQUIRE(s.numLearntConstraints() == 2);
        REQUIRE(dummy->shared.empty());
        REQUIRE(s.getLearnt(0).simplify(s, false) == false);
        s.pushRoot(posLit(aux));
        s.pushRoot(a);
        lits.clear();
        s.copyGuidingPath(lits);
        REQUIRE((lits.size() == 1 && lits[0] == a));
        s.clearAssumptions();
        lits.resize(4);
        lits[0] = ~a;
        lits[1] = posLit(aux);
        lits[2] = ~b;
        lits[3] = c;
        ClauseCreator::create(s, lits, {}, ConstraintInfo(ConstraintType::conflict));
        s.assume(a) && s.propagate();
        s.assume(negLit(aux)) && s.propagate();
        s.assume(~c) && s.propagate();
        REQUIRE(s.hasConflict());
        s.resolveConflict();
        REQUIRE(s.numLearntConstraints() == 4);
        REQUIRE(dummy->shared.empty());
        REQUIRE(s.sharedContext()->numTernary() + s.sharedContext()->numBinary() == 0);
    }

    SECTION("testAttachToDB") {
        ctx.startAddConstraints();
        ClauseCreator cc(&s);
        cc.start().add(a).add(b).add(c).add(d).end();
        Solver& s2 = ctx.pushSolver();
        ctx.endInit();
        ctx.attach(s2);
        REQUIRE(s2.numConstraints() == 1);
        ctx.unfreeze();
        Literal e = posLit(ctx.addVar(VarType::atom));
        Literal f = posLit(ctx.addVar(VarType::atom));
        Literal g = posLit(ctx.addVar(VarType::atom));
        Literal h = posLit(ctx.addVar(VarType::atom));
        ctx.startAddConstraints();
        cc.start().add(e).add(f).add(g).add(h).end();
        cc.start().add(a).end();
        ctx.endInit();
        REQUIRE(s.numConstraints() == 1);
        ctx.attach(s2);
        REQUIRE(s2.numConstraints() == 1);
        s2.assume(~e) && s2.propagate();
        s2.assume(~f) && s2.propagate();
        s2.assume(~g) && s2.propagate();
        REQUIRE(s2.isTrue(h));
    }

    SECTION("testAttachDeferred") {
        ctx.startAddConstraints();
        ClauseCreator cc(&s);
        cc.start().add(a).add(b).add(c).add(d).end();
        Solver& s2 = ctx.pushSolver();
        ctx.endInit(true);
        REQUIRE(s2.numConstraints() == 1);
        ctx.unfreeze();
        ctx.startAddConstraints();
        cc.start().add(~a).add(~b).add(c).add(d).end();
        ctx.endInit(false);
        REQUIRE(s.numConstraints() == 2);
        REQUIRE(s2.numConstraints() == 1);
        ctx.unfreeze();
        ctx.startAddConstraints();
        cc.start().add(a).add(b).add(~c).add(~d).end();
        ctx.endInit(true);
        REQUIRE(s.numConstraints() == 3);
        REQUIRE(s2.numConstraints() == 3);
    }
    SECTION("testUnfortunateSplitSeq") {
        ctx.startAddConstraints();
        Solver& s2 = ctx.pushSolver();
        ctx.endInit(true);

        s.assume(a) && s.propagate();
        // new fact
        s.backtrack() && s.propagate();

        s.assume(b) && s.propagate();

        LitVec sGp;
        s.copyGuidingPath(sGp);

        sGp.push_back(~b);
        s.pushRootLevel();
        integrateGp(s2, sGp);
        sGp.pop_back();
        s.clearAssumptions();

        LitVec s2Gp;

        s2.assume(c) && s.propagate();
        s2.copyGuidingPath(s2Gp);
        s.pushRootLevel();
        s2Gp.push_back(~c);
        integrateGp(s, s2Gp);
        s2.clearAssumptions();
        s2Gp.clear();

        s.assume(d) && s.propagate();
        sGp.clear();
        s.copyGuidingPath(sGp);

        integrateGp(s2, sGp);
        REQUIRE(s2.isTrue(~a));
    }
    SECTION("testPeerComputation") {
        constexpr uint32_t maxT    = 64;
        constexpr auto     threads = irange(1u, maxT + 1);
        SECTION("full") {
            for (uint32_t nt : threads) {
                for (uint32_t id : irange(nt)) {
                    CAPTURE(nt, id);
                    auto set = ParallelSolveOptions::fullPeerSet(id, nt);
                    REQUIRE_FALSE(set.contains(id));
                    REQUIRE(set.count() == (nt - 1));
                }
            }
        }
        using Topology = ParallelSolveOptions::Integration::Topology;
        SECTION("all") {
            auto topo = Topology::topo_all;
            for (uint32_t nt : threads) {
                for (uint32_t id : irange(nt)) {
                    CAPTURE(nt, id);
                    auto expected = ParallelSolveOptions::fullPeerSet(id, nt);
                    REQUIRE(ParallelSolveOptions::initPeerSet(id, topo, nt) == expected);
                }
            }
        }
        SECTION("ring") {
            auto topo = Topology::topo_ring;
            for (uint32_t nt : threads) {
                for (uint32_t id : irange(nt)) {
                    CAPTURE(nt, id);
                    uint32_t prev     = (id > 0 ? id : nt) - 1;
                    uint32_t next     = (id + 1) % nt;
                    auto     expected = SolverSet{prev, next};
                    CHECK(ParallelSolveOptions::initPeerSet(id, topo, nt) == expected);
                }
            }
        }
        SECTION("cube and cubex") {
            Topology  tCube    = Topology::topo_cube;
            Topology  tCubeX   = Topology::topo_cubex;
            SolverSet nodes[8] = {
                /* 0: */ {1u, 2u, 4u},
                /* 1: */ {0u, 3u, 5u},
                /* 2: */ {0u, 3u, 6u},
                /* 3: */ {1u, 2u, 7u},
                /* 4: */ {0u, 5u, 6u},
                /* 5: */ {1u, 4u, 7u},
                /* 6: */ {2u, 4u, 7u},
                /* 7: */ {3u, 5u, 6u},
            };
            for (uint32_t dim = 0; uint32_t nt : irange(2u, maxT + 1)) {
                bool powerOfTwo  = Potassco::has_single_bit(nt);
                dim             += powerOfTwo;
                for (uint32_t id : irange(nt)) {
                    CAPTURE(nt, id, dim);
                    auto cube  = ParallelSolveOptions::initPeerSet(id, tCube, nt);
                    auto cubeX = ParallelSolveOptions::initPeerSet(id, tCubeX, nt);
                    CHECK_FALSE(cube.contains(id));
                    CHECK_FALSE(cubeX.contains(id));
                    auto cubeBits  = cube.count();
                    auto cubeXBits = cubeX.count();
                    CAPTURE(cubeBits, cubeXBits);
                    if (powerOfTwo) {
                        CHECK(cube == cubeX);
                        CHECK(cubeBits == dim);
                        if (dim == 3) {
                            CHECK(cube == nodes[id]);
                        }
                    }
                    else {
                        if (cubeBits != dim) {
                            auto cubePow = ParallelSolveOptions::initPeerSet(id, tCube, 1 << (dim + 1));
                            cubePow.removeMax(nt);
                            CHECK(cubePow == cube);
                        }
                        CHECK(cube < SolverSet{nt});
                        CHECK(cubeX < SolverSet{nt});
                        CHECK(cubeBits <= cubeXBits);
                    }
                    for (uint32_t o : irange(nt)) {
                        if (cubeX.contains(o)) {
                            auto peerSet = ParallelSolveOptions::initPeerSet(o, tCubeX, nt);
                            CHECK(peerSet.contains(id));
                            peerSet = ParallelSolveOptions::initPeerSet(o, tCube, nt);
                            CHECK(cube.contains(o) == peerSet.contains(id));
                        }
                    }
                }
            }
        }
    }
}
#endif
} // namespace Clasp::Test
