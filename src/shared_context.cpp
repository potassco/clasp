//
// Copyright (c) 2010-present Benjamin Kaufmann
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
#include <clasp/shared_context.h>

#include <clasp/clause.h>
#include <clasp/dependency_graph.h>
#include <clasp/minimize_constraint.h>
#include <clasp/solver.h>
#include <clasp/statistics.h>
#include <clasp/weight_constraint.h>
#if CLASP_HAS_THREADS
#include <clasp/mt/thread.h>
#endif

#include <cstdarg>

namespace Clasp {
#define PS_STATS(APPLY)                                                                                                \
    APPLY(vars, VALUE(vars.num))                                                                                       \
    APPLY(vars_eliminated, VALUE(vars.eliminated))                                                                     \
    APPLY(vars_frozen, VALUE(vars.frozen))                                                                             \
    APPLY(constraints, VALUE(constraints.other))                                                                       \
    APPLY(constraints_binary, VALUE(constraints.binary))                                                               \
    APPLY(constraints_ternary, VALUE(constraints.ternary))                                                             \
    APPLY(acyc_edges, VALUE(acycEdges))                                                                                \
    APPLY(complexity, VALUE(complexity))

#define PS_EXTRA_STATS(APPLY)                                                                                          \
    APPLY(clauses, VALUE(clauses))                                                                                     \
    APPLY(other, VALUE(other))                                                                                         \
    APPLY(clause_lits, VALUE(clLits))                                                                                  \
    APPLY(cardinality_cons, VALUE(weightCons[0].n))                                                                    \
    APPLY(cardinality_lits, VALUE(weightCons[0].lits))                                                                 \
    APPLY(cardinality_bounds, VALUE(weightCons[0].bounds))                                                             \
    APPLY(cardinality_complexity, VALUE(weightCons[0].c))                                                              \
    APPLY(weight_cons, VALUE(weightCons[1].n))                                                                         \
    APPLY(weight_lits, VALUE(weightCons[1].lits))                                                                      \
    APPLY(weight_bounds, VALUE(weightCons[1].bounds))                                                                  \
    APPLY(weight_complexity, VALUE(weightCons[1].c))

#define KEY(X, Y) #X,
static constexpr std::string_view stats_s[]    = {PS_STATS(KEY) "extra"};
static constexpr std::string_view extra_keys[] = {PS_EXTRA_STATS(KEY)};
#undef KEY
auto ProblemStats::size() -> uint32_t { return size32(stats_s); }
auto ProblemStats::Extra::size() -> uint32_t { return size32(extra_keys); }
auto ProblemStats::key(uint32_t i) -> std::string_view {
    POTASSCO_CHECK(i < size(), ERANGE);
    return stats_s[i];
}
auto ProblemStats::Extra::key(uint32_t i) -> std::string_view {
    POTASSCO_CHECK(i < size(), ERANGE);
    return extra_keys[i];
}
#define VALUE(X) StatisticObject::value(&(X))
#define APPLY(x, y)                                                                                                    \
    if (k == #x)                                                                                                       \
        return y;

auto ProblemStats::at(std::string_view k) const -> StatisticObject {
    if (k == "extra") {
        return StatisticObject::map(&this->extra);
    }
    PS_STATS(APPLY)
    POTASSCO_FAIL(ERANGE);
}
auto ProblemStats::Extra::at(std::string_view k) const -> StatisticObject {
    PS_EXTRA_STATS(APPLY)
    POTASSCO_FAIL(ERANGE);
}
#undef VALUE
#undef APPLY
#undef PS_STATS
#undef PS_EXTRA_STATS
/////////////////////////////////////////////////////////////////////////////////////////
// EventHandler
/////////////////////////////////////////////////////////////////////////////////////////
auto Event::nextId() -> uint32_t {
    static uint32_t id = 0;
    return id++;
}
EventHandler::EventHandler(Event::Verbosity verbosity) : verb_(0), sys_(0) {
    if (uint32_t x = verbosity) {
        uint32_t r = (x | (x << 4u) | (x << 8u) | (x << 12u));
        verb_      = static_cast<uint16_t>(r);
    }
}
void EventHandler::setVerbosity(Event::Subsystem sys, Event::Verbosity verb) {
    uint32_t s = static_cast<uint32_t>(sys) << verb_shift;
    uint32_t r = verb_;
    Potassco::store_clear_mask(r, verb_mask << s);
    Potassco::store_set_mask(r, static_cast<uint32_t>(verb) << s);
    verb_ = static_cast<uint16_t>(r);
}
bool EventHandler::setActive(Event::Subsystem sys) {
    if (sys != static_cast<Event::Subsystem>(sys_)) {
        sys_ = static_cast<uint16_t>(sys);
        dispatch(EnterEvent{sys, sys == Event::subsystem_solve ? Event::verbosity_low : Event::verbosity_high});
        return true;
    }
    return false;
}
auto EventHandler::active() const -> Event::Subsystem { return static_cast<Event::Subsystem>(sys_); }
/////////////////////////////////////////////////////////////////////////////////////////
// ShortImplicationsGraph::ImplicationList
/////////////////////////////////////////////////////////////////////////////////////////
ShortImplicationsGraph::ImplicationList::~ImplicationList() { reset(); }
auto ShortImplicationsGraph::ImplicationList::operator=(ImplicationList&& other) noexcept -> ImplicationList& {
    if (this != &other) {
        reset();
        std::memmove(static_cast<void*>(this), static_cast<const void*>(&other), sizeof(ImplicationList));
#if CLASP_HAS_THREADS
        other.learnt.exchange(nullptr);
#endif
        other.cap  = small_cap;
        other.nBin = other.nTern = 0u;
    }
    return *this;
}
void ShortImplicationsGraph::ImplicationList::reset() {
#if CLASP_HAS_THREADS
    resetLearnt();
#endif
    if (cap != small_cap) {
        Potassco::SystemAllocator::deallocate(data());
    }
    cap  = small_cap;
    nBin = nTern = 0u;
}
void ShortImplicationsGraph::ImplicationList::shrink() {
    if (cap != small_cap && used() <= small_cap) {
        auto* b = data();
        auto* t = tern() - nTern;
        if (nBin) {
            std::memcpy(static_cast<void*>(small), b, nBin * sizeof(Literal));
        }
        if (nTern) {
            auto* x = reinterpret_cast<Tern*>(small + small_cap);
            std::memcpy(static_cast<void*>(x - nTern), static_cast<const void*>(t), nTern * sizeof(Tern));
        }
        Potassco::SystemAllocator::deallocate(b);
        cap = small_cap;
    }
}
void ShortImplicationsGraph::ImplicationList::grow() {
    auto nc = saturating_mul(cap, 3u) >> 1u;
    POTASSCO_CHECK(nc > cap, Potassco::Errc::length_error, "ImplicationList");
    auto bytes = Potassco::SystemAllocator::goodAllocSize(nc * sizeof(Literal));
    nc         = bytes / sizeof(Literal);
    auto* mem  = static_cast<Literal*>(Potassco::SystemAllocator::allocate(bytes));
    if (nBin) {
        std::memcpy(static_cast<void*>(mem), static_cast<const void*>(data()), nBin * sizeof(Literal));
    }
    if (nTern) {
        auto* t = reinterpret_cast<Tern*>(mem + nc);
        std::memcpy(static_cast<void*>(t - nTern), static_cast<const void*>(tern() - nTern), nTern * sizeof(Tern));
    }
    if (cap != small_cap) {
        Potassco::SystemAllocator::deallocate(data());
    }
    std::memcpy(static_cast<void*>(small + pad), static_cast<const void*>(&mem), sizeof(Literal*));
    cap = nc;
    assert(data() == mem);
}

void ShortImplicationsGraph::ImplicationList::addBin(Literal p) {
    if (used() == cap) {
        grow();
    }
    data()[nBin++] = p;
}

void ShortImplicationsGraph::ImplicationList::addTern(const Tern& t) {
    if ((cap - used()) < 2u) {
        grow();
    }
    ++nTern;
    auto* pos = tern() - nTern;
    new (pos) Tern(t);
}

void ShortImplicationsGraph::ImplicationList::removeBin(Literal p) {
    for (auto* d = data(); auto i : irange(nBin)) {
        if (d[i] == p) {
            d[i] = d[--nBin];
            return;
        }
    }
}
void ShortImplicationsGraph::ImplicationList::removeTern(Literal p) {
    for (auto *d = tern(), *e = d - nTern; d != e;) {
        if (const auto& t = *--d; t[0] == p || t[1] == p) {
            *d = *e;
            --nTern;
            return;
        }
    }
}
void ShortImplicationsGraph::ImplicationList::removeTern(const Tern& x) {
    auto needle = std::minmax(x[0], x[1]);
    for (auto *d = tern(), *e = d - nTern; d != e;) {
        if (const auto& t = *--d; std::minmax(t[0], t[1]) == needle) {
            *d = *e;
            --nTern;
            return;
        }
    }
}
#if CLASP_HAS_THREADS
ShortImplicationsGraph::Block::Block(uint32_t cap, Block* n, const Literal* x, uint32_t xs)
    : next_(n)
    , cap_(cap)
    , size_(xs) {
    std::copy_n(x, xs, data_);
}
auto ShortImplicationsGraph::Block::create(Block* n, const Literal* x, uint32_t xs) -> Block* {
    auto nc    = 12u;
    auto bytes = sizeof(Block) + nc * sizeof(Literal);
    if (n) {
        nc    = n->cap() + (n->next() ? n->next()->cap() : nc);
        bytes = Potassco::SystemAllocator::goodAllocSize(sizeof(Block) + nc * sizeof(Literal));
        nc    = toU32((bytes - sizeof(Block)) / sizeof(Literal));
    }
    return new (Potassco::SystemAllocator::allocate(bytes)) Block(nc, n, x, xs);
}
void ShortImplicationsGraph::Block::destroy(Block* b) {
    b->~Block();
    Potassco::SystemAllocator::deallocate(b);
}
bool ShortImplicationsGraph::Block::tryLock(uint32_t& size) { return size_.try_lock(&size); }
bool ShortImplicationsGraph::Block::addUnlock(uint32_t lockedSize, const Literal* x, uint32_t xs) {
    if ((lockedSize + xs) <= cap_) {
        std::copy_n(x, xs, data_ + lockedSize);
        size_.store_unlock(lockedSize + xs);
        return true;
    }
    return false;
}
void ShortImplicationsGraph::ImplicationList::resetLearnt(bool merge) {
    for (Block* x = learnt.exchange(nullptr, std::memory_order_acquire); x;) {
        if (merge) {
            for (auto imp = x->begin(), endOf = x->end(); imp != endOf;) {
                auto sz = 2u - imp->flagged();
                if (sz == 1u) {
                    addBin(imp[0]);
                }
                else {
                    addTern({Literal(imp[0]).flag(), imp[1]});
                }
                imp += sz;
            }
        }
        Block* t = std::exchange(x, x->next());
        Block::destroy(t);
    }
}

bool ShortImplicationsGraph::ImplicationList::addLearnt(Literal q, Literal r, bool allowFail) {
    Literal  nc[2] = {q, r};
    uint32_t ns    = 1 + not isSentinel(r);
    nc[ns - 1].flag(); // mark end of clause
    do {
        if (auto* x = learnt.load(); x == nullptr) {
            auto* n = Block::create(nullptr, nc, ns);
            if (learnt.compare_exchange_strong(x, n)) {
                return true; // won the race and published our block as first block
            }
            // some other thread published the first block
            Block::destroy(n);
        }
        else if (uint32_t lockedSize; x->tryLock(lockedSize)) [[likely]] {
            if (not x->addUnlock(lockedSize, nc, ns)) {
                auto* t = Block::create(x, nc, ns); // x is full and remains locked forever
                learnt.store(t);                    // publish new (unlocked) block
            }
            return true;
        }
        else {
            // some other thread is currently adding to this list...
            mt::this_thread::yield();
        }
    } while (allowFail);
    return false;
}

bool ShortImplicationsGraph::ImplicationList::hasLearnt(Literal q, Literal r) const {
    return not forEachLearnt(lit_true, [&, binary = isSentinel(r)](Literal, Literal q0, Literal r0) {
        if (q0 == q || q0 == r) {
            // binary clause subsumes new bin/tern clause
            if (r0 == lit_false) {
                return false;
            }
            // existing ternary clause subsumes new tern clause
            if (not binary && (r0 == q || r0 == r)) {
                return false;
            }
        }
        return true;
    });
}
#endif
static void mergeLearnt(auto& w) {
    if constexpr (requires { w.resetLearnt(true); }) {
        w.resetLearnt(true);
    }
}
/////////////////////////////////////////////////////////////////////////////////////////
// ShortImplicationsGraph
/////////////////////////////////////////////////////////////////////////////////////////
ShortImplicationsGraph::~ShortImplicationsGraph() = default;
void ShortImplicationsGraph::resize(uint32_t nodes) {
    if (nodes > cap_) {
        assert((UINT32_MAX - nodes) >= 2);
        auto nc = std::max(cap_ ? nodes + nodes / 2 : 16u, nodes + 2);
        auto t  = std::make_unique<ImplicationList[]>(nc);
        if (size_) {
            std::copy_n(std::make_move_iterator(graph_.get()), size_, t.get());
        }
        graph_ = std::move(t);
        cap_   = nc;
    }
    else if (nodes < size()) {
        for (auto *it = graph_.get() + nodes, *oldEnd = graph_.get() + size(); it != oldEnd; ++it) {
            if (not it->empty()) {
                it->reset();
            }
        }
    }
    size_ = nodes;
}

auto ShortImplicationsGraph::numEdges(Literal p) const -> uint32_t { return graph_[p.id()].size(); }

bool ShortImplicationsGraph::add(LitView lits, bool learnt) {
    POTASSCO_ASSERT(lits.size() > 1 && lits.size() < 4);
    bool    tern = lits.size() == 3u;
    Literal p = lits[0], q = lits[1], r = (tern ? lits[2] : lit_false);
    p.unflag(), q.unflag(), r.unflag();
    if (not shared_) {
        bool simp = simp_ == ContextParams::simp_all || (learnt && simp_ == ContextParams::simp_learnt);
        if (simp && contains(getList(~p).binView(), q)) {
            return false;
        }
        if (learnt) {
            p.flag(), q.flag(), r.flag();
        }
        if (not tern) {
            getList(~p).addBin(q);
            getList(~q).addBin(p);
        }
        else {
            if (simp) {
                if (contains(getList(~p).binView(), r)) {
                    return false;
                }
                if (contains(getList(~q).binView(), r)) {
                    return false;
                }
                for (auto mm = std::minmax(q, r); auto [x, y] : getList(~p).ternView()) {
                    if (mm == std::minmax(x, y)) {
                        return false;
                    }
                }
            }
            getList(~p).addTern({q, r});
            getList(~q).addTern({p, r});
            getList(~r).addTern({p, q});
        }
        uint32_t& stats = (tern ? tern_ : bin_)[learnt];
        ++stats;
        return true;
    }
#if CLASP_HAS_THREADS
    if (learnt) {
        if (q < p) {
            std::swap(q, p);
        }
        if (tern) {
            if (r < p) {
                std::swap(r, p);
            }
            if (r < q) {
                std::swap(r, q);
            }
        }
        while (not getList(~p).hasLearnt(q, r) && (not tern || not getList(~q).hasLearnt(p, r))) {
            if (getList(~p).addLearnt(q, r, false)) {
                getList(~q).addLearnt(p, r, true);
                if (tern) {
                    getList(~r).addLearnt(p, q, true);
                }
                mt::AtomicRef<uint32_t> stats((tern ? tern_ : bin_)[1]);
                std::ignore = stats.fetch_add(1u, mt::memory_order_relaxed);
                return true;
            }
        }
    }
#endif
    return false;
}
void ShortImplicationsGraph::remove(LitView lits, bool learnt) {
    assert(not shared_);
    bool     tern  = lits.size() == 3u;
    auto&    stats = (tern ? tern_ : bin_)[learnt];
    unsigned i = 0, rem = 0;
    for (auto x : lits) {
        auto& w = getList(~x);
        mergeLearnt(w);
        auto sz = w.size();
        if (not tern) {
            w.removeBin(lits[1 - i]);
        }
        else {
            w.removeTern({lits[(i + 1) % 3], lits[(i + 2) % 3]});
        }
        rem += sz != w.size();
        w.shrink();
        ++i;
    }
    if (rem) {
        --stats;
    }
}

void ShortImplicationsGraph::removeBin(Literal other, Literal sat) {
    --bin_[other.flagged()];
    auto& w = getList(~other);
    mergeLearnt(w);
    w.removeBin(sat);
    w.shrink();
}

void ShortImplicationsGraph::removeTern(const Solver& s, const Tern& t, Literal p) {
    assert(s.value(p.var()) != value_free);
    --tern_[t[0].flagged()];
    for (auto lit : t) {
        auto& w = getList(~lit);
        mergeLearnt(w);
        w.removeTern(p);
        w.shrink();
    }
    if (s.isFalse(p) && s.value(t[0].var()) == value_free && s.value(t[1].var()) == value_free) {
        // clause is binary on dl 0
        add(t, t[0].flagged());
    }
    // else: clause is SAT
}
// Removes all binary clauses containing p - those are now SAT.
// Binary clauses containing ~p are unit and therefore likewise SAT. Those
// are removed when their second literal is processed.
//
// Ternary clauses containing p are SAT and therefore removed.
// Ternary clauses containing ~p are now either binary or SAT. Those that
// are SAT are removed when the satisfied literal is processed.
// All conditional binary clauses are replaced with real binary clauses.
// Note: clauses containing p watch ~p. Those containing ~p watch p.
void ShortImplicationsGraph::removeTrue(const Solver& s, Literal p) {
    POTASSCO_ASSERT(not shared_);
    auto& negPList = getList(~p);
    auto& pList    = getList(p);
    mergeLearnt(negPList);
    mergeLearnt(pList);
    // remove every binary clause containing p -> clause is satisfied
    for (auto x : negPList.binView()) { removeBin(x, p); }
    // remove every ternary clause containing p -> clause is satisfied
    for (const auto& t : negPList.ternView()) { removeTern(s, t, p); }
    // transform ternary clauses containing ~p to binary clause
    for (const auto& t : pList.ternView()) { removeTern(s, t, ~p); }
    negPList.reset();
    pList.reset();
}

bool ShortImplicationsGraph::propagate(Solver& s, Literal p) const {
    return forEach(p, [&s]<typename T>(Literal p0, Literal q, T r) {
        if constexpr (std::is_same_v<T, Unary_t>) {
            return s.isTrue(q) || s.force(q, Antecedent(p0));
        }
        else {
            if (auto vq = s.value(q.var()); vq) {
                return vq == trueValue(q) || s.isTrue(r) || s.force(r, Antecedent(p0, ~q));
            }
            return not s.isFalse(r) || s.force(q, Antecedent(p0, ~r));
        }
    });
}
bool ShortImplicationsGraph::reverseArc(const Solver& s, Literal p, uint32_t maxLev, Antecedent& out) const {
    return not forEach(p, [&]<typename T>(Literal, Literal q, T r) {
        if (not isRevLit(s, q, maxLev)) {
            return true;
        }
        if constexpr (std::is_same_v<T, Unary_t>) {
            out = Antecedent(~q);
            return false;
        }
        else {
            if (not isRevLit(s, r, maxLev)) {
                return true;
            }
            out = Antecedent(~q, ~r);
            return false;
        }
    });
}
bool ShortImplicationsGraph::propagateBin(Assignment& out, Literal p, uint32_t level) const {
    for (const auto& lit : graph_[p.id()].binView()) {
        if (not out.assign(lit, level, p)) {
            return false;
        }
    }
    return true;
}
/////////////////////////////////////////////////////////////////////////////////////////
// SatPreprocessor
/////////////////////////////////////////////////////////////////////////////////////////
SatPreprocessor::SatPreprocessor() : ctx_(nullptr), elimTop_(nullptr), seen_(1, 1) {}
SatPreprocessor::~SatPreprocessor() { discardClauses(elimTop_); }
void SatPreprocessor::discardClauses(Clause* top) {
    for (auto destroy = OwnedPtr::deleter_type{}; auto* clause : clauses_) { destroy(clause); }
    discardVec(clauses_);
    while (top) {
        OwnedPtr t{top};
        top = top->next();
    }
}
void SatPreprocessor::reportProgress(Progress::EventOp id, uint32_t curr, uint32_t max) {
    ctx().report(Progress(this, id, curr, max));
}
bool SatPreprocessor::addClause(LitView clause) {
    if (clause.empty()) {
        return false;
    }
    clause.size() > 1 ? clauses_.push_back(Clause::newClause(clause)) : units_.push_back(clause[0]);
    return true;
}

bool SatPreprocessor::attachClauses(bool propagate) {
    auto& s = *ctx_->master();
    auto  j = attached_;
    s.acquireProblemVars();
    for (Clause*& clause : drop(clauses_, attached_)) {
        OwnedPtr c{std::exchange(clause, nullptr)};
        POTASSCO_ASSERT(c);
        c->simplify(s);
        if (Literal x = (*c)[0]; c->size() > 1 && s.value(x.var()) == value_free) {
            clauses_[j++] = c.release();
        }
        else if (not ctx_->addUnary(x)) {
            return false;
        }
    }
    truncateVec(clauses_, j);
    auto newRange = Range32{std::exchange(attached_, j), j};
    return s.propagate() && doAttachClauses(newRange, propagate);
}
void SatPreprocessor::freezeSeen() {
    if (not ctx_->validVar(seen_.lo)) {
        seen_.lo = 1;
    }
    if (not ctx_->validVar(seen_.hi)) {
        seen_.hi = ctx_->numVars() + 1;
    }
    for (auto v : irange(seen_.lo, seen_.hi)) {
        assert(v >= seen_.lo && v < seen_.hi);
        if (not ctx_->eliminated(v)) {
            ctx_->setFrozen(v, true);
        }
    }
    seen_.lo = seen_.hi;
}
bool SatPreprocessor::addUnits() {
    if (std::ranges::all_of(units_, [this](Literal x) { return ctx_->addUnary(x); })) {
        units_.clear();
        return true;
    }
    return false;
}

bool SatPreprocessor::preprocess(SharedContext& ctx, Options& opts) {
    ctx_      = &ctx;
    Solver* s = ctx_->master();
    POTASSCO_SCOPE_EXIT({
        seen_.hi = ctx_->numVars() + 1;
        discardClauses(nullptr);
        ctx_      = nullptr;
        attached_ = 0;
        doCleanUp();
    });
    // skip preprocessing if other constraints are UNSAT
    if (not addUnits() || not s->propagate()) {
        return false;
    }
    if (ctx.preserveModels()) {
        opts.disableBce();
    }
    if (ctx.preserveShown()) {
        for (const auto& pred : ctx.output.pred_range()) { ctx.setFrozen(pred.cond.var(), true); }
        for (auto v : ctx.output.vars_range()) { ctx.setFrozen(v, true); }
    }
    if (ctx.preserveHeuristic()) {
        for (const auto& x : ctx.heuristic) {
            if (not ctx.master()->isFalse(x.cond())) {
                ctx.setFrozen(x.var(), true);
            }
        }
        DomainTable::applyDefault(
            ctx, [&ctx](Literal p, HeuParams::DomPref, uint32_t) { ctx.setFrozen(p.var(), true); },
            ctx.defaultDomPref());
    }

    // preprocess only if not too many vars are frozen or not too many clauses
    if (opts.type != 0 && not opts.clauseLimit(numClauses()) && not opts.frozenLimit(ctx) && initPreprocess(opts)) {
        reportProgress(Progress::event_enter, 0, 100);
        POTASSCO_SCOPE_EXIT({ reportProgress(Progress::event_exit, 100, 100); });
        freezeSeen();
        // remove SAT clauses, strengthen clauses w.r.t false literals, attach, and preprocess clauses
        if (not attachClauses(false) || not doPreprocess()) {
            return false;
        }
    }
    // simplify other constraints w.r.t any newly derived top-level facts
    if (not s->simplify()) {
        return false;
    }
    // move preprocessed clauses to ctx
    for (Clause*& c : clauses_) {
        if (auto clause = OwnedPtr{std::exchange(c, nullptr)}; clause && not clause->addTo(*s)) {
            return false;
        }
    }
    discardVec(clauses_);
    return true;
}
bool SatPreprocessor::propagate(SharedContext& ctx) {
    POTASSCO_ASSERT(ctx_ == nullptr || ctx_ == &ctx);
    if (std::exchange(ctx_, &ctx) == nullptr) {
        POTASSCO_SCOPE_EXIT({ ctx_ = nullptr; });
        return addUnits() && ctx.master()->propagate() && attachClauses(true);
    }
    return true;
}
bool SatPreprocessor::preprocess(SharedContext& ctx) {
    SatPreParams opts = ctx.configuration()->context().satPre;
    return preprocess(ctx, opts);
}
void SatPreprocessor::extendModel(ValueVec& m, LitVec& open) {
    if (not open.empty()) {
        // flip last unconstrained variable to get "next" model
        open.back() = ~open.back();
    }
    doExtendModel(elimTop_, m, open);
    // remove unconstrained vars already flipped
    while (not open.empty() && open.back().sign()) { open.pop_back(); }
}
auto SatPreprocessor::Clause::newClause(LitView lits) -> Clause* {
    assert(not lits.empty());
    void* mem = ::operator new(sizeof(Clause) + (lits.size() - 1) * sizeof(Literal));
    return new (mem) Clause(lits.data(), size32(lits));
}
SatPreprocessor::Clause::Clause(const Literal* lits, uint32_t size) : size_(size), inQ_(0), marked_(0) {
    std::memcpy(lits_, lits, size * sizeof(Literal));
}
void SatPreprocessor::Clause::strengthen(Literal p) {
    uint64_t a = 0;
    uint32_t i;
    for (i = 0; lits_[i] != p; ++i) { a |= abstractLit(lits_[i]); }
    for (uint32_t end = size_ - 1; i < end; ++i) {
        lits_[i]  = lits_[i + 1];
        a        |= abstractLit(lits_[i]);
    }
    --size_;
    data_.abstr = a;
}
void SatPreprocessor::Clause::simplify(Solver& s) {
    uint32_t i;
    for (i = 0; i != size_ && s.value(lits_[i].var()) == value_free; ++i) { ; }
    if (i == size_) {
        return;
    }
    if (s.isTrue(lits_[i])) {
        std::swap(lits_[i], lits_[0]);
        return;
    }
    uint32_t j = i++;
    for (; i != size_; ++i) {
        if (s.isTrue(lits_[i])) {
            std::swap(lits_[i], lits_[0]);
            return;
        }
        if (not s.isFalse(lits_[i])) {
            lits_[j++] = lits_[i];
        }
    }
    size_ = j;
}
bool SatPreprocessor::Clause::addTo(Solver& s) {
    return ClauseCreator::create(s, ClauseRep::create({lits_, size_}), {}).ok();
}

void SatPreprocessor::Clause::destroy() {
    void* mem = this;
    this->~Clause();
    ::operator delete(mem);
}
/////////////////////////////////////////////////////////////////////////////////////////
// OutputTable
/////////////////////////////////////////////////////////////////////////////////////////
OutputTable::OutputTable() : vars_(0, 0), projMode_(ProjectMode::implicit), hide_(0) {}
OutputTable::~OutputTable() {
    while (not theories_.empty()) {
        if (theories_.back().test<0>()) {
            delete theories_.back().get();
        }
        theories_.pop_back();
    }
}
void OutputTable::setFilter(char c) { hide_ = c; }
bool OutputTable::filter(const std::string_view& n) const { return n.empty() || n.starts_with(hide_); }
auto OutputTable::filter(uint32_t startPos) -> uint32_t {
    auto it = std::remove_if(preds_.begin() + std::min(startPos, numPreds()), preds_.end(), [this](PredType& p) {
        if (filter(p.name.view()) || p.cond == lit_false) {
            auto expire = std::move(p.name);
            return true;
        }
        return false;
    });
    return truncateVec(preds_, it);
}
void OutputTable::add(const std::string_view& n, Literal c, uint32_t u) { preds_.push_back({NameType(n), c, u}); }
void OutputTable::add(Theory& t) {
    theories_.push_back(TheoryPtr(&t));
    POTASSCO_ASSERT(not theories_.back().test<0>());
}
void OutputTable::add(std::unique_ptr<Theory> t) {
    theories_.push_back(TheoryPtr(t.get()));
    theories_.back().set<0>();
    std::ignore = t.release(); // we own the pointer at this point
    POTASSCO_ASSERT(theories_.back().test<0>());
}
bool OutputTable::remove(Theory& t) {
    return erase_if(theories_, [p = &t](TheoryPtr ptr) { return ptr.get() == p; }) != 0;
}
void OutputTable::setVarRange(const Range32& r) { vars_ = r; }
void OutputTable::setProjectMode(ProjectMode m) { projMode_ = m; }
void OutputTable::addProject(Literal x) { proj_.push_back(x); }
void OutputTable::clearProject() { proj_.clear(); }
void OutputTable::setPredicateCondition(uint32_t n, Literal cond) { preds_.at(n).cond = cond; }
auto OutputTable::size() const -> uint32_t { return numPreds() + numVars(); }
OutputTable::Theory::~Theory() = default;
/////////////////////////////////////////////////////////////////////////////////////////
// DomainTable
/////////////////////////////////////////////////////////////////////////////////////////
DomainTable::ValueType::ValueType(Var_t v, DomModType t, int16_t bias, uint16_t prio, Literal cond)
    : cond_(cond.id())
    , comp_(t == DomModType::true_ || t == DomModType::false_)
    , var_(v)
    , type_(t <= 3u ? +t : static_cast<uint32_t>(t == DomModType::false_))
    , bias_(bias)
    , prio_(prio) {}
auto DomainTable::ValueType::type() const -> DomModType {
    return static_cast<DomModType>(comp_ == 0 ? type_ : +DomModType::true_ + type_);
}
DomainTable::DomainTable() : assume(nullptr), seen_(0) {}
void DomainTable::add(Var_t v, DomModType t, int16_t b, uint16_t p, Literal c) {
    if (c != lit_false && (t != DomModType::init || c == lit_true)) {
        entries_.push_back(ValueType(v, t, b, p, c));
    }
}
auto DomainTable::simplify() -> uint32_t {
    if (seen_ >= size()) {
        return size();
    }
    std::stable_sort(entries_.begin() + seen_, entries_.end(), [](const ValueType& lhs, const ValueType& rhs) {
        return lhs.cond() < rhs.cond() || (lhs.cond() == rhs.cond() && lhs.var() < rhs.var());
    });
    auto j = entries_.begin() + seen_;
    for (DomVec::const_iterator it = j, end = entries_.end(), n; it != end; it = n) {
        auto    v = it->var();
        Literal c = it->cond();
        for (n = it + 1; n != end && n->var() == v && n->cond() == c;) { ++n; }
        if ((n - it) == 1) {
            *j++ = *it;
        }
        else {
            static_assert(DomModType::level == 0 && DomModType::sign == 1 && DomModType::true_ == 4,
                          "check enumeration constants");
            static constexpr auto    n_simp    = 4u;
            static constexpr auto    mod_level = +DomModType::level, mod_sign = +DomModType::sign;
            static constexpr int16_t no_bias      = INT16_MAX;
            uint16_t                 prio[n_simp] = {0, 0, 0, 0};
            int16_t                  bias[n_simp] = {no_bias, no_bias, no_bias, no_bias};
            for (; it != n; ++it) {
                if (not it->comp() && it->prio() >= prio[+it->type()]) {
                    bias[+it->type()] = it->bias();
                    prio[+it->type()] = it->prio();
                }
                else if (it->comp()) {
                    if (it->prio() >= prio[mod_level]) {
                        bias[mod_level] = it->bias();
                        prio[mod_level] = it->prio();
                    }
                    if (it->prio() >= prio[mod_sign]) {
                        bias[mod_sign] = it->type() == DomModType::true_ ? 1 : -1;
                        prio[mod_sign] = it->prio();
                    }
                }
            }
            int s = 0;
            if (bias[mod_level] != no_bias && bias[mod_sign] != no_bias && bias[mod_sign] &&
                prio[mod_level] == prio[mod_sign]) {
                *j++ = ValueType(v, bias[mod_sign] > 0 ? DomModType::true_ : DomModType::false_, bias[mod_level],
                                 prio[mod_level], c);
                s    = mod_sign + 1;
            }
            for (int t = s; t != n_simp; ++t) {
                if (bias[t] != no_bias) {
                    *j++ = ValueType(v, static_cast<DomModType>(t), bias[t], prio[t], c);
                }
            }
        }
    }
    if (truncateVec(entries_, j) > 2 && entries_.capacity() > static_cast<std::size_t>(entries_.size() * 1.75)) {
        entries_.shrink_to_fit();
    }
    return (seen_ = size());
}
void DomainTable::reset() {
    discardVec(entries_);
    assume = nullptr;
    seen_  = 0;
}
void DomainTable::applyDefault(const SharedContext& ctx, const DefaultAction& act, uint32_t defFilter) {
    if (not act) {
        return;
    }

    if ((defFilter & HeuParams::pref_show) != 0 || not defFilter) {
        auto pref = defFilter ? HeuParams::pref_show : HeuParams::pref_atom;
        auto vars = defFilter ? ctx.output.vars_range() : ctx.vars();
        for (const auto& pred : ctx.output.pred_range()) {
            if (defFilter ||
                (pred.cond.sign() && pred.user && Potassco::atom(Potassco::lit(pred.user)) < Asp::PrgNode::no_node)) {
                act(pred.cond, pref, pref);
            }
        }
        for (auto v : vars) {
            if (ctx.varInfo(v).atom()) {
                act(posLit(v), pref, pref);
            }
        }
    }
    if ((defFilter & HeuParams::pref_min) != 0 && ctx.minimizeNoCreate()) {
        Weight_t lastW = -1;
        uint32_t strat = HeuParams::pref_show;
        for (const auto& wl : *ctx.minimizeNoCreate()) {
            if (wl.weight != lastW && strat > HeuParams::pref_disj) {
                --strat;
                lastW = wl.weight;
            }
            act(wl.lit, HeuParams::pref_min, strat);
        }
    }
    const auto gs = static_cast<uint32_t>(HeuParams::pref_scc | HeuParams::pref_hcc | HeuParams::pref_disj) & defFilter;
    if (ctx.sccGraph.get() && gs && ((gs & HeuParams::pref_scc) != 0 || ctx.sccGraph->numNonHcfs())) {
        for (auto i : irange(ctx.sccGraph->numAtoms())) {
            const PrgDepGraph::AtomNode& a = ctx.sccGraph->getAtom(i);
            if ((gs & HeuParams::pref_disj) != 0 && a.inDisjunctive()) {
                act(a.lit, HeuParams::pref_disj, 3u);
            }
            else if ((gs & HeuParams::pref_hcc) != 0 && a.inNonHcf()) {
                act(a.lit, HeuParams::pref_hcc, 2u);
            }
            else if ((gs & HeuParams::pref_scc) != 0) {
                act(a.lit, HeuParams::pref_scc, 1u);
            }
        }
    }
}
bool DomainTable::empty() const { return entries_.empty(); }
auto DomainTable::size() const -> uint32_t { return size32(entries_); }
auto DomainTable::begin() const -> iterator { return entries_.begin(); }
auto DomainTable::end() const -> iterator { return entries_.end(); }
/////////////////////////////////////////////////////////////////////////////////////////
// SharedContext::Minimize
/////////////////////////////////////////////////////////////////////////////////////////
struct SharedContext::Minimize {
    using ProductPtr = std::unique_ptr<SharedMinimizeData, ReleaseObject>;
    void               add(Weight_t p, const WeightLiteral& lit) { builder.add(p, lit); }
    [[nodiscard]] bool reset() const {
        if (product.get()) {
            product->resetBounds();
        }
        return true;
    }
    auto get(SharedContext& ctx) -> SharedMinimizeData* {
        if (builder.empty()) {
            return product.get();
        }
        if (product) {
            builder.add(*product);
            product = nullptr;
        }
        product.reset(builder.build(ctx));
        return product.get();
    }
    MinimizeBuilder builder;
    ProductPtr      product;
};
/////////////////////////////////////////////////////////////////////////////////////////
// SharedContext
/////////////////////////////////////////////////////////////////////////////////////////
static BasicSatConfig g_config_def;
SharedContext::SharedContext() : mini_(nullptr), progress_(nullptr), lastTopLevel_(0) {
    static_assert(sizeof(Share) == sizeof(uint32_t), "unexpected size");
    // sentinel is always present
    setFrozen(addVar(VarType::atom, 0), true);
    stats_.vars.num = 0;
    config_         = &g_config_def;
    pushSolver();
}
auto SharedContext::defaultDomPref() const -> uint32_t {
    const SolverParams& sp = config_->solver(0);
    return sp.heuId == HeuristicType::domain && sp.heuristic.domMod != HeuParams::mod_none ? sp.heuristic.domPref
                                                                                           : Potassco::set_bit(0u, 31);
}
bool SharedContext::ok() const {
    return master()->decisionLevel() || not master()->hasConflict() || master()->hasStopConflict();
}
void SharedContext::enableStats(uint32_t lev) {
    if (lev > 0) {
        master()->stats.enableExtended();
    }
}
SharedContext::~SharedContext() {
    while (not solvers_.empty()) {
        delete solvers_.back();
        solvers_.pop_back();
    }
}

void SharedContext::reset() {
    this->~SharedContext();
    new (this) SharedContext();
}

void SharedContext::setConcurrency(uint32_t n, ResizeMode mode) {
    auto prev    = share_.count;
    share_.count = std::max(n, static_cast<uint32_t>(1));
    solvers_.reserve(share_.count);
    while (size32(solvers_) < share_.count && Potassco::test(mode, resize_push)) { pushSolver(); }
    while (size32(solvers_) > share_.count && Potassco::test(mode, resize_pop)) {
        delete solvers_.back();
        solvers_.pop_back();
    }
    if ((share_.shareM & ContextParams::share_auto) != 0) {
        setShareMode(ContextParams::share_auto);
    }
    if (prev != share_.count && sccGraph) {
        for (auto* c : sccGraph->nonHcfs()) { c->setGeneratorConcurrency(share_.count); }
    }
}

void SharedContext::setShareMode(ContextParams::ShareMode m) {
    if (share_.shareM = static_cast<uint32_t>(m); m == ContextParams::share_auto && share_.count > 1) {
        share_.shareM |= static_cast<uint32_t>(ContextParams::share_all);
    }
}
void SharedContext::setShortMode(ContextParams::ShortMode m, ContextParams::ShortSimpMode x) {
    share_.shortM = static_cast<uint32_t>(m);
    btig_.setSimpMode(x);
}

void SharedContext::setPreproMode(uint32_t m, bool b) {
    share_.satPreM &= ~m;
    if (b) {
        share_.satPreM |= m;
    }
}

auto SharedContext::pushSolver() -> Solver& {
    auto id      = size32(solvers_);
    share_.count = std::max(share_.count, id + 1);
    auto* s      = new Solver(this, id);
    solvers_.push_back(s);
    return *s;
}

void SharedContext::setConfiguration(Configuration* c) {
    auto* nc            = c ? c : &g_config_def;
    auto  configChanged = config_ != nc;
    config_             = nc;
    if (configChanged) {
        config_->prepare(*this);
        const ContextParams& opts = config_->context();
        setShareMode(static_cast<ContextParams::ShareMode>(opts.shareMode));
        setShortMode(static_cast<ContextParams::ShortMode>(opts.shortMode),
                     static_cast<ContextParams::ShortSimpMode>(opts.shortSimp));
        share_.seed = opts.seed;
        if (satPrepro.get() == nullptr && opts.satPre.type != SatPreParams::sat_pre_no) {
            satPrepro.reset(SatPreParams::create(opts.satPre));
        }
        enableStats(opts.stats);
        // force update on next call to Solver::startInit()
        for (auto* s : solvers_) { s->resetConfig(); }
    }
}

bool SharedContext::unfreeze() {
    if (frozen()) {
        share_.frozen    = 0;
        share_.winner    = 0;
        heuristic.assume = nullptr;
        btig_.markShared(false);
        return master()->popRootLevel(master()->rootLevel()) &&
               btig_.propagate(*master(), lit_true) // any newly learnt facts
               && unfreezeStep() && (not mini_ || mini_->reset());
    }
    return true;
}

bool SharedContext::unfreezeStep() {
    POTASSCO_ASSERT(not frozen());
    auto tag = step_.var();
    for (auto i = size32(solvers_); i--;) {
        Solver& s = *solvers_[i];
        if (not s.validVar(tag)) {
            continue;
        }
        s.endStep(lastTopLevel_, configuration()->solver(s.id()));
    }
    if (tag) {
        if (not validVar(tag + 1)) {
            // the step literal was added last - drop it from the problem/assignment
            varInfo_[tag] = VarInfo();
            popVars(1);
            ++stats_.vars.num;
        }
        else {
            POTASSCO_ASSERT(master()->isFalse(step_), "step literal must be false after endStep");
        }
        step_ = lit_false; // request a new step literal for the next step
    }
    return not master()->hasConflict();
}

auto SharedContext::addVars(uint32_t nVars, VarType t, uint8_t flags) -> Var_t {
    static constexpr auto flags_for = [](VarType in) {
        switch (in) {
            default             : return static_cast<VarInfo::Flag>(0);
            case VarType::body  : return VarInfo::flag_body;
            case VarType::hybrid: return VarInfo::flag_eq;
        }
    };
    Potassco::store_clear_mask(flags, VarInfo::flag_pos | VarInfo::flag_neg);
    Potassco::store_set_mask(flags, flags_for(t));
    appendVec(varInfo_, nVars, VarInfo(flags));
    stats_.vars.num += nVars;
    return static_cast<Var_t>(varInfo_.size() - nVars);
}

void SharedContext::popVars(uint32_t nVars) {
    POTASSCO_CHECK_PRE(not frozen(), "Cannot pop vars from frozen program");
    POTASSCO_CHECK_PRE(nVars <= numVars(), "Too many variables to pop");
    uint32_t newVars = numVars() - nVars;
    uint32_t comVars = master()->numVars();
    if (newVars >= comVars) {
        // pop any vars not yet committed
        truncateVec(varInfo_, varInfo_.end() - nVars);
        stats_.vars.num -= nVars;
    }
    else {
        for (Var_t v = numVars(); v && nVars; --nVars, --v) {
            stats_.vars.eliminated -= eliminated(v);
            stats_.vars.frozen     -= varInfo(v).frozen();
            --stats_.vars.num;
            varInfo_.pop_back();
        }
        btig_.resize((numVars() + 1) << 1u);
        for (auto i = size32(solvers_); i--;) { solvers_[i]->updateVars(); }
        lastTopLevel_ = std::min(lastTopLevel_, master()->assign_.front);
    }
}

void SharedContext::setSolveMode(SolveMode m) { share_.solveM = m; }
void SharedContext::requestStepVar() {
    if (step_ == lit_true) {
        step_ = lit_false;
    }
}
auto SharedContext::requireStepVar() -> Literal {
    if (isSentinel(step_)) {
        VarInfo nv;
        nv.set(VarInfo::flag_frozen);
        step_ = posLit(size32(varInfo_));
        varInfo_.push_back(nv);
        btig_.resize((numVars() + 1) << 1u);
    }
    return step_;
}

void SharedContext::setFrozen(Var_t v, bool b) {
    assert(validVar(v));
    if (v && b != varInfo_[v].has(VarInfo::flag_frozen)) {
        varInfo_[v].toggle(VarInfo::flag_frozen);
        b ? ++stats_.vars.frozen : --stats_.vars.frozen;
    }
}

bool SharedContext::eliminated(Var_t v) const {
    assert(validVar(v));
    return not master()->assign_.valid(v);
}

void SharedContext::eliminate(Var_t v) {
    assert(validVar(v) && not frozen() && master()->decisionLevel() == 0);
    if (not eliminated(v)) {
        ++stats_.vars.eliminated;
        // eliminate var from assignment - no longer a decision variable!
        master()->assign_.eliminate(v);
    }
}

auto SharedContext::startAddConstraints(uint32_t constraintGuess) -> Solver& {
    if (not unfreeze()) {
        return *master();
    }
    auto expectedSize = (numVars() + 1) << 1u;
    if (step_ == lit_false || (step_ == lit_true && solveMode() == solve_multi)) {
        expectedSize += 2; // reserve space for step literal
    }
    btig_.resize(expectedSize);
    master()->startInit(constraintGuess, configuration()->solver(0));
    return *master();
}
bool SharedContext::addUnary(Literal x) { // NOLINT(readability-make-member-function-const)
    POTASSCO_CHECK_PRE(not frozen() || not isShared());
    master()->acquireProblemVar(x.var());
    return master()->force(x);
}
bool SharedContext::addBinary(Literal x, Literal y) { // NOLINT(readability-make-member-function-const)
    POTASSCO_CHECK_PRE(allowImplicit(ConstraintType::static_));
    Literal lits[2] = {x, y};
    return ClauseCreator::create(*master(), ClauseRep::create(lits), ClauseCreator::clause_force_simplify).ok();
}
bool SharedContext::addTernary(Literal x, Literal y, Literal z) { // NOLINT(readability-make-member-function-const)
    POTASSCO_CHECK_PRE(allowImplicit(ConstraintType::static_));
    Literal lits[3] = {x, y, z};
    return ClauseCreator::create(*master(), ClauseRep::create(lits), ClauseCreator::clause_force_simplify).ok();
}
void SharedContext::add(Constraint* c) { // NOLINT(readability-make-member-function-const)
    POTASSCO_CHECK_PRE(not frozen());
    master()->add(c);
}
void SharedContext::addMinimize(WeightLiteral x, Weight_t p) {
    if (not mini_) {
        mini_ = std::make_unique<Minimize>();
    }
    mini_->add(p, x);
}
bool SharedContext::hasMinimize() const { return mini_ != nullptr; }
void SharedContext::removeMinimize() { mini_.reset(); }
auto SharedContext::minimize() -> SharedMinimizeData* { return mini_ ? mini_->get(*this) : nullptr; }
auto SharedContext::minimizeNoCreate() const -> SharedMinimizeData* { return mini_ ? mini_->product.get() : nullptr; }
int  SharedContext::addImp(LitView lits, ConstraintType ct) {
    if (not allowImplicit(ct)) {
        return -1;
    }
    bool learnt = ct != ConstraintType::static_;
    if (not learnt && not frozen() && satPrepro.get()) {
        satPrepro->addClause(lits);
        return 1;
    }
    return static_cast<int>(btig_.add(lits, learnt));
}
bool SharedContext::addPost(Solver& s) {
    POTASSCO_CHECK_PRE(s.sharedContext() == this, "solver not attached");
    return config_->addPost(s);
}
void SharedContext::setHeuristic(Solver& s) {
    POTASSCO_CHECK_PRE(s.sharedContext() == this, "solver not attached");
    config_->setHeuristic(s);
}
auto SharedContext::numConstraints() const -> uint32_t {
    return numBinary() + numTernary() + size32(master()->constraints_);
}

bool SharedContext::endInit(bool attachAll) {
    assert(not frozen());
    if (not master()->strategies().hasConfig) {
        master()->startInit(numConstraints(), configuration()->solver(0));
    }
    initStats(*master());
    heuristic.simplify();
    bool ok = not master()->hasConflict() && master()->preparePost();
    if (ok) {
        auto temp = std::move(satPrepro);
        ok        = (not temp || temp->preprocess(*this)) && master()->endInit();
        satPrepro = std::move(temp);
    }
    master()->dbIdx_           = size32(master()->constraints_);
    lastTopLevel_              = master()->assign_.front;
    stats_.constraints.other   = size32(master()->constraints_);
    stats_.constraints.binary  = btig_.numBinary();
    stats_.constraints.ternary = btig_.numTernary();
    stats_.acycEdges           = extGraph.get() ? extGraph->edges() : 0;
    stats_.extra               = {};
    auto complexity            = stats_.constraints.binary + stats_.constraints.ternary;
    for (auto* c : master()->constraints()) {
        if (const auto* clause = c->clause(); clause) {
            ++stats_.extra.clauses;
            stats_.extra.clLits += clause->size();
        }
        else if (const auto* wc = dynamic_cast<const WeightConstraint*>(c); wc) {
            auto& stats = stats_.extra.weightCons[wc->isWeight()];
            auto  cc    = wc->estimateComplexity(*master());
            ++stats.n;
            stats.c      += cc;
            stats.lits   += wc->size();
            stats.bounds += static_cast<uint64_t>(std::max(wc->bound(), 0));
            complexity   += cc;
        }
        else {
            complexity += c->estimateComplexity(*master());
            ++stats_.extra.other;
        }
    }
    stats_.complexity = std::max(stats_.complexity, complexity + stats_.extra.clauses);
    if (ok && step_ == lit_false) {
        requireStepVar();
        auto x = master()->pushAuxVar();
        POTASSCO_ASSERT(x == step_.var());
    }
    btig_.markShared(concurrency() > 1);
    share_.frozen = 1;
    if (ok && master()->getPost(PostPropagator::priority_class_general)) {
        ok = master()->propagate() && master()->simplify();
    }
    if (ok && attachAll) {
        for (auto i : irange(1u, concurrency())) {
            if (not hasSolver(i)) {
                pushSolver();
            }
            if (not attach(i)) {
                ok = false;
                break;
            }
        }
    }
    return ok || (detach(*master(), false), master()->setStopConflict(), false);
}
bool SharedContext::propagate() {
    if (not master()->propagate()) {
        return false;
    }
    return frozen() || not satPrepro || satPrepro->propagate(*this);
}
bool SharedContext::attach(Solver& other) {
    assert(frozen() && other.shared_ == this);
    if (other.validVar(step_.var())) {
        if (not other.popRootLevel(other.rootLevel())) {
            return false;
        }
        if (&other == master()) {
            return true;
        }
    }
    initStats(other);
    // 1. clone vars & assignment
    Var_t lastVar = other.numVars();
    other.startInit(size32(master()->constraints_), configuration()->solver(other.id()));
    if (other.hasConflict()) {
        return false;
    }
    for (auto x : master()->trailView()) {
        if (master()->auxVar(x.var())) {
            continue;
        }
        if (Antecedent null; not other.force(x, null)) {
            return false;
        }
    }
    for (Var_t v = satPrepro.get() ? lastVar + 1 : var_max, end = master()->numVars(); v <= end; ++v) {
        if (eliminated(v) && other.value(v) == value_free) {
            other.assign_.eliminate(v);
        }
    }
    if (other.constraints_.empty()) {
        other.lastSimp_ = master()->lastSimp_;
    }
    // 2. clone & attach constraints
    if (not other.cloneDB(master()->constraints_)) {
        return false;
    }
    Constraint* c = master()->enumerationConstraint();
    other.setEnumerationConstraint(c ? c->cloneAttach(other) : nullptr);
    // 3. endInit
    return (other.preparePost() && other.endInit()) || (detach(other, false), false);
}

void SharedContext::detach(Solver& s, bool reset) {
    assert(s.shared_ == this);
    if (reset) {
        s.reset();
    }
    s.setEnumerationConstraint(nullptr);
    s.popAuxVar();
}
void SharedContext::initStats(Solver& s) const {
    s.stats.enable(master()->stats);
    s.stats.reset();
}
auto SharedContext::solverStats(uint32_t sId) const -> SolverStats& {
    POTASSCO_ASSERT(hasSolver(sId), "solver id out of range");
    return solver(sId)->stats;
}
auto SharedContext::accuStats(SolverStats& out) const -> const SolverStats& {
    for (auto s : solvers_) { out.accu(s->stats, true); }
    return out;
}
void SharedContext::warn(const char* what) const {
    if (progress_) {
        progress_->dispatch(LogEvent(progress_->active(), Event::verbosity_quiet, LogEvent::warning, nullptr, what));
    }
}
void SharedContext::report(const char* what, const Solver* s) const {
    if (progress_) {
        progress_->dispatch(LogEvent(progress_->active(), Event::verbosity_high, LogEvent::message, s, what));
    }
}
void SharedContext::enter(Event::Subsystem sys) const {
    if (progress_) {
        progress_->setActive(sys);
    }
}
void SharedContext::simplify(LitView assigned, bool shuffle) {
    if (not isShared() && not assigned.empty()) {
        for (auto p : assigned) {
            if (p.id() < btig_.size()) {
                btig_.removeTrue(*master(), p);
            }
        }
    }
    auto& db = master()->constraints_;
    if (concurrency() == 1 || master()->dbIdx_ == 0) {
        simplifyDB(*master(), db, shuffle);
    }
    else {
        uint32_t rem = 0;
        for (Constraint*& con : db) {
            if (con->simplify(*master(), shuffle)) {
                con->destroy(master(), false);
                con = nullptr;
                ++rem;
            }
        }
        if (rem) {
            constexpr auto isNull = [](const Constraint* c) { return c == nullptr; };
            for (auto* s : drop(solvers_, 1u)) {
                POTASSCO_ASSERT(s->dbIdx_ <= db.size(), "Invalid DB idx!");
                if (s->dbIdx_ == db.size()) {
                    s->dbIdx_ -= rem;
                }
                else if (s->dbIdx_ != 0) {
                    s->dbIdx_ -= static_cast<uint32_t>(std::count_if(db.begin(), db.begin() + s->dbIdx_, isNull));
                }
            }
            erase_if(db, isNull);
        }
    }
    master()->dbIdx_ = size32(db);
}
void SharedContext::removeConstraint(uint32_t idx, bool detach) {
    auto& db = master()->constraints_;
    POTASSCO_CHECK_PRE(idx < db.size());
    Constraint* c = db[idx];
    for (auto* s : drop(solvers_, 1u)) { s->dbIdx_ -= (idx < s->dbIdx_); }
    db.erase(db.begin() + idx);
    master()->dbIdx_ = size32(db);
    c->destroy(master(), detach);
}

bool SharedContext::preprocessShort() {
    auto&  s      = *master();
    auto&  assign = s.assign_;
    LitVec lits;
    LitVec tern;
    for (Var_t v = 1; v < assign.numVars() && not s.hasConflict(); ++v) {
        if (assign.value(v) != value_free) {
            continue;
        }
        for (Literal lit : {posLit(v), negLit(v)}) {
            if (marked(lit)) {
                continue;
            }
            tern.clear();
            bool ok     = true;
            auto qFront = assign.assigned();
            assign.assign(lit, 0, lit_true);
            do {
                ok = btig_.forEach(assign.trail[qFront++], [&](Literal p, Literal q, Literal r) {
                    if (r == lit_false) {
                        return assign.assign(q, 0, p);
                    }
                    auto vq   = assign.value(q.var());
                    auto vr   = assign.value(r.var());
                    auto ante = Antecedent(p);
                    if (vr == trueValue(r) || vq == trueValue(q)) {
                        if (assign.reason(r.var()).asUint() == ante.asUint() ||
                            assign.reason(q.var()).asUint() == ante.asUint()) {
                            tern.push_back(~p);
                            tern.push_back(q);
                            tern.push_back(r);
                        }
                        return true;
                    }
                    if (vr == vq) {
                        return vr == value_free;
                    }
                    if (vq) {
                        if (assign.reason(q.var()).asUint() == ante.asUint()) {
                            tern.push_back(q.flag());
                            tern.push_back(~p);
                            tern.push_back(r);
                        }
                        return assign.assign(r, 0, Antecedent(p, ~q));
                    }
                    if (assign.reason(r.var()).asUint() == ante.asUint()) {
                        tern.push_back(r.flag());
                        tern.push_back(~p);
                        tern.push_back(q);
                    }
                    return assign.assign(q, 0, Antecedent(p, ~r));
                });
            } while (ok && qFront < assign.assigned());
            if (ok) {
                for (auto i = 0u; i < size32(tern); i += 3) {
                    bool sat    = not tern[i].flagged();
                    bool learnt = tern[i + 1].flagged() || tern[i + 2].flagged();
                    tern[i].unflag();
                    btig_.remove(std::span(tern.data() + i, 3), learnt);
                    if (not sat) {
                        btig_.add(std::span(tern.data() + i + 1, 2), learnt);
                    }
                }
            }
            while (assign.trail.back() != lit) {
                if (not marked(assign.trail.back())) {
                    mark(assign.trail.back());
                    lits.push_back(assign.trail.back());
                }
                assign.undoLast();
            }
            assign.undoLast();
            if (not ok) {
                master()->force(~lit) && master()->propagate();
                break;
            }
        }
    }
    while (not lits.empty()) {
        unmark(lits.back().var());
        lits.pop_back();
    }
    return master()->simplify();
}
/////////////////////////////////////////////////////////////////////////////////////////
// Distributor
/////////////////////////////////////////////////////////////////////////////////////////
Distributor::Distributor(const Policy& p) : policy_(p) {}
Distributor::~Distributor() = default;

} // namespace Clasp
