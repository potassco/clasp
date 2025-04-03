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
#if CLASP_HAS_THREADS
#include <clasp/mt/thread.h>
#endif

#include <potassco/basic_types.h>

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

static constexpr const char* const stats_s[] = {
#define KEY(X, Y) #X,
    PS_STATS(KEY)
#undef KEY
        "ctx"};
uint32_t    ProblemStats::size() { return toU32(std::size(stats_s)) - 1; }
const char* ProblemStats::key(uint32_t i) {
    POTASSCO_CHECK(i < size(), ERANGE);
    return stats_s[i];
}
StatisticObject ProblemStats::at(const char* key) const {
#define VALUE(X) StatisticObject::value(&(X))
#define APPLY(x, y)                                                                                                    \
    if (std::strcmp(key, #x) == 0)                                                                                     \
        return y;
    PS_STATS(APPLY)
    POTASSCO_CHECK(false, ERANGE);
#undef VALUE
#undef APPLY
}
#undef PS_STATS
/////////////////////////////////////////////////////////////////////////////////////////
// EventHandler
/////////////////////////////////////////////////////////////////////////////////////////
uint32_t Event::nextId() {
    static uint32_t id_s = 0;
    return id_s++;
}
EventHandler::EventHandler(Event::Verbosity verbosity) : verb_(0), sys_(0) {
    if (uint32_t x = verbosity) {
        uint32_t r = (x | (x << 4) | (x << 8) | (x << 12));
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
    if (sys == static_cast<Event::Subsystem>(sys_)) {
        return false;
    }
    sys_ = static_cast<uint16_t>(sys);
    return true;
}
Event::Subsystem EventHandler::active() const { return static_cast<Event::Subsystem>(sys_); }
/////////////////////////////////////////////////////////////////////////////////////////
// ShortImplicationsGraph::ImplicationList
/////////////////////////////////////////////////////////////////////////////////////////
#if CLASP_HAS_THREADS
ShortImplicationsGraph::Block::Block(Block* n, const Literal* x, uint32_t xs) : next_(n), sizeLock_(xs << size_shift) {
    std::copy_n(x, xs, data_);
}
bool ShortImplicationsGraph::Block::tryLock(uint32_t& size) {
    if (uint32_t s = sizeLock_.fetch_or(lock_mask, std::memory_order_acquire); not Potassco::test_mask(s, lock_mask)) {
        size = s >> size_shift;
        return true;
    }
    return false;
}
bool ShortImplicationsGraph::Block::addUnlock(uint32_t lockedSize, const Literal* x, uint32_t xs) {
    if ((lockedSize + xs) <= block_cap) {
        std::copy_n(x, xs, data_ + lockedSize);
        sizeLock_.store((lockedSize + xs) << size_shift, std::memory_order_release);
        return true;
    }
    return false;
}
ShortImplicationsGraph::ImplicationList::~ImplicationList() { resetLearnt(); }
void ShortImplicationsGraph::ImplicationList::resetLearnt() {
    for (Block* x = learnt.exchange(nullptr, std::memory_order_acquire); x;) {
        Block* t = std::exchange(x, x->next());
        delete t;
    }
}
void ShortImplicationsGraph::ImplicationList::reset() {
    ImpListBase::reset();
    resetLearnt();
}

void ShortImplicationsGraph::ImplicationList::addLearnt(Literal q, Literal r) {
    Literal  nc[2] = {q, r};
    uint32_t ns    = 1 + not isSentinel(r);
    nc[ns - 1].flag(); // mark end of clause
    for (Block* x = learnt.load();;) {
        if (x != nullptr) {
            if (uint32_t lockedSize; x->tryLock(lockedSize)) [[likely]] {
                if (not x->addUnlock(lockedSize, nc, ns)) {
                    auto* t = new Block(x, nc, ns); // x is full and remains locked forever
                    learnt.store(t);                // publish new (unlocked) block
                }
                return;
            }
            // some other thread is currently adding to this list...
            mt::this_thread::yield();
            x = learnt.load(); // ...reload - x might be full and no longer the active block
        }
        else if (auto* n = new Block(x, nc, ns); learnt.compare_exchange_weak(x, n)) {
            return; // won the race and published our block as first block
        }
        else { // some thread allocated and published a first block before us
            assert(x != nullptr);
            delete n;
        }
    }
}

bool ShortImplicationsGraph::ImplicationList::hasLearnt(Literal q, Literal r) const {
    return not forEachLearnt(lit_true, [&, binary = isSentinel(r)](Literal, Literal q0, Literal r0 = lit_false) {
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
/////////////////////////////////////////////////////////////////////////////////////////
// ShortImplicationsGraph
/////////////////////////////////////////////////////////////////////////////////////////
ShortImplicationsGraph::~ShortImplicationsGraph() { PodVector<ImplicationList>::destruct(graph_); }
void ShortImplicationsGraph::resize(uint32_t nodes) {
    if (nodes <= graph_.size()) {
        while (graph_.size() != nodes) {
            graph_.back().reset();
            graph_.pop_back();
        }
    }
    else if (graph_.capacity() >= nodes) {
        graph_.resize(nodes);
    }
    else {
        // NOTE: We can't simply resize graph here because ImplicationList is actually not trivially relocatable.
        ImpLists temp;
        temp.resize(nodes);
        for (auto i : irange(graph_)) { temp[i] = std::move(graph_[i]); }
        graph_.swap(temp);
    }
}

uint32_t ShortImplicationsGraph::numEdges(Literal p) const { return graph_[p.id()].size(); }

bool ShortImplicationsGraph::add(LitView lits, bool learnt) {
    POTASSCO_ASSERT(lits.size() > 1 && lits.size() < 4);
    bool      tern  = lits.size() == 3u;
    uint32_t& stats = (tern ? tern_ : bin_)[learnt];
    Literal   p = lits[0], q = lits[1], r = (tern ? lits[2] : lit_false);
    p.unflag(), q.unflag(), r.unflag();
    if (not shared_) {
        bool simp = learnt && simp_ == ContextParams::simp_learnt;
        if (simp && contains(getList(~p).left_view(), q)) {
            return true;
        }
        if (learnt) {
            p.flag(), q.flag(), r.flag();
        }
        if (not tern) {
            getList(~p).push_left(q);
            getList(~q).push_left(p);
        }
        else {
            if (simp && contains(getList(~p).right_view(), Tern{q, r})) {
                return true;
            }
            getList(~p).push_right({q, r});
            getList(~q).push_right({p, r});
            getList(~r).push_right({p, q});
        }
        ++stats;
        return true;
    }
#if CLASP_HAS_THREADS
    else if (learnt && not getList(~p).hasLearnt(q, r)) {
        getList(~p).addLearnt(q, r);
        getList(~q).addLearnt(p, r);
        if (tern) {
            getList(~r).addLearnt(p, q);
        }
        ++stats;
        return true;
    }
#endif
    return false;
}

void ShortImplicationsGraph::removeBin(Literal other, Literal sat) {
    --bin_[other.flagged()];
    auto& w = getList(~other);
    w.erase_left_unordered(std::find(w.left_begin(), w.left_end(), sat));
    w.try_shrink();
}

void ShortImplicationsGraph::removeTern(const Solver& s, const Tern& t, Literal p) {
    assert(s.value(p.var()) != value_free);
    --tern_[t[0].flagged()];
    for (auto lit : t) {
        auto& w = getList(~lit);
        w.erase_right_unordered(
            std::find_if(w.right_begin(), w.right_end(), [p](const Tern& x) { return x[0] == p || x[1] == p; }));
        w.try_shrink();
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
// All conditional binary-clauses are replaced with real binary clauses.
// Note: clauses containing p watch ~p. Those containing ~p watch p.
void ShortImplicationsGraph::removeTrue(const Solver& s, Literal p) {
    POTASSCO_ASSERT(not shared_);
#if CLASP_HAS_THREADS
    for (auto lit : {p, ~p}) {
        getList(~lit).forEachLearnt(lit, [&](Literal p0, Literal q, Literal r = lit_false) {
            for (auto x : {q, r}) {
                if (auto& xl = getList(~x); xl.learnt) {
                    // promote entries from learnt blocks to base list
                    std::ignore = xl.forEachLearnt(x, [&](Literal, Literal l1, Literal l2 = lit_false) {
                        if (s.value(l1.var()) == value_free) {
                            if (l2 == lit_false) {
                                xl.push_left(l1.flag());
                            }
                            else if (s.value(l2.var()) == value_free) {
                                xl.push_right({l1.flag(), l2.flag()});
                            }
                        }
                        // else: entry is no longer relevant or will be re-added later.
                        return true;
                    });
                    xl.resetLearnt();
                }
            }
            if (r != lit_false) {
                removeTern(s, {q.flag(), r.flag()}, p0);
            }
            else if (p == p0) {
                removeBin(q.flag(), p0);
            }
            return true;
        });
    }
#endif
    auto& negPList = getList(~p);
    auto& pList    = getList(p);
    // remove every binary clause containing p -> clause is satisfied
    for (auto x : negPList.left_view()) { removeBin(x, p); }
    // remove every ternary clause containing p -> clause is satisfied
    for (const auto& t : negPList.right_view()) { removeTern(s, t, p); }
    // transform ternary clauses containing ~p to binary clause
    for (const auto& t : pList.right_view()) { removeTern(s, t, ~p); }
    negPList.reset();
    pList.reset();
}

bool ShortImplicationsGraph::propagate(Solver& s, Literal p) const {
    return forEach(p, [&s](Literal p0, Literal q, Literal r = lit_false) {
        if (auto vq = s.value(q.var()); vq != trueValue(q)) {
            if (r == lit_false) {
                return s.force(q, Antecedent(p0));
            }
            if (auto vr = s.value(r.var()); vr != trueValue(r) && vr + vq) {
                return vq ? s.force(r, Antecedent(p0, ~q)) : s.force(q, Antecedent(p0, ~r));
            }
        }
        return true;
    });
}
bool ShortImplicationsGraph::reverseArc(const Solver& s, Literal p, uint32_t maxLev, Antecedent& out) const {
    return not forEach(p, [&](Literal, Literal q, Literal r = lit_false) {
        if (not isRevLit(s, q, maxLev)) {
            return true;
        }
        if (r == lit_false) {
            out = Antecedent(~q);
            return false;
        }
        if (not isRevLit(s, r, maxLev)) {
            return true;
        }
        out = Antecedent(~q, ~r);
        return false;
    });
}
bool ShortImplicationsGraph::propagateBin(Assignment& out, Literal p, uint32_t level) const {
    for (const auto& lit : graph_[p.id()].left_view()) {
        if (not out.assign(lit, level, p)) {
            return false;
        }
    }
    return true;
}
/////////////////////////////////////////////////////////////////////////////////////////
// SatPreprocessor
/////////////////////////////////////////////////////////////////////////////////////////
SatPreprocessor::SatPreprocessor() : ctx_(nullptr), opts_(nullptr), elimTop_(nullptr), seen_(1, 1) {}
SatPreprocessor::~SatPreprocessor() { discardClauses(true); }
void SatPreprocessor::discardClauses(bool discardEliminated) {
    for (auto* clause : clauses_) {
        if (clause) {
            clause->destroy();
        }
    }
    discardVec(clauses_);
    if (Clause* r = (discardEliminated ? elimTop_ : nullptr)) {
        do {
            Clause* t = r;
            r         = r->next();
            t->destroy();
        } while (r);
        elimTop_ = nullptr;
    }
    if (discardEliminated) {
        seen_ = Range32(1, 1);
    }
}
void SatPreprocessor::cleanUp(bool discardEliminated) {
    if (ctx_) {
        seen_.hi = ctx_->numVars() + 1;
    }
    doCleanUp();
    discardClauses(discardEliminated);
}

bool SatPreprocessor::addClause(LitView clause) {
    if (clause.empty()) {
        return false;
    }
    clause.size() > 1 ? clauses_.push_back(Clause::newClause(clause)) : units_.push_back(clause[0]);
    return true;
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

bool SatPreprocessor::preprocess(SharedContext& ctx, Options& opts) {
    ctx_         = &ctx;
    opts_        = &opts;
    Solver* s    = ctx_->master();
    auto    prev = std::move(ctx.satPrepro);
    POTASSCO_SCOPE_EXIT({
        cleanUp();
        if (not ctx.satPrepro) {
            ctx.satPrepro = std::move(prev);
        }
    });
    for (auto lit : units_) {
        if (not ctx.addUnary(lit)) {
            return false;
        }
    }
    units_.clear();
    // skip preprocessing if other constraints are UNSAT
    if (not s->propagate()) {
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
    bool limFrozen = false;
    if (double limit = opts.limFrozen; limit != 0 && ctx_->stats().vars.frozen) {
        uint32_t varFrozen = ctx_->stats().vars.frozen;
        for (auto lit : s->trailView()) { varFrozen -= (ctx_->varInfo(lit.var()).frozen()); }
        limFrozen = percent(varFrozen, s->numFreeVars()) > limit;
    }
    // 1. remove SAT-clauses, strengthen clauses w.r.t false literals, attach
    if (opts.type != 0 && not opts.clauseLimit(numClauses()) && not limFrozen && initPreprocess(opts)) {
        ClauseList::size_type j = 0;
        for (Clause*& clause : clauses_) {
            auto* c = std::exchange(clause, nullptr);
            assert(c);
            c->simplify(*s);
            Literal x = (*c)[0];
            if (s->value(x.var()) == value_free) {
                clauses_[j++] = c;
            }
            else {
                c->destroy();
                if (not ctx.addUnary(x)) {
                    return false;
                }
            }
        }
        shrinkVecTo(clauses_, j);
        // 2. run preprocessing
        freezeSeen();
        if (not s->propagate() || not doPreprocess()) {
            return false;
        }
    }
    // simplify other constraints w.r.t any newly derived top-level facts
    if (not s->simplify()) {
        return false;
    }
    // 3. move preprocessed clauses to ctx
    for (Clause*& c : clauses_) {
        if (c) {
            if (not ClauseCreator::create(*s, ClauseRep::create({&(*c)[0], c->size()}), {})) {
                return false;
            }
            std::exchange(c, nullptr)->destroy();
        }
    }
    discardVec(clauses_);
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
    doExtendModel(m, open);
    // remove unconstrained vars already flipped
    while (not open.empty() && open.back().sign()) { open.pop_back(); }
}
SatPreprocessor::Clause* SatPreprocessor::Clause::newClause(LitView lits) {
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
void SatPreprocessor::Clause::destroy() {
    void* mem = this;
    this->~Clause();
    ::operator delete(mem);
}
/////////////////////////////////////////////////////////////////////////////////////////
// OutputTable
/////////////////////////////////////////////////////////////////////////////////////////
OutputTable::OutputTable() : theory(nullptr), vars_(0, 0), projMode_(ProjectMode::implicit), hide_(0) {}
OutputTable::~OutputTable() {
    PodVector<NameType>::destruct(facts_);
    PodVector<PredType>::destruct(preds_);
}

void OutputTable::setFilter(char c) { hide_ = c; }
bool OutputTable::filter(const std::string_view& n) const { return n.empty() || n.starts_with(hide_); }
bool OutputTable::filter(const NameType& n) const { return filter(n.view()); }
bool OutputTable::add(const NameType& fact) {
    if (not filter(fact)) {
        facts_.push_back(fact);
        return true;
    }
    return false;
}
bool OutputTable::add(const std::string_view& fact) {
    return not filter(fact) && add(NameType(fact, NameType::create_shared));
}

bool OutputTable::add(const NameType& n, Literal c, uint32_t u) {
    if (not filter(n)) {
        PredType p = {n, c, u};
        preds_.push_back(p);
        return true;
    }
    return false;
}
bool OutputTable::add(const std::string_view& n, Literal c, uint32_t u) {
    return not filter(n) && add(NameType(n, NameType::create_shared), c, u);
}

void     OutputTable::setVarRange(const Range32& r) { vars_ = r; }
void     OutputTable::setProjectMode(ProjectMode m) { projMode_ = m; }
void     OutputTable::addProject(Literal x) { proj_.push_back(x); }
void     OutputTable::clearProject() { proj_.clear(); }
uint32_t OutputTable::size() const { return numFacts() + numPreds() + numVars(); }
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
DomModType DomainTable::ValueType::type() const {
    return static_cast<DomModType>(comp_ == 0 ? type_ : +DomModType::true_ + type_);
}
DomainTable::DomainTable() : assume(nullptr), seen_(0) {}
void DomainTable::add(Var_t v, DomModType t, int16_t b, uint16_t p, Literal c) {
    if (c != lit_false && (t != DomModType::init || c == lit_true)) {
        entries_.push_back(ValueType(v, t, b, p, c));
    }
}
uint32_t DomainTable::simplify() {
    if (seen_ >= size()) {
        return size();
    }
    std::stable_sort(entries_.begin() + seen_, entries_.end(), [](const ValueType& lhs, const ValueType& rhs) {
        return lhs.cond() < rhs.cond() || (lhs.cond() == rhs.cond() && lhs.var() < rhs.var());
    });
    DomVec::iterator j = entries_.begin() + seen_;
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
            static constexpr auto n_simp    = 4u;
            constexpr auto        mod_level = +DomModType::level, mod_sign = +DomModType::sign;
            constexpr int16_t     no_bias      = INT16_MAX;
            uint16_t              prio[n_simp] = {0, 0, 0, 0};
            int16_t               bias[n_simp] = {no_bias, no_bias, no_bias, no_bias};
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
    entries_.erase(j, entries_.end());
    if (entries_.capacity() > static_cast<std::size_t>(entries_.size() * 1.75)) {
        DomVec(entries_).swap(entries_);
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
    const uint32_t gs =
        static_cast<uint32_t>(HeuParams::pref_scc | HeuParams::pref_hcc | HeuParams::pref_disj) & defFilter;
    if (ctx.sccGraph.get() && gs && ((gs & HeuParams::pref_scc) != 0 || ctx.sccGraph->numNonHcfs())) {
        for (uint32_t i : irange(ctx.sccGraph->numAtoms())) {
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
bool                  DomainTable::empty() const { return entries_.empty(); }
uint32_t              DomainTable::size() const { return size32(entries_); }
DomainTable::iterator DomainTable::begin() const { return entries_.begin(); }
DomainTable::iterator DomainTable::end() const { return entries_.end(); }
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
    SharedMinimizeData* get(SharedContext& ctx) {
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
    // sentinel always present
    setFrozen(addVar(VarType::atom, 0), true);
    stats_.vars.num = 0;
    config_         = &g_config_def;
    pushSolver();
}
uint32_t SharedContext::defaultDomPref() const {
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
    if (n <= 1) {
        share_.count = 1;
    }
    else {
        share_.count = n;
        solvers_.reserve(n);
    }
    while (solvers_.size() < share_.count && Potassco::test(mode, resize_push)) { pushSolver(); }
    while (solvers_.size() > share_.count && Potassco::test(mode, resize_pop)) {
        delete solvers_.back();
        solvers_.pop_back();
    }
    if ((share_.shareM & ContextParams::share_auto) != 0) {
        setShareMode(ContextParams::share_auto);
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

Solver& SharedContext::pushSolver() {
    auto id      = size32(solvers_);
    share_.count = std::max(share_.count, id + 1);
    auto* s      = new Solver(this, id);
    solvers_.push_back(s);
    return *s;
}

void SharedContext::setConfiguration(Configuration* c) {
    auto* nc = c ? c : &g_config_def;
    report(Event::subsystem_facade);
    auto configChanged = config_ != nc;
    config_            = nc;
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
        varInfo_[tag] = VarInfo();
        step_         = lit_false;
        popVars(1);
        ++stats_.vars.num;
    }
    return not master()->hasConflict();
}

Var_t SharedContext::addVars(uint32_t nVars, VarType t, uint8_t flags) {
    static constexpr auto flags_for = [](VarType in) {
        switch (in) {
            default             : return static_cast<VarInfo::Flag>(0);
            case VarType::body  : return VarInfo::flag_body;
            case VarType::hybrid: return VarInfo::flag_eq;
        }
    };
    Potassco::store_clear_mask(flags, VarInfo::flag_pos | VarInfo::flag_neg);
    Potassco::store_set_mask(flags, flags_for(t));
    varInfo_.insert(varInfo_.end(), nVars, VarInfo(flags));
    stats_.vars.num += nVars;
    return static_cast<Var_t>(varInfo_.size() - nVars);
}

void SharedContext::popVars(uint32_t nVars) {
    POTASSCO_CHECK_PRE(not frozen(), "Cannot pop vars from frozen program");
    POTASSCO_CHECK(nVars <= numVars(), EINVAL, POTASSCO_FUNC_NAME);
    uint32_t newVars = numVars() - nVars;
    uint32_t comVars = master()->numVars();
    if (newVars >= comVars) {
        // vars not yet committed
        varInfo_.erase(varInfo_.end() - nVars, varInfo_.end());
        stats_.vars.num -= nVars;
    }
    else {
        for (Var_t v = numVars(); v && nVars; --nVars, --v) {
            stats_.vars.eliminated -= eliminated(v);
            stats_.vars.frozen     -= varInfo(v).frozen();
            --stats_.vars.num;
            varInfo_.pop_back();
        }
        btig_.resize((numVars() + 1) << 1);
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

Literal SharedContext::addStepLit() {
    VarInfo nv;
    nv.set(VarInfo::flag_frozen);
    varInfo_.push_back(nv);
    btig_.resize((numVars() + 1) << 1);
    return posLit(master()->pushAuxVar());
}
Solver& SharedContext::startAddConstraints(uint32_t constraintGuess) {
    if (not unfreeze()) {
        return *master();
    }
    btig_.resize((numVars() + 1 + static_cast<uint32_t>(step_ == lit_false || solveMode() == solve_multi)) << 1);
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
bool                SharedContext::hasMinimize() const { return mini_ != nullptr; }
void                SharedContext::removeMinimize() { mini_.reset(); }
SharedMinimizeData* SharedContext::minimize() { return mini_ ? mini_->get(*this) : nullptr; }
SharedMinimizeData* SharedContext::minimizeNoCreate() const { return mini_ ? mini_->product.get() : nullptr; }
int                 SharedContext::addImp(LitView lits, ConstraintType ct) {
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

uint32_t SharedContext::numConstraints() const { return numBinary() + numTernary() + size32(master()->constraints_); }

bool SharedContext::endInit(bool attachAll) {
    assert(not frozen());
    report(Event::subsystem_prepare);
    initStats(*master());
    heuristic.simplify();
    SatPrePtr temp = std::move(satPrepro);
    bool      ok   = not master()->hasConflict() && master()->preparePost() && (not temp || temp->preprocess(*this)) &&
              master()->endInit();
    satPrepro                  = std::move(temp);
    master()->dbIdx_           = size32(master()->constraints_);
    lastTopLevel_              = master()->assign_.front;
    stats_.constraints.other   = size32(master()->constraints_);
    stats_.constraints.binary  = btig_.numBinary();
    stats_.constraints.ternary = btig_.numTernary();
    stats_.acycEdges           = extGraph.get() ? extGraph->edges() : 0;
    stats_.complexity          = std::max(stats_.complexity, problemComplexity());
    if (ok && step_ == lit_false) {
        step_ = addStepLit();
    }
    btig_.markShared(concurrency() > 1);
    share_.frozen = 1;
    if (ok && master()->getPost(PostPropagator::priority_class_general)) {
        ok = master()->propagate() && master()->simplify();
    }
    if (ok && attachAll) {
        for (uint32_t i : irange(1u, concurrency())) {
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
SolverStats& SharedContext::solverStats(uint32_t sId) const {
    POTASSCO_ASSERT(hasSolver(sId), "solver id out of range");
    return solver(sId)->stats;
}
const SolverStats& SharedContext::accuStats(SolverStats& out) const {
    for (auto s : solvers_) { out.accu(s->stats, true); }
    return out;
}
void SharedContext::warn(const char* what) const {
    if (progress_) {
        progress_->dispatch(LogEvent(progress_->active(), Event::verbosity_quiet, LogEvent::warning, nullptr, what));
    }
}
POTASSCO_ATTRIBUTE_FORMAT(2, 3) void SharedContext::warnFmt(const char* fmt, ...) const {
    if (progress_ && fmt && *fmt) {
        va_list args;
        va_start(args, fmt);
        char msg[1024];
        std::vsnprintf(msg, std::size(msg), fmt, args);
        va_end(args);
        warn(msg);
    }
}
void SharedContext::report(const char* what, const Solver* s) const {
    if (progress_) {
        progress_->dispatch(LogEvent(progress_->active(), Event::verbosity_high, LogEvent::message, s, what));
    }
}
void SharedContext::report(Event::Subsystem sys) const {
    if (progress_ && progress_->setActive(sys)) {
        const char*      m;
        Event::Verbosity v = Event::verbosity_high;
        switch (sys) {
            default                      : return;
            case Event::subsystem_load   : m = "Reading"; break;
            case Event::subsystem_prepare: m = "Preprocessing"; break;
            case Event::subsystem_solve:
                m = "Solving";
                v = Event::verbosity_low;
                break;
        }
        progress_->onEvent(LogEvent(sys, v, LogEvent::message, nullptr, m));
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
    Solver::ConstraintDB& db = master()->constraints_;
    POTASSCO_CHECK_PRE(idx < db.size());
    Constraint* c = db[idx];
    for (auto* s : drop(solvers_, 1u)) { s->dbIdx_ -= (idx < s->dbIdx_); }
    db.erase(db.begin() + idx);
    master()->dbIdx_ = size32(db);
    c->destroy(master(), detach);
}

uint32_t SharedContext::problemComplexity() const {
    if (isExtended()) {
        uint32_t r = numBinary() + numTernary();
        for (const auto* constraint : master()->constraints_) { r += constraint->estimateComplexity(*master()); }
        return r;
    }
    return numConstraints();
}
/////////////////////////////////////////////////////////////////////////////////////////
// Distributor
/////////////////////////////////////////////////////////////////////////////////////////
Distributor::Distributor(const Policy& p) : policy_(p) {}
Distributor::~Distributor() = default;

} // namespace Clasp
