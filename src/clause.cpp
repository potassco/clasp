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
#include <clasp/util/misc_types.h>

#include <potassco/error.h>

#include <algorithm>

namespace Clasp {
namespace Detail {

static auto alloc(std::size_t size) -> void* {
    POTASSCO_PRAGMA_TODO("replace with CACHE_LINE_ALIGNED alloc")
    return ::operator new(size);
}
static void free(void* mem) { ::operator delete(mem); }
using SharedLitsPtr = std::unique_ptr<SharedLiterals, ReleaseObject>;

} // namespace Detail
/////////////////////////////////////////////////////////////////////////////////////////
// SharedLiterals
/////////////////////////////////////////////////////////////////////////////////////////
auto SharedLiterals::newShareable(LitView lits, ConstraintType t, uint32_t numRefs) -> SharedLiterals* {
    void* m = Detail::alloc(sizeof(SharedLiterals) + (lits.size() * sizeof(Literal)));
    return new (m) SharedLiterals(lits, t, numRefs);
}

SharedLiterals::SharedLiterals(LitView lits, ConstraintType t, uint32_t refs)
    : refCount_(std::max(1u, refs))
    , sizeType_((size32(lits) << 2) + +t) {
    if (not lits.empty()) {
        std::memcpy(lits_, lits.data(), lits.size() * sizeof(Literal));
    }
}

auto SharedLiterals::simplify(Solver& s) -> uint32_t {
    auto falseInc = 1u - unique();
    auto newSize  = 0u;
    for (Literal* c = lits_; auto lit : literals()) {
        if (auto v = s.value(lit.var()); v == value_free) {
            if (*c != lit) {
                *c = lit;
            }
            ++c;
            ++newSize;
        }
        else if (v == trueValue(lit)) {
            newSize = 0;
            break;
        }
        else {
            c += falseInc;
        }
    }
    if (falseInc == 0 && newSize != size()) {
        sizeType_ = (newSize << 2) | (sizeType_ & 3u);
    }
    return newSize;
}

void SharedLiterals::release(int n) {
    if (n > 0 && refCount_.release(static_cast<uint32_t>(n))) {
        this->~SharedLiterals();
        Detail::free(this);
    }
}
auto SharedLiterals::share() -> SharedLiterals* {
    refCount_.add();
    return this;
}
/////////////////////////////////////////////////////////////////////////////////////////
// ClauseCreator
/////////////////////////////////////////////////////////////////////////////////////////
ClauseCreator::ClauseCreator(Solver* s) : solver_(s), flags_{} {}

auto ClauseCreator::start(ConstraintType t) -> ClauseCreator& {
    assert(solver_ && (solver_->decisionLevel() == 0 || t != ConstraintType::static_));
    literals_.clear();
    extra_ = ConstraintInfo(t);
    return *this;
}

auto ClauseCreator::watchOrder(const Solver& s, Literal p) -> uint32_t {
    auto valueP = s.value(p.var());
    if (valueP == value_free) { // DL+1,  if isFree(p)
        return s.decisionLevel() + 1;
    }
    // DL(p), if isFalse(p)
    // ~DL(p),if isTrue(p)
    return s.level(p.var()) ^ static_cast<uint32_t>(0 - (valueP == trueValue(p)));
}
ClauseRep ClauseCreator::prepare(Solver& s, LitView in, const ConstraintInfo& e, CreateFlag flags,
                                 std::span<Literal> out) {
    assert(not out.empty() || in.empty());
    ClauseRep ret    = ClauseRep::prepared({out.data(), 0u}, e);
    uint32_t  abstW1 = 0, abstW2 = 0;
    bool      simplify = Potassco::test(flags, clause_force_simplify) && out.size() >= in.size();
    Literal   tag      = ~s.tagLiteral();
    Var_t     vMax     = s.numProblemVars() > s.numVars() && not in.empty() ? std::ranges::max_element(in)->var() : 0;
    s.acquireProblemVar(vMax);
    for (uint32_t j = 0, maxOut = size32(out) - 1; auto p : in) {
        auto abstP = watchOrder(s, p);
        if ((abstP + 1) > 1 && (not simplify || not s.seen(p.var()))) {
            out[j] = p;
            if (p == tag) {
                ret.info.setTagged(true);
            }
            if (p.var() > vMax) {
                vMax = p.var();
            }
            if (simplify) {
                s.markSeen(p);
            }
            if (abstP > abstW1) {
                std::swap(abstP, abstW1);
                std::swap(out[0], out[j]);
            }
            if (abstP > abstW2) {
                std::swap(abstP, abstW2);
                std::swap(out[1], out[j]);
            }
            if (j != maxOut) {
                ++j;
            }
            ++ret.size;
        }
        else if (abstP == UINT32_MAX || (simplify && abstP && s.seen(~p))) {
            abstW1 = UINT32_MAX;
            break;
        }
    }
    if (simplify) {
        assert(ret.size <= size32(out));
        for (auto x : irange(ret.size)) { s.clearSeen(out[x].var()); }
    }
    if (abstW1 == UINT32_MAX || (abstW2 && out[0].var() == out[1].var())) {
        out[0]   = abstW1 == UINT32_MAX || out[0] == ~out[1] ? lit_true : out[0];
        ret.size = 1;
    }
    ret.info.setAux(s.auxVar(vMax));
    return ret;
}

auto ClauseCreator::prepare(Solver& s, LitVec& lits, CreateFlag flags, const ConstraintInfo& info) -> ClauseRep {
    if (lits.empty()) {
        lits.push_back(lit_false);
    }
    if (not Potassco::test(flags, clause_no_prepare) || Potassco::test(flags, clause_force_simplify)) {
        ClauseRep x = prepare(s, lits, info, flags, lits);
        truncateVec(lits, x.size);
        return x;
    }
    return ClauseRep::prepared(lits, info);
}

auto ClauseCreator::prepare(bool forceSimplify) -> ClauseRep {
    return prepare(*solver_, literals_, forceSimplify ? clause_force_simplify : CreateFlag{}, extra_);
}

auto ClauseCreator::status(const Solver& s, LitView lits) -> Status {
    if (lits.empty()) {
        return status_empty;
    }
    Literal temp[3];
    auto    x = prepare(const_cast<Solver&>(s), lits, ConstraintInfo(), {}, temp);
    return statusPrepared(s, x);
}

auto ClauseCreator::status(const Solver& s, const ClauseRep& c) -> Status {
    return c.prep ? statusPrepared(s, c) : status(s, c.literals());
}

auto ClauseCreator::statusPrepared(const Solver& s, const ClauseRep& c) -> Status {
    uint32_t dl = s.decisionLevel();
    uint32_t fw = c.size ? watchOrder(s, c.lits[0]) : 0;
    if (fw == UINT32_MAX) {
        return status_subsumed;
    }
    uint32_t sw = c.size > 1 ? watchOrder(s, c.lits[1]) : 0;
    uint32_t st = status_open;
    if (fw > var_max) {
        st |= status_sat;
        fw  = ~fw;
    }
    else if (fw <= dl) {
        st |= (fw ? status_unsat : status_empty);
    }
    if (sw <= dl && fw > sw) {
        st |= status_unit;
    }
    return static_cast<Status>(st);
}

bool ClauseCreator::ignoreClause(const Solver& s, const ClauseRep& c, Status st, CreateFlag flags) {
    auto x = (st & (status_sat | status_unsat));
    if (x == status_open) {
        return false;
    }
    if (x == status_unsat) {
        return st != status_empty && Potassco::test(flags, clause_not_conflict);
    }
    assert(x == status_sat);
    return st == status_subsumed ||
           (st == status_sat && (Potassco::test(flags, clause_not_sat) || (Potassco::test(flags, clause_not_root_sat) &&
                                                                           s.level(c.lits[0].var()) <= s.rootLevel())));
}

auto ClauseCreator::end(CreateFlag flags) -> Result {
    assert(solver_);
    flags |= flags_;
    return createPrepared(*solver_, prepare(*solver_, literals_, flags, extra_), flags);
}

auto ClauseCreator::newProblemClause(Solver& s, const ClauseRep& clause, CreateFlag flags) -> ClauseHead* {
    ClauseHead* ret;
    auto        wMode = s.watchInitMode();
    if (Potassco::test(flags, clause_watch_first)) {
        wMode = SolverStrategies::watch_first;
    }
    else if (Potassco::test(flags, clause_watch_rand)) {
        wMode = SolverStrategies::watch_rand;
    }
    else if (Potassco::test(flags, clause_watch_least)) {
        wMode = SolverStrategies::watch_least;
    }
    if (clause.size > 2 && wMode != SolverStrategies::watch_first) {
        uint32_t fw = 0, sw = 1;
        if (wMode == SolverStrategies::watch_rand) {
            fw = s.rng.irand(clause.size);
            do { sw = s.rng.irand(clause.size); } while (sw == fw);
        }
        else if (wMode == SolverStrategies::watch_least) {
            uint32_t cw1 = s.numWatches(~clause.lits[0]);
            uint32_t cw2 = s.numWatches(~clause.lits[1]);
            if (cw1 > cw2) {
                std::swap(fw, sw);
                std::swap(cw1, cw2);
            }
            for (uint32_t i = 2; i != clause.size && cw2; ++i) {
                uint32_t p   = i;
                uint32_t cwp = s.numWatches(~clause.lits[i]);
                if (cwp < cw1) {
                    std::swap(cwp, cw1);
                    std::swap(fw, p);
                }
                if (cwp < cw2) {
                    std::swap(cwp, cw2);
                    std::swap(sw, p);
                }
            }
        }
        std::swap(clause.lits[0], clause.lits[fw]);
        std::swap(clause.lits[1], clause.lits[sw]);
    }
    if (clause.size <= Clause::max_short_len || not s.sharedContext()->physicalShareProblem()) {
        ret = Clause::newClause(s, clause);
    }
    else {
        ret = Clause::newShared(s, SharedLiterals::newShareable(clause.literals(), clause.info.type(), 1), clause.info,
                                clause.lits, false);
    }
    if (not Potassco::test(flags, clause_no_add)) {
        assert(not clause.info.aux());
        s.add(ret);
    }
    return ret;
}

auto ClauseCreator::newLearntClause(Solver& s, const ClauseRep& clause, CreateFlag flags) -> ClauseHead* {
    ClauseHead* ret;
    auto        shared = Detail::SharedLitsPtr(s.distribute(clause.literals(), clause.info));
    if (clause.size <= Clause::max_short_len || not shared) {
        if (not s.isFalse(clause.lits[1]) || clause.size < s.compressLimit()) {
            ret = Clause::newClause(s, clause);
        }
        else {
            ret = Clause::newContractedClause(s, clause, 2, true);
        }
    }
    else {
        ret = Clause::newShared(s, shared.release(), clause.info, clause.lits, false);
    }
    if (not Potassco::test(flags, clause_no_add)) {
        s.addLearnt(ret, clause.size, clause.info.type());
    }
    return ret;
}

ClauseHead* ClauseCreator::newUnshared(Solver& s, const SharedLiterals* clause, const Literal* w,
                                       const ConstraintInfo& e) {
    LitVec temp;
    temp.reserve(clause->size());
    temp.assign(w, w + 2);
    for (auto x : *clause) {
        if (watchOrder(s, x) > 0 && x != temp[0] && x != temp[1]) {
            temp.push_back(x);
        }
    }
    return Clause::newClause(s, ClauseRep::prepared(temp, e));
}

auto ClauseCreator::createPrepared(Solver& s, const ClauseRep& clause, CreateFlag flags) -> Result {
    assert(s.decisionLevel() == 0 || (clause.info.learnt() && clause.prep));
    Status x = status(s, clause);
    if (ignoreClause(s, clause, x, flags)) {
        return Result(nullptr, x);
    }
    if (clause.size > 1) {
        Result ret(nullptr, x);
        if (not clause.info.learnt() && s.satPrepro() && not s.sharedContext()->frozen()) {
            return Result(nullptr, s.satPrepro()->addClause(clause.literals()) ? x : status_unsat);
        }
        if (not Potassco::test(flags, clause_no_heuristic)) {
            s.heuristic()->newConstraint(s, clause.literals(), clause.info.type());
        }
        if (clause.size > 3 || Potassco::test(flags, clause_explicit) || not s.allowImplicit(clause)) {
            ret.local = clause.info.learnt() ? newLearntClause(s, clause, flags) : newProblemClause(s, clause, flags);
        }
        else {
            // add implicit short rep
            s.add(clause);
        }
        if ((x & (status_unit | status_unsat)) != 0) {
            Antecedent ante(ret.local);
            if (not ret.local) {
                ante = clause.size == 3 ? Antecedent(~clause.lits[1], ~clause.lits[2]) : Antecedent(~clause.lits[1]);
            }
            ret.status = s.force(clause.lits[0], s.level(clause.lits[1].var()), ante) ? status_unit : status_unsat;
        }
        return ret;
    }
    s.add(clause);
    return Result(nullptr, not s.hasConflict() ? status_unit : status_unsat);
}

auto ClauseCreator::create(Solver& s, LitVec& lits, CreateFlag flags, const ConstraintInfo& extra) -> Result {
    return createPrepared(s, prepare(s, lits, flags, extra), flags);
}

auto ClauseCreator::create(Solver& s, const ClauseRep& rep, CreateFlag flags) -> Result {
    return createPrepared(s,
                          rep.prep == 0 && not Potassco::test(flags, clause_no_prepare)
                              ? prepare(s, rep.literals(), rep.info, flags, {rep.lits, rep.size})
                              : ClauseRep::prepared({rep.lits, rep.size}, rep.info),
                          flags);
}

ClauseCreator::Result ClauseCreator::integrate(Solver& s, SharedLiterals* clause, CreateFlag modeFlags,
                                               ConstraintType t) {
    assert(not s.hasConflict() && "ClauseCreator::integrate() - precondition violated!");
    auto shared = Detail::SharedLitsPtr(not Potassco::test(modeFlags, clause_no_release) ? clause : nullptr);
    // determine state of clause
    Literal temp[Clause::max_short_len];
    temp[0] = temp[1] = lit_false;
    ClauseRep x       = prepare(s, clause->literals(), ConstraintInfo(t), {}, temp);
    uint32_t  impSize = Potassco::test(modeFlags, clause_explicit) || not s.allowImplicit(x) ? 1 : 3;
    Status    xs      = status(s, x);
    if (ignoreClause(s, x, xs, modeFlags)) {
        return Result(nullptr, xs);
    }
    Result result(nullptr, xs);
    if (not Potassco::test(modeFlags, clause_no_heuristic)) {
        s.heuristic()->newConstraint(s, {clause->begin(), clause->size()}, t);
    }
    if (x.size > Clause::max_short_len && s.sharedContext()->physicalShare(t)) {
        result.local = Clause::newShared(s, clause, x.info, temp, shared.release() == nullptr);
    }
    else if (x.size > impSize) {
        result.local = x.size <= Clause::max_short_len ? Clause::newClause(s, x) : newUnshared(s, clause, temp, x.info);
    }
    else {
        // unary clause or implicitly shared via binary/ternary implication graph;
        // only check for implication/conflict but do not create
        // a local representation for the clause
        s.stats.addLearnt(x.size, x.info.type());
        modeFlags |= clause_no_add;
    }
    if (not Potassco::test(modeFlags, clause_no_add)) {
        s.addLearnt(result.local, x.size, x.info.type());
    }
    if (unitOrUnsat(xs)) {
        Antecedent ante     = result.local ? Antecedent(result.local) : Antecedent(~temp[1], ~temp[2]);
        uint32_t   impLevel = s.level(temp[1].var());
        result.status       = s.force(temp[0], impLevel, ante) ? status_unit : status_unsat;
        if (result.local && Potassco::test(modeFlags, clause_int_lbd)) {
            uint32_t lbd = s.countLevels(clause->literals());
            result.local->resetScore(ConstraintScore(x.info.activity(), lbd));
        }
    }
    return result;
}
auto ClauseCreator::integrate(Solver& s, SharedLiterals* clause, CreateFlag modeFlags) -> Result {
    return integrate(s, clause, modeFlags, clause->type());
}
/////////////////////////////////////////////////////////////////////////////////////////
// Clause
/////////////////////////////////////////////////////////////////////////////////////////
auto Clause::alloc(Solver& s, uint32_t lits, bool learnt) -> void* {
    if (lits <= max_short_len) {
        if (learnt) {
            s.addLearntBytes(32);
        }
        return s.allocSmall();
    }
    uint32_t extra = std::max(head_lits, lits) - head_lits;
    uint32_t bytes = sizeof(Clause) + (extra) * sizeof(Literal);
    if (learnt) {
        s.addLearntBytes(bytes);
    }
    return Detail::alloc(bytes);
}
auto Clause::newClause(void* mem, Solver& s, const ClauseRep& rep) -> ClauseHead* {
    assert(rep.size >= 2 && mem);
    if (rep.size <= max_short_len) {
        return new (mem) SmallClause(s, rep);
    }
    return new (mem) Clause(s, rep);
}
ClauseHead* Clause::newShared(Solver& s, SharedLiterals* sharedLits, const InfoType& e, const Literal* lits,
                              bool addRef) {
    return mt::SharedLitsClause::newClause(s, sharedLits, e, lits, addRef);
}

auto Clause::newContractedClause(Solver& s, const ClauseRep& rep, uint32_t tailStart, bool extend) -> ClauseHead* {
    assert(rep.size >= 2);
    auto mem = alloc(s, rep.size, rep.info.learnt());
    if (rep.size <= max_short_len) {
        return new (mem) SmallClause(s, rep);
    }
    if (extend) {
        Potassco::radixSort(
            std::span{rep.lits + tailStart, rep.lits + rep.size},
            [dl = s.decisionLevel(), &s](Literal p) {
                assert(s.value(p.var()) != value_free);
                return dl - s.level(p.var());
            },
            Potassco::radix_def, std::ref(s.temp()));
    }
    return new (mem) Clause(s, rep, tailStart, extend);
}
Clause::SmallClause::SmallClause(Solver& s, const ClauseRep& rep) : ClauseHead(rep.info) {
    std::memcpy(data_, rep.lits, rep.size * sizeof(Literal));
    assert(head() == data_ && rep.size == SmallClause::size());
    attach(s);
}
Clause::Clause(Solver& s, const ClauseRep& rep, uint32_t tail, bool extend) : ClauseHead(rep.info) {
    assert(tail >= rep.size || s.isFalse(rep.lits[tail]));
    setSize(rep.size);
    data_[1].rep() = 0u;
    auto* lits     = static_cast<Literal*>(std::memcpy(head(), rep.lits, rep.size * sizeof(Literal)));
    tail           = std::max(tail, head_lits);
    if (tail < rep.size) {         // contracted clause
        lits[rep.size - 1].flag(); // mark last literal of clause
        if (Literal t = lits[tail]; s.level(t.var()) > 0) {
            toggleContracted();
            if (extend) {
                s.addUndoWatch(s.level(t.var()), this);
            }
        }
        setSize(tail);
    }
    attach(s);
}
static auto cloneImpl(Solver& other, LitView lits, ConstraintInfo info) -> ClauseHead* {
    assert(not info.learnt());
    auto rep = ClauseRep::prepared({const_cast<Literal*>(lits.data()), size32(lits)}, info);
    return Clause::newClause(other, rep);
}
auto Clause::SmallClause::cloneAttach(Solver& other) -> ClauseHead* {
    return cloneImpl(other, SmallClause::toLits(), info_);
}
auto Clause::cloneAttach(Solver& other) -> ClauseHead* { return cloneImpl(other, Clause::toLits(), info_); }
void Clause::detach(Solver& s) {
    if (contracted()) {
        auto range = active();
        if (Literal* eoc = range.data() + range.size(); s.isFalse(*eoc) && s.level(eoc->var()) != 0) {
            s.removeUndoWatch(s.level(eoc->var()), this);
        }
    }
    ClauseHead::detach(s);
}
uint32_t Clause::computeAllocSize() const {
    uint32_t rt = sizeof(Clause) - (head_lits * sizeof(Literal));
    uint32_t sz = Clause::size();
    if (auto nw = static_cast<uint32_t>(contracted()) + static_cast<uint32_t>(shortened()); nw != 0u) {
        auto* head = this->head();
        auto* eoc  = head + sz;
        do { nw -= eoc++->flagged(); } while (nw);
        sz = static_cast<uint32_t>(eoc - head);
    }
    return rt + (sz * sizeof(Literal));
}
void Clause::SmallClause::destroy(Solver* s, bool detachFirst) {
    if (s) {
        if (detachFirst) {
            ClauseHead::detach(*s);
        }
        if (learnt()) {
            s->freeLearntBytes(32);
        }
    }
    void* mem = static_cast<Constraint*>(this);
    this->~SmallClause();
    if (s) {
        s->freeSmall(mem);
    }
}
void Clause::destroy(Solver* s, bool detachFirst) {
    if (s) {
        if (detachFirst) {
            Clause::detach(*s);
        }
        if (learnt()) {
            s->freeLearntBytes(computeAllocSize());
        }
    }
    void* mem = static_cast<Constraint*>(this);
    this->~Clause();
    Detail::free(mem);
}

bool Clause::SmallClause::updateWatch(Solver& s, Literal* head, uint32_t pos) {
    assert(head == data_);
    if (not s.isFalse(head[3])) {
        std::swap(head[pos], head[3]);
        return true;
    }
    if (not s.isFalse(head[4])) {
        std::swap(head[pos], head[4]);
        return true;
    }
    return false;
}
bool Clause::updateWatch(Solver& s, Literal* head, uint32_t pos) {
    assert(head == data_ + 2u);
    for (auto *it = head + head_lits, *begin = it, *end = head + Clause::size(), *first = begin + index();;) {
        for (it = first; it < end; ++it) {
            if (not s.isFalse(*it)) {
                std::swap(*it, head[pos]);
                setIndex(static_cast<uint32_t>(++it - begin));
                return true;
            }
        }
        if (first == begin) {
            break;
        }
        end   = first;
        first = begin;
    }
    return false;
}
static void reasonImpl(LitView cl, ConstraintInfo& info, Solver& s, Literal p, LitVec& out) {
    out.push_back(~cl[p == cl[0]]);
    for (auto x : cl.subspan(2u)) { out.push_back(~x); }
    if (info.learnt()) {
        s.updateOnReason(info.score(), p, out);
    }
}
void Clause::SmallClause::reason(Solver& s, Literal p, LitVec& out) {
    reasonImpl(SmallClause::toLits(), info_, s, p, out);
}
void Clause::reason(Solver& s, Literal p, LitVec& out) { reasonImpl(Clause::toLits(), info_, s, p, out); }

static bool minimizeImpl(LitView lits, const Solver& s, Literal p, CCMinRecursive* rec, ConstraintScore& sc,
                         bool contracted = false) {
    s.updateOnMinimize(sc);
    if (not s.ccMinimize(~lits[p == lits[0]], rec)) {
        return false;
    }
    if (not std::ranges::all_of(lits.subspan(2u), [&](Literal x) { return s.ccMinimize(~x, rec); })) {
        return false;
    }
    if (contracted) {
        const auto* end = lits.data() + lits.size();
        do {
            if (not s.ccMinimize(~*end, rec)) {
                return false;
            }
        } while (not end++->flagged());
    }
    return true;
}
static bool isReverseReasonImpl(LitView lits, const Solver& s, Literal p, uint32_t maxL, uint32_t maxN,
                                bool contracted = false) {
    uint32_t other = p == lits[0];
    if (not isRevLit(s, lits[other], maxL)) {
        return false;
    }
    if (uint32_t notSeen = not s.seen(lits[other].var()); notSeen <= maxN) {
        for (auto x : lits.subspan(2u)) {
            if (not isRevLit(s, x, maxL) || (not s.seen(x.var()) && ++notSeen > maxN)) {
                return false;
            }
        }
        if (contracted) {
            const auto* end = lits.data() + lits.size();
            do { notSeen += not s.seen(end->var()); } while (notSeen <= maxN && not end++->flagged());
        }
        return notSeen <= maxN;
    }
    return false;
}

bool Clause::SmallClause::minimize(Solver& s, Literal p, CCMinRecursive* rec) {
    return minimizeImpl(SmallClause::toLits(), s, p, rec, info_.score());
}
bool Clause::minimize(Solver& s, Literal p, CCMinRecursive* rec) {
    return minimizeImpl(active(), s, p, rec, info_.score(), contracted());
}
bool Clause::SmallClause::isReverseReason(const Solver& s, Literal p, uint32_t maxL, uint32_t maxN) {
    return isReverseReasonImpl(SmallClause::toLits(), s, p, maxL, maxN);
}
bool Clause::isReverseReason(const Solver& s, Literal p, uint32_t maxL, uint32_t maxN) {
    return isReverseReasonImpl(active(), s, p, maxL, maxN, contracted());
}
auto Clause::SmallClause::size() const -> uint32_t {
    static_assert(max_short_len == 5);
    if (data_[2] == lit_false) {
        return 2u;
    }
    if (data_[3] == lit_false) {
        return 3u;
    }
    if (data_[4] == lit_false) {
        return 4u;
    }
    return max_short_len;
}
auto Clause::SmallClause::toLits() const -> LitView { return {data_, SmallClause::size()}; }
auto Clause::toLits() const -> LitView {
    auto ret = const_cast<Clause*>(this)->active();
    if (contracted()) {
        auto end = ret.data() + ret.size();
        while (not end++->flagged()) {}
        ret = {ret.data(), end};
    }
    return ret; // NOLINT
}

static auto simplifyImpl(const Solver& s, std::span<Literal> lits) -> uint32_t {
    assert(s.decisionLevel() == 0 && s.queueSize() == 0);
    auto* it  = lits.data();
    auto* end = it + lits.size();
    // skip free literals
    while (it != end && s.value(it->var()) == value_free) { ++it; }
    auto* j = it;
    // copy remaining free literals
    for (; it != end; ++it) {
        if (s.value(it->var()) == value_free) {
            *j++ = *it;
        }
        else if (s.isTrue(*it)) {
            return 0u;
        }
    }
    // replace any false lits with sentinels
    for (auto* r = j; r != end; ++r) { *r = lit_false; }
    return static_cast<uint32_t>(j - lits.data());
}

bool Clause::SmallClause::simplify(Solver& s, bool) {
    auto sz = simplifyImpl(s, active());
    if (sz == 0u) {
        detach(s);
        return true;
    }
    return sz <= 3u && toImplication(s);
}
bool Clause::simplify(Solver& s, bool reinit) {
    auto range = active();
    auto sz    = simplifyImpl(s, range);
    if (sz == 0u) {
        Clause::detach(s);
        return true;
    }
    setIndex(0u);
    if (Clause::size() > sz) {
        if (learnt() && not shortened()) {
            // mark last literal so that we can recompute alloc size later
            range.back().flag();
            toggleShortened();
        }
        setSize(sz);
    }
    if (reinit && sz > 3) {
        detach(s);
        s.rng.shuffle(range.data(), range.data() + sz);
        attach(s);
    }
    return sz <= 3u && toImplication(s);
}

static auto isOpenImpl(const ClauseHead& head, std::span<Literal> range, const Solver& s, const TypeSet& x,
                       LitVec& freeLits) -> uint32_t {
    if (not x.contains(head.ClauseHead::type()) || head.satisfied(s)) {
        return 0;
    }
    assert(s.queueSize() == 0 && "Watches might be false!");
    freeLits.push_back(range[0]);
    freeLits.push_back(range[1]);
    for (Literal& r : range.subspan(2)) {
        if (auto v = s.value(r.var()); v == value_free) {
            freeLits.push_back(r);
        }
        else if (v == trueValue(r)) {
            std::swap(range[2], r);
            return 0;
        }
    }
    return +head.ClauseHead::type();
}
auto Clause::SmallClause::isOpen(const Solver& s, const TypeSet& x, LitVec& freeLits) -> uint32_t {
    return isOpenImpl(*this, active(), s, x, freeLits);
}
auto Clause::isOpen(const Solver& s, const TypeSet& x, LitVec& freeLits) -> uint32_t {
    return isOpenImpl(*this, active(), s, x, freeLits);
}

void Clause::undoLevel(Solver& s) {
    auto  ul    = s.jumpLevel();
    auto  range = active();
    auto* r     = range.data() + range.size();
    while (not r->flagged() && (s.value(r->var()) == value_free || s.level(r->var()) > ul)) { ++r; }
    if (r->flagged() || s.level(r->var()) == 0) {
        r->unflag();
        r += not isSentinel(*r);
        toggleContracted();
        assert(not contracted());
    }
    else {
        s.addUndoWatch(s.level(r->var()), this);
    }
    setSize(static_cast<uint32_t>(r - range.data()));
}
static auto strengthenImpl(ClauseHead& self, ConstraintInfo& info, std::span<Literal> range, Solver& s,
                           Literal p) -> std::pair<Literal*, Literal*> {
    auto lits = range.data();
    auto end  = lits + range.size();
    if (auto it = std::ranges::find(range.data(), end, p); it != end) {
        if (auto pos = static_cast<uint32_t>(it - range.data()); pos < 3u) {
            if (pos < 2u) {
                *it = lits[2];
                s.removeWatch(~p, &self);
                Literal* best = it;
                for (Literal* n = lits + ClauseHead::head_lits; n < end && s.isFalse(*best); ++n) {
                    if (not s.isFalse(*n) || s.level(n->var()) > s.level(best->var())) {
                        best = n;
                    }
                }
                std::swap(*it, *best);
                s.addWatch(~*it, &self);
                it = lits + 2;
            }
            if (range.size() > 3u) {
                *it++ = lits[3];
            }
        }
        if (~p == s.tagLiteral()) {
            info.setTagged(false);
        }
        return {it, end};
    }
    return {nullptr, end};
}

auto Clause::SmallClause::strengthen(Solver& s, Literal p, bool toShort) -> StrengthenResult {
    auto [found, end] = strengthenImpl(*this, info_, active(), s, p);
    if (found) {
        *found = *--end;
        *end   = lit_false;
    }
    auto sz = static_cast<uint32_t>(end - data_);
    return {.litRemoved = found != nullptr, .removeClause = toShort && sz <= 3u && toImplication(s)};
}
auto Clause::strengthen(Solver& s, Literal p, bool toShort) -> StrengthenResult {
    auto [found, end] = strengthenImpl(*this, info_, active(), s, p);
    if (not found && contracted()) {
        auto* pos = end;
        while (*pos != p && not pos->flagged()) { ++pos; }
        if (*pos == p) {
            found = pos;
        }
    }
    if (found) {
        if (not contracted()) {
            *found = *--end;
            *end   = lit_false;
            setSize(Clause::size() - 1u);
            setIndex(0u);
        }
        else {
            auto  uLev = s.level(end->var());
            auto* j    = found;
            while (not j->flagged()) { *j++ = *++found; }
            *j = lit_false;
            if (auto nLev = s.level(end->var()); uLev != nLev) {
                s.updateUndoWatch(uLev, this, nLev);
            }
            if (j != end) {
                (j - 1)->flag();
            }
            else {
                toggleContracted();
            }
            end = j;
        }
        if (learnt() && not shortened()) {
            end->flag();
            toggleShortened();
        }
    }
    auto sz = static_cast<uint32_t>(end - data_) - 2u;
    return {.litRemoved = found != nullptr, .removeClause = toShort && sz <= 3u && toImplication(s)};
}
/////////////////////////////////////////////////////////////////////////////////////////
// mt::SharedLitsClause
/////////////////////////////////////////////////////////////////////////////////////////
namespace mt {
ClauseHead* SharedLitsClause::newClause(Solver& s, SharedLiterals* sharedLits, const InfoType& e, const Literal* lits,
                                        bool addRef) {
    return new (s.allocSmall()) SharedLitsClause(s, sharedLits, lits, e, addRef);
}

SharedLitsClause::SharedLitsClause(Solver& s, SharedLiterals* sharedLits, const Literal* w, const InfoType& e,
                                   bool addRef)
    : ClauseHead(e) {
    static_assert(sizeof(SharedLitsClause) <= 32, "Unsupported Padding");
    auto* shared = addRef ? sharedLits->share() : sharedLits;
    std::memcpy(data_, w, std::min(head_lits, sharedLits->size()) * sizeof(Literal));
    std::memcpy(static_cast<void*>(data_ + head_lits), static_cast<void*>(&shared), sizeof(SharedLiterals*));
    assert(this->shared() == shared && head() == data_);
    attach(s);
    if (learnt()) {
        s.addLearntBytes(32);
    }
}
auto SharedLitsClause::shared() const -> SharedLiterals* {
    SharedLiterals* ret;
    std::memcpy(static_cast<void*>(&ret), static_cast<const void*>(data_ + head_lits), sizeof(SharedLiterals*));
    return ret;
}

auto SharedLitsClause::cloneAttach(Solver& other) -> ClauseHead* {
    return newClause(other, shared(), InfoType(this->type()), data_);
}

bool SharedLitsClause::updateWatch(Solver& s, Literal* head, uint32_t pos) {
#define REPLACE_CACHE_OR()                                                                                             \
    if (not s.isFalse(*++r) && *r != other) {                                                                          \
        head[2] = *r;                                                                                                  \
        assert(not r->flagged());                                                                                      \
        return true;                                                                                                   \
    }
    Literal other  = head[1 ^ pos];
    auto*   shared = this->shared();
    for (const Literal *r = shared->begin(), *end = shared->end(); r != end; ++r) {
        // at this point we know that head[2] is false, so we only need to check
        // that we do not watch the other watched literal twice!
        if (not s.isFalse(*r) && *r != other) {
            head[pos] = *r; // replace watch
            assert(not r->flagged());
            // try to replace cache literal
            // NOLINTBEGIN(bugprone-branch-clone)
            switch (std::min(static_cast<uint32_t>(8), static_cast<uint32_t>(end - r))) {
                case 8 : REPLACE_CACHE_OR() [[fallthrough]];
                case 7 : REPLACE_CACHE_OR() [[fallthrough]];
                case 6 : REPLACE_CACHE_OR() [[fallthrough]];
                case 5 : REPLACE_CACHE_OR() [[fallthrough]];
                case 4 : REPLACE_CACHE_OR() [[fallthrough]];
                case 3 : REPLACE_CACHE_OR() [[fallthrough]];
                case 2 : REPLACE_CACHE_OR() [[fallthrough]];
                default: return true;
            }
            // NOLINTEND(bugprone-branch-clone)
        }
    }
#undef REPLACE_CACHE_OR
    return false;
}

void SharedLitsClause::reason(Solver& s, Literal p, LitVec& out) {
    for (auto r : *shared()) {
        assert(s.isFalse(r) || r == p);
        if (r != p) {
            out.push_back(~r);
        }
    }
    if (learnt()) {
        s.updateOnReason(info_.score(), p, out);
    }
}

bool SharedLitsClause::minimize(Solver& s, Literal p, CCMinRecursive* rec) {
    s.updateOnMinimize(info_.score());
    return std::ranges::all_of(*shared(), [&](Literal r) { return r == p || s.ccMinimize(~r, rec); });
}

bool SharedLitsClause::isReverseReason(const Solver& s, Literal p, uint32_t maxL, uint32_t maxN) {
    uint32_t notSeen = 0;
    for (auto r : *shared()) {
        if (r == p) {
            continue;
        }
        if (not isRevLit(s, r, maxL)) {
            return false;
        }
        if (not s.seen(r.var()) && ++notSeen > maxN) {
            return false;
        }
    }
    return true;
}

bool SharedLitsClause::simplify(Solver& s, bool reinit) {
    if (satisfied(s)) {
        detach(s);
        return true;
    }
    if (uint32_t optSize = shared()->simplify(s); optSize == 0) {
        detach(s);
        return true;
    }
    else if (optSize <= max_short_len) {
        Literal  lits[max_short_len];
        Literal* j = lits;
        for (auto r : *shared()) {
            if (not s.isFalse(r)) {
                *j++ = r;
            }
        }
        // safe extra data
        InfoType myInfo = info_;
        // detach & destroy but do not release memory
        detach(s);
        SharedLitsClause::destroy(nullptr, false);
        // construct short clause in "this"
        void*       mem = std::launder(this);
        ClauseHead* h = Clause::newClause(mem, s, ClauseRep::prepared({lits, static_cast<uint32_t>(j - lits)}, myInfo));
        return h->simplify(s, reinit);
    }
    else if (auto* h = data_; s.isFalse(h[2])) {
        // try to replace cache lit with non-false literal
        for (auto r : *shared()) {
            if (not s.isFalse(r) && std::find(h, h + 2, r) == h + 2) {
                h[2] = r;
                break;
            }
        }
    }
    return false;
}

void SharedLitsClause::destroy(Solver* s, bool detachFirst) {
    if (s) {
        if (detachFirst) {
            ClauseHead::detach(*s);
        }
        if (learnt()) {
            s->freeLearntBytes(32);
        }
    }
    shared()->release();
    void* mem = this;
    this->~SharedLitsClause();
    if (s) {
        s->freeSmall(mem);
    }
}

auto SharedLitsClause::isOpen(const Solver& s, const TypeSet& x, LitVec& freeLits) -> uint32_t {
    if (not x.contains(ClauseHead::type()) || satisfied(s)) {
        return 0;
    }
    Literal* head = data_;
    for (auto r : *shared()) {
        if (auto v = s.value(r.var()); v == value_free) {
            freeLits.push_back(r);
        }
        else if (v == trueValue(r)) {
            head[2] = r; // remember as cache literal
            return 0;
        }
    }
    return +ClauseHead::type();
}

auto SharedLitsClause::toLits() const -> LitView { return shared()->literals(); }

auto SharedLitsClause::strengthen(Solver&, Literal, bool) -> StrengthenResult { return {}; }

auto SharedLitsClause::size() const -> uint32_t { return shared()->size(); }
} // end namespace mt

/////////////////////////////////////////////////////////////////////////////////////////
// LoopFormula
/////////////////////////////////////////////////////////////////////////////////////////
auto LoopFormula::newLoopFormula(Solver& s, const ClauseRep& c1, LitView atoms, bool heu) -> LoopFormula* {
    uint32_t bytes = sizeof(LoopFormula) + (c1.size + size32(atoms) + 2) * sizeof(Literal);
    void*    mem   = Detail::alloc(bytes);
    s.addLearntBytes(bytes);
    return new (mem) LoopFormula(s, c1, atoms, heu);
}
LoopFormula::LoopFormula(Solver& s, const ClauseRep& c1, LitView atoms, bool heu) {
    act_     = c1.info.score();
    lits_[0] = lit_true; // Starting sentinel
    std::memcpy(lits_ + 1, c1.lits, c1.size * sizeof(Literal));
    lits_[end_ = c1.size + 1] = lit_true; // Ending sentinel
    s.addWatch(~lits_[2], this, (2 << 1) + 1);
    lits_[2].flag();
    size_  = c1.size + size32(atoms) + 2;
    str_   = 0;
    xPos_  = 1;
    other_ = 1;
    for (uint32_t x = end_ + 1; auto a : atoms) {
        act_.bumpActivity();
        s.addWatch(~(lits_[x++] = a), this, (1 << 1) + 1);
        if (heu) {
            lits_[1] = a;
            s.heuristic()->newConstraint(s, {lits_ + 1, c1.size}, ConstraintType::loop);
        }
    }
    (lits_[1] = c1.lits[0]).flag();
}
void LoopFormula::destroy(Solver* s, bool detach) {
    if (s) {
        if (detach) {
            this->detach(*s);
        }
        if (str_) {
            while (lits_[size_++].rep() != 3u) { ; }
        }
        s->freeLearntBytes(sizeof(LoopFormula) + (size_ * sizeof(Literal)));
    }
    void* mem = static_cast<Constraint*>(this);
    this->~LoopFormula();
    Detail::free(mem);
}
void LoopFormula::detach(Solver& s) {
    for (Literal* it = begin() + xPos_; not isSentinel(*it); ++it) {
        if (it->flagged()) {
            s.removeWatch(~*it, this);
            it->unflag();
        }
    }
    for (auto lit : xSpan()) { s.removeWatch(~lit, this); }
}
bool LoopFormula::otherIsSat(const Solver& s) {
    if (other_ != xPos_) {
        return s.isTrue(lits_[other_]);
    }
    if (not s.isTrue(lits_[other_])) {
        return false;
    }
    for (auto lit : xSpan()) {
        if (not s.isTrue(lit)) {
            if (lits_[xPos_].flagged()) {
                (lits_[xPos_] = lit).flag();
            }
            else {
                lits_[xPos_] = lit;
            }
            return false;
        }
    }
    return true;
}
auto LoopFormula::propagate(Solver& s, Literal p, uint32_t& data) -> PropResult {
    if (otherIsSat(s)) { // already satisfied?
        return PropResult(true, true);
    }
    uint32_t idx  = data >> 1;
    Literal* w    = lits_ + idx;
    bool     head = idx == xPos_;
    if (head) { // p is one of the atoms - move to active part
        p = ~p;
        if (*w != p && s.isFalse(*w)) {
            return PropResult(true, true);
        }
        if (not w->flagged()) {
            *w = p;
            return PropResult(true, true);
        }
        (*w = p).flag();
    }
    for (int bounds = 0, dir = static_cast<int>((data & 1) << 1) - 1;;) {
        // search non-false literal - sentinels guarantee termination
        for (w += dir; s.isFalse(*w); w += dir) { ; }
        if (not isSentinel(*w)) {
            auto nIdx = static_cast<uint32_t>(w - lits_);
            // other watched literal?
            if (w->flagged()) {
                other_ = nIdx;
                continue;
            }
            // replace watch
            lits_[idx].unflag();
            w->flag();
            // add new watch only w is not one of the atoms
            // and keep previous watch if p is one of the atoms
            if (nIdx != xPos_) {
                s.addWatch(~*w, this, (nIdx << 1) + (dir == 1));
            }
            return PropResult(true, head);
        }
        else if (++bounds == 1) {
            w     = lits_ + idx; // Halfway through, restart search, but
            dir  *= -1;          // this time walk in the opposite direction.
            data ^= 1;           // Save new direction of watch
        }
        else { // clause is unit
            bool ok = s.force(lits_[other_], this);
            if (other_ == xPos_ && ok) { // all lits in inactive part are implied
                for (auto lit : xSpan()) {
                    if (ok = s.force(lit, this); not ok) {
                        break;
                    }
                }
            }
            return PropResult(ok, true);
        }
    }
}
void LoopFormula::reason(Solver& s, Literal p, LitVec& lits) {
    // p = body: all literals in active clause
    // p = atom: only bodies
    for (Literal* it = begin() + (other_ == xPos_); not isSentinel(*it); ++it) {
        if (*it != p) {
            lits.push_back(~*it);
        }
    }
    s.updateOnReason(act_, p, lits);
}
bool LoopFormula::minimize(Solver& s, Literal p, CCMinRecursive* rec) {
    s.updateOnMinimize(act_);
    for (Literal* it = begin() + (other_ == xPos_); not isSentinel(*it); ++it) {
        if (*it != p && not s.ccMinimize(~*it, rec)) {
            return false;
        }
    }
    return true;
}
auto LoopFormula::size() const -> uint32_t { return size_ - (2u + xPos_); }
bool LoopFormula::locked(const Solver& s) const {
    if (other_ != xPos_ || not s.isTrue(lits_[other_])) {
        return s.isTrue(lits_[other_]) && s.reason(lits_[other_]) == this;
    }
    auto& self = const_cast<LoopFormula&>(*this);
    return std::ranges::any_of(self.xSpan(), [&](Literal lit) { return s.isTrue(lit) && s.reason(lit) == this; });
}
auto LoopFormula::isOpen(const Solver& s, const TypeSet& xs, LitVec& freeLits) -> uint32_t {
    if (not xs.contains(ConstraintType::loop) || otherIsSat(s)) {
        return 0;
    }
    for (Literal* it = begin() + xPos_; not isSentinel(*it); ++it) {
        if (s.value(it->var()) == value_free) {
            freeLits.push_back(*it);
        }
        else if (s.isTrue(*it)) {
            other_ = static_cast<uint32_t>(it - lits_);
            return 0;
        }
    }
    for (auto lit : xSpan()) {
        if (s.value(lit.var()) == value_free) {
            freeLits.push_back(lit);
        }
    }
    return +ConstraintType::loop;
}
bool LoopFormula::simplify(Solver& s, bool) {
    if (otherIsSat(s) || (other_ != xPos_ && (other_ = xPos_) != 0 && otherIsSat(s))) {
        detach(s);
        return true;
    }
    Literal *it = begin(), *j, *end = xEnd();
    while (s.value(it->var()) == value_free) { ++it; }
    if (j = it; not isSentinel(*j)) {
        // simplify active clause
        if (*it == lits_[xPos_]) {
            xPos_ = 0;
        }
        for (GenericWatch* w; not isSentinel(*it); ++it) {
            if (s.value(it->var()) == value_free) {
                if (it->flagged() && (w = s.getWatch(~*it, this)) != nullptr) {
                    w->data = (static_cast<uint32_t>(j - lits_) << 1) + (w->data & 1);
                }
                *j++ = *it;
            }
            else if (s.isTrue(*it)) {
                detach(s);
                return true;
            }
            else {
                assert(not it->flagged() && "Constraint not propagated!");
            }
        }
        *j   = lit_true;
        end_ = static_cast<uint32_t>(j - lits_);
    }
    // simplify extra part
    for (++it, ++j; it != end; ++it) {
        if (s.value(it->var()) == value_free && xPos_) {
            *j++ = *it;
        }
        else {
            s.removeWatch(~*it, this);
        }
    }
    bool isClause = static_cast<uint32_t>(j - xBegin()) == 1;
    if (isClause) {
        --j;
    }
    if (j != end) { // size changed?
        if (not str_) {
            (end - 1)->rep() = 3u;
            str_             = 1u;
        }
        if (isClause) {
            assert(xPos_ && *j == lits_[xPos_]);
            if (not lits_[xPos_].flagged()) {
                s.removeWatch(~*j, this);
            }
            xPos_ = 0;
        }
        size_ = static_cast<uint32_t>((end = j) - lits_);
    }
    assert(not isClause || xPos_ == 0);
    other_        = xPos_ + 1;
    ClauseRep act = ClauseRep::create({begin(), end_ - 1}, ConstraintType::loop);
    POTASSCO_ASSERT(act.size > 1);
    if (s.allowImplicit(act)) {
        detach(s);
        act.prep = 1;
        for (auto lit : xPos_ ? xSpan() : std::span{begin(), 1u}) {
            POTASSCO_ASSERT(s.value(lit.var()) == value_free);
            lits_[xPos_] = lit;
            auto res     = ClauseCreator::create(s, act, ClauseCreator::clause_no_add);
            POTASSCO_ASSERT(res.ok() && not res.local, "LOOP MUST NOT CONTAIN AUX VARS!");
        }
        return true;
    }
    return false;
}

} // namespace Clasp
