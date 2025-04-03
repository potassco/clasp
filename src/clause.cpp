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

static void* alloc(std::size_t size) {
    POTASSCO_PRAGMA_TODO("replace with CACHE_LINE_ALIGNED alloc")
    return ::operator new(size);
}
static void free(void* mem) { ::operator delete(mem); }
using SharedLitsPtr = std::unique_ptr<SharedLiterals, ReleaseObject>;

} // namespace Detail

/////////////////////////////////////////////////////////////////////////////////////////
// SharedLiterals
/////////////////////////////////////////////////////////////////////////////////////////
SharedLiterals* SharedLiterals::newShareable(LitView lits, ConstraintType t, uint32_t numRefs) {
    void* m = Detail::alloc(sizeof(SharedLiterals) + (lits.size() * sizeof(Literal)));
    return new (m) SharedLiterals(lits, t, numRefs);
}

SharedLiterals::SharedLiterals(LitView lits, ConstraintType t, uint32_t refs)
    : refCount_(std::max(1u, refs))
    , size_type_((size32(lits) << 2) + +t) {
    std::memcpy(lits_, lits.data(), lits.size() * sizeof(Literal));
}

uint32_t SharedLiterals::simplify(Solver& s) {
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
        size_type_ = (newSize << 2) | (size_type_ & 3u);
    }
    return newSize;
}

void SharedLiterals::release(int n) {
    if (n > 0 && refCount_.release(static_cast<uint32_t>(n))) {
        this->~SharedLiterals();
        Detail::free(this);
    }
}
SharedLiterals* SharedLiterals::share() {
    refCount_.add();
    return this;
}
/////////////////////////////////////////////////////////////////////////////////////////
// ClauseCreator
/////////////////////////////////////////////////////////////////////////////////////////
ClauseCreator::ClauseCreator(Solver* s) : solver_(s), flags_{} {}

ClauseCreator& ClauseCreator::start(ConstraintType t) {
    assert(solver_ && (solver_->decisionLevel() == 0 || t != ConstraintType::static_));
    literals_.clear();
    extra_ = ConstraintInfo(t);
    return *this;
}

uint32_t ClauseCreator::watchOrder(const Solver& s, Literal p) {
    auto value_p = s.value(p.var());
    if (value_p == value_free) { // DL+1,  if isFree(p)
        return s.decisionLevel() + 1;
    }
    // DL(p), if isFalse(p)
    // ~DL(p),if isTrue(p)
    return s.level(p.var()) ^ static_cast<uint32_t>(0 - (value_p == trueValue(p)));
}
ClauseRep ClauseCreator::prepare(Solver& s, LitView in, const ConstraintInfo& e, CreateFlag flags,
                                 std::span<Literal> out) {
    assert(not out.empty() || in.empty());
    ClauseRep ret     = ClauseRep::prepared({out.data(), 0u}, e);
    uint32_t  abst_w1 = 0, abst_w2 = 0;
    bool      simplify = Potassco::test(flags, clause_force_simplify) && out.size() >= in.size();
    Literal   tag      = ~s.tagLiteral();
    Var_t     vMax     = s.numProblemVars() > s.numVars() && not in.empty() ? std::ranges::max_element(in)->var() : 0;
    s.acquireProblemVar(vMax);
    for (uint32_t j = 0, max_out = size32(out) - 1; auto p : in) {
        auto abst_p = watchOrder(s, p);
        if ((abst_p + 1) > 1 && (not simplify || not s.seen(p.var()))) {
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
            if (abst_p > abst_w1) {
                std::swap(abst_p, abst_w1);
                std::swap(out[0], out[j]);
            }
            if (abst_p > abst_w2) {
                std::swap(abst_p, abst_w2);
                std::swap(out[1], out[j]);
            }
            if (j != max_out) {
                ++j;
            }
            ++ret.size;
        }
        else if (abst_p == UINT32_MAX || (simplify && abst_p && s.seen(~p))) {
            abst_w1 = UINT32_MAX;
            break;
        }
    }
    if (simplify) {
        assert(ret.size <= size32(out));
        for (auto x : irange(ret.size)) { s.clearSeen(out[x].var()); }
    }
    if (abst_w1 == UINT32_MAX || (abst_w2 && out[0].var() == out[1].var())) {
        out[0]   = abst_w1 == UINT32_MAX || out[0] == ~out[1] ? lit_true : out[0];
        ret.size = 1;
    }
    ret.info.setAux(s.auxVar(vMax));
    return ret;
}

ClauseRep ClauseCreator::prepare(Solver& s, LitVec& lits, CreateFlag flags, const ConstraintInfo& info) {
    if (lits.empty()) {
        lits.push_back(lit_false);
    }
    if (not Potassco::test(flags, clause_no_prepare) || Potassco::test(flags, clause_force_simplify)) {
        ClauseRep x = prepare(s, lits, info, flags, lits);
        shrinkVecTo(lits, x.size);
        return x;
    }
    return ClauseRep::prepared(lits, info);
}

ClauseRep ClauseCreator::prepare(bool forceSimplify) {
    return prepare(*solver_, literals_, forceSimplify ? clause_force_simplify : CreateFlag{}, extra_);
}

ClauseCreator::Status ClauseCreator::status(const Solver& s, LitView lits) {
    if (lits.empty()) {
        return status_empty;
    }
    Literal temp[3];
    auto    x = prepare(const_cast<Solver&>(s), lits, ConstraintInfo(), {}, temp);
    return statusPrepared(s, x);
}

ClauseCreator::Status ClauseCreator::status(const Solver& s, const ClauseRep& c) {
    return c.prep ? statusPrepared(s, c) : status(s, c.literals());
}

ClauseCreator::Status ClauseCreator::statusPrepared(const Solver& s, const ClauseRep& c) {
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

ClauseCreator::Result ClauseCreator::end(CreateFlag flags) {
    assert(solver_);
    flags |= flags_;
    return createPrepared(*solver_, prepare(*solver_, literals_, flags, extra_), flags);
}

ClauseHead* ClauseCreator::newProblemClause(Solver& s, const ClauseRep& clause, CreateFlag flags) {
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

ClauseHead* ClauseCreator::newLearntClause(Solver& s, const ClauseRep& clause, CreateFlag flags) {
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

ClauseCreator::Result ClauseCreator::createPrepared(Solver& s, const ClauseRep& clause, CreateFlag flags) {
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

ClauseCreator::Result ClauseCreator::create(Solver& s, LitVec& lits, CreateFlag flags, const ConstraintInfo& extra) {
    return createPrepared(s, prepare(s, lits, flags, extra), flags);
}

ClauseCreator::Result ClauseCreator::create(Solver& s, const ClauseRep& rep, CreateFlag flags) {
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
ClauseCreator::Result ClauseCreator::integrate(Solver& s, SharedLiterals* clause, CreateFlag modeFlags) {
    return integrate(s, clause, modeFlags, clause->type());
}
/////////////////////////////////////////////////////////////////////////////////////////
// Clause
/////////////////////////////////////////////////////////////////////////////////////////
void* Clause::alloc(Solver& s, uint32_t lits, bool learnt) {
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

ClauseHead* Clause::newClause(void* mem, Solver& s, const ClauseRep& rep) {
    assert(rep.size >= 2 && mem);
    return new (mem) Clause(s, rep);
}

ClauseHead* Clause::newShared(Solver& s, SharedLiterals* shared_lits, const InfoType& e, const Literal* lits,
                              bool addRef) {
    return mt::SharedLitsClause::newClause(s, shared_lits, e, lits, addRef);
}

ClauseHead* Clause::newContractedClause(Solver& s, const ClauseRep& rep, uint32_t tailStart, bool extend) {
    assert(rep.size >= 2);
    if (extend) {
        std::stable_sort(rep.lits + tailStart, rep.lits + rep.size, [&s](const Literal& p1, const Literal& p2) {
            assert(s.value(p1.var()) != value_free && s.value(p2.var()) != value_free);
            return s.level(p1.var()) > s.level(p2.var());
        });
    }
    return new (alloc(s, rep.size, rep.info.learnt())) Clause(s, rep, tailStart, extend);
}
void ClauseHead::Local::init(uint32_t sz) {
    std::memset(mem, 0, sizeof(mem));
    if (sz > max_short_len) {
        mem[0] = (sz << 3) + 1;
    }
    assert(isSmall() == (sz <= ClauseHead::max_short_len));
}
Clause::Clause(Solver& s, const ClauseRep& rep, uint32_t tail, bool extend) : ClauseHead(rep.info) {
    assert(tail >= rep.size || s.isFalse(rep.lits[tail]));
    local_.init(rep.size);
    if (not isSmall()) {
        // copy literals
        auto* lits = static_cast<Literal*>(std::memcpy(head_, rep.lits, rep.size * sizeof(Literal)));
        tail       = std::max(tail, head_lits);
        if (tail < rep.size) {         // contracted clause
            lits[rep.size - 1].flag(); // mark last literal of clause
            if (Literal t = lits[tail]; s.level(t.var()) > 0) {
                local_.markContracted();
                if (extend) {
                    s.addUndoWatch(s.level(t.var()), this);
                }
            }
            local_.setSize(tail);
        }
    }
    else {
        std::memcpy(head_, rep.lits, std::min(rep.size, head_lits) * sizeof(Literal));
        small()[0] = rep.size > head_lits ? rep.lits[head_lits] : lit_false;
        small()[1] = rep.size > head_lits + 1 ? rep.lits[head_lits + 1] : lit_false;
        assert(isSmall() && Clause::size() == rep.size);
    }
    attach(s);
}

Clause::Clause(Solver& s, const Clause& other) : ClauseHead(other.info_) {
    uint32_t oSize = other.size();
    local_.init(oSize);
    if (not isSmall()) {
        std::memcpy(head_, other.head_, oSize * sizeof(Literal));
    }
    else if (other.isSmall()) {
        std::memcpy(&local_, &other.local_, (max_short_len + 1) * sizeof(Literal));
    }
    else { // this is small, other is not
        std::memcpy(head_, other.head_, head_lits * sizeof(Literal));
        std::memcpy(&local_, other.head_ + head_lits, 2 * sizeof(Literal));
    }
    attach(s);
}

ClauseHead* Clause::cloneAttach(Solver& other) {
    assert(not learnt());
    return new (alloc(other, Clause::size(), false)) Clause(other, *this);
}
Literal* Clause::small() { return reinterpret_cast<Literal*>(local_.mem); }
bool     Clause::contracted() const { return local_.contracted(); }
bool     Clause::isSmall() const { return local_.isSmall(); }
bool     Clause::strengthened() const { return local_.strengthened(); }
void     Clause::destroy(Solver* s, bool detachFirst) {
    if (s) {
        if (detachFirst) {
            Clause::detach(*s);
        }
        if (learnt()) {
            s->freeLearntBytes(computeAllocSize());
        }
    }
    void* mem   = static_cast<Constraint*>(this);
    bool  small = isSmall();
    this->~Clause();
    if (not small) {
        Detail::free(mem);
    }
    else if (s) {
        s->freeSmall(mem);
    }
}

void Clause::detach(Solver& s) {
    if (contracted()) {
        if (Literal* eoc = end(); s.isFalse(*eoc) && s.level(eoc->var()) != 0) {
            s.removeUndoWatch(s.level(eoc->var()), this);
        }
    }
    ClauseHead::detach(s);
}

uint32_t Clause::computeAllocSize() const {
    if (isSmall()) {
        return 32;
    }
    uint32_t rt = sizeof(Clause) - (head_lits * sizeof(Literal));
    uint32_t sz = local_.size();
    if (auto nw = contracted() + strengthened(); nw != 0u) {
        const Literal* eoc = head_ + sz;
        do { nw -= eoc++->flagged(); } while (nw);
        sz = static_cast<uint32_t>(eoc - head_);
    }
    return rt + (sz * sizeof(Literal));
}

bool Clause::updateWatch(Solver& s, uint32_t pos) {
    Literal* it;
    if (not isSmall()) {
        for (Literal *begin = head_ + head_lits, *end = this->end(), *first = begin + local_.mem[1];;) {
            for (it = first; it < end; ++it) {
                if (not s.isFalse(*it)) {
                    std::swap(*it, head_[pos]);
                    local_.mem[1] = static_cast<uint32_t>(++it - begin);
                    return true;
                }
            }
            if (first == begin) {
                break;
            }
            end   = first;
            first = begin;
        }
    }
    else if (it = this->small(); not s.isFalse(*it) || not s.isFalse(*++it)) {
#if defined(__GNUC__) && __GNUC__ == 7 && __GNUC_MINOR__ < 2
        // Add compiler barrier to prevent gcc Bug 81365:
        // https://gcc.gnu.org/bugzilla/show_bug.cgi?id=81365
        asm volatile("" ::: "memory");
#endif
        std::swap(head_[pos], *it);
        return true;
    }
    return false;
}
Clause::Tail Clause::tail() {
    if (not isSmall()) {
        return {head_ + head_lits, end()};
    }
    Literal *tBeg = small(), *tEnd = tBeg;
    tEnd += *tEnd != lit_false;
    tEnd += *tEnd != lit_false;
    return {tBeg, tEnd};
}
void Clause::reason(Solver& s, Literal p, LitVec& out) {
    out.push_back(~head_[p == head_[0]]);
    if (not isSentinel(head_[2])) {
        out.push_back(~head_[2]);
        auto t = tail();
        for (auto r : t) { out.push_back(~r); }
        if (contracted()) {
            const Literal* r = t.end();
            do { out.push_back(~*r); } while (not r++->flagged());
        }
    }
    if (learnt()) {
        s.updateOnReason(info_.score(), p, out);
    }
}

bool Clause::minimize(Solver& s, Literal p, CCMinRecursive* rec) {
    s.updateOnMinimize(info_.score());
    uint32_t other = p == head_[0];
    if (not s.ccMinimize(~head_[other], rec) || not s.ccMinimize(~head_[2], rec)) {
        return false;
    }
    auto t = tail();
    for (auto r : t) {
        if (not s.ccMinimize(~r, rec)) {
            return false;
        }
    }
    if (contracted()) {
        const Literal* r = t.end();
        do {
            if (not s.ccMinimize(~*r, rec)) {
                return false;
            }
        } while (not r++->flagged());
    }
    return true;
}

bool Clause::isReverseReason(const Solver& s, Literal p, uint32_t maxL, uint32_t maxN) {
    uint32_t other = p == head_[0];
    if (not isRevLit(s, head_[other], maxL) || not isRevLit(s, head_[2], maxL)) {
        return false;
    }
    if (uint32_t notSeen = not s.seen(head_[other].var()) + not s.seen(head_[2].var()); notSeen <= maxN) {
        auto t = tail();
        for (auto r : t) {
            if (not isRevLit(s, r, maxL) || (not s.seen(r.var()) && ++notSeen > maxN)) {
                return false;
            }
        }
        if (contracted()) {
            const Literal* r = t.end();
            do { notSeen += not s.seen(r->var()); } while (notSeen <= maxN && not r++->flagged());
        }
        return notSeen <= maxN;
    }
    return false;
}

bool Clause::simplify(Solver& s, bool reinit) {
    assert(s.decisionLevel() == 0 && s.queueSize() == 0);
    if (satisfied(s)) {
        detach(s);
        return true;
    }
    auto     t  = tail();
    Literal *it = t.begin() - not isSmall(), *j, *eot = t.end();
    // skip free literals
    while (it != eot && s.value(it->var()) == value_free) { ++it; }
    // copy remaining free literals
    for (j = it; it != eot; ++it) {
        if (s.value(it->var()) == value_free) {
            *j++ = *it;
        }
        else if (s.isTrue(*it)) {
            Clause::detach(s);
            return true;
        }
    }
    // replace any false lits with sentinels
    for (Literal* r = j; r != eot; ++r) { *r = lit_false; }
    if (not isSmall()) {
        uint32_t size = std::max(head_lits, static_cast<uint32_t>(j - head_));
        local_.setSize(size);
        local_.clearIdx();
        if (j != eot && learnt() && not strengthened()) {
            // mark last literal so that we can recompute alloc size later
            eot[-1].flag();
            local_.markStrengthened();
        }
        if (reinit && size > 3) {
            detach(s);
            s.rng.shuffle(head_, j);
            attach(s);
        }
    }
    else if (s.isFalse(head_[2])) {
        head_[2] = t.b[0];
        t.b[0]   = t.b[1];
        t.b[1]   = lit_false;
        --j;
    }
    return j <= t.begin() && toImplication(s);
}

uint32_t Clause::isOpen(const Solver& s, const TypeSet& x, LitVec& freeLits) {
    if (not x.contains(ClauseHead::type()) || satisfied(s)) {
        return 0;
    }
    assert(s.queueSize() == 0 && "Watches might be false!");
    freeLits.push_back(head_[0]);
    freeLits.push_back(head_[1]);
    if (not s.isFalse(head_[2])) {
        freeLits.push_back(head_[2]);
    }
    for (Literal& r : tail()) {
        if (auto v = s.value(r.var()); v == value_free) {
            freeLits.push_back(r);
        }
        else if (v == trueValue(r)) {
            std::swap(head_[2], r);
            return 0;
        }
    }
    return +ClauseHead::type();
}

void Clause::undoLevel(Solver& s) {
    assert(not isSmall());
    uint32_t t  = local_.size();
    uint32_t ul = s.jumpLevel();
    Literal* r  = head_ + t;
    while (not r->flagged() && (s.value(r->var()) == value_free || s.level(r->var()) > ul)) {
        ++t;
        ++r;
    }
    if (r->flagged() || s.level(r->var()) == 0) {
        r->unflag();
        t += not isSentinel(*r);
        local_.clearContracted();
    }
    else {
        s.addUndoWatch(s.level(r->var()), this);
    }
    local_.setSize(t);
}

LitView Clause::toLits(SmallBuffer& tmp) const {
    if (not isSmall()) {
        const auto* eoc = const_cast<Clause&>(*this).end();
        if (contracted()) {
            while (not eoc++->flagged()) {}
        }
        return {head_, eoc};
    }
    auto x = std::copy(head_, (head_ + head_lits) - isSentinel(head_[2]), tmp.data());
    if (const auto* eoc = const_cast<Clause&>(*this).small(); *eoc != lit_false) {
        *x++ = *eoc++;
        if (*eoc != lit_false) {
            *x++ = *eoc;
        }
    }
    return {tmp.data(), x};
}

ClauseHead::StrengthenResult Clause::strengthen(Solver& s, Literal p, bool toShort) {
    auto  t      = tail();
    auto* eoh    = head_ + head_lits;
    auto* eot    = t.end();
    auto* it     = std::find(head_, eoh, p);
    auto  litRem = false;
    if (it != eoh) {
        if (it != head_ + 2) { // update watch
            *it = head_[2];
            s.removeWatch(~p, this);
            Literal* best = it;
            for (Literal* n = t.begin(); n != eot && s.isFalse(*best); ++n) {
                if (not s.isFalse(*n) || s.level(n->var()) > s.level(best->var())) {
                    best = n;
                }
            }
            std::swap(*it, *best);
            s.addWatch(~*it, ClauseWatch(this));
            it = head_ + 2;
        }
        // replace cache literal with literal from tail
        if (*it = *t.begin(); *it != lit_false) {
            eot = removeFromTail(s, t.begin(), eot);
        }
        litRem = true;
    }
    else if (it = std::find(t.begin(), eot, p); it != eot) {
        eot    = removeFromTail(s, it, eot);
        litRem = true;
    }
    else if (contracted()) {
        for (; *it != p && not it->flagged(); ++it) { ; }
        litRem = (*it == p);
        eot    = *it == p ? removeFromTail(s, it, eot) : it + 1;
    }
    if (litRem && ~p == s.tagLiteral()) {
        clearTagged();
    }
    return {.litRemoved = litRem, .removeClause = toShort && eot == t.begin() && toImplication(s)};
}

Literal* Clause::removeFromTail(Solver& s, Literal* it, Literal* end) {
    assert(it != end || contracted());
    if (not contracted()) {
        *it  = *--end;
        *end = lit_false;
        if (not isSmall()) {
            local_.setSize(local_.size() - 1);
            local_.clearIdx();
        }
    }
    else {
        uint32_t uLev = s.level(end->var());
        Literal* j    = it;
        while (not j->flagged()) { *j++ = *++it; }
        *j            = lit_false;
        uint32_t nLev = s.level(end->var());
        if (uLev != nLev && s.removeUndoWatch(uLev, this) && nLev != 0) {
            s.addUndoWatch(nLev, this);
        }
        if (j != end) {
            (j - 1)->flag();
        }
        else {
            local_.clearContracted();
        }
        end = j;
    }
    if (learnt() && not isSmall() && not strengthened()) {
        end->flag();
        local_.markStrengthened();
    }
    return end;
}
uint32_t Clause::size() const {
    auto t = const_cast<Clause&>(*this).tail();
    return not isSentinel(head_[2]) ? 3u + t.size() : 2u;
}
/////////////////////////////////////////////////////////////////////////////////////////
// mt::SharedLitsClause
/////////////////////////////////////////////////////////////////////////////////////////
namespace mt {
ClauseHead* SharedLitsClause::newClause(Solver& s, SharedLiterals* shared_lits, const InfoType& e, const Literal* lits,
                                        bool addRef) {
    return new (s.allocSmall()) SharedLitsClause(s, shared_lits, lits, e, addRef);
}

SharedLitsClause::SharedLitsClause(Solver& s, SharedLiterals* shared_lits, const Literal* w, const InfoType& e,
                                   bool addRef)
    : ClauseHead(e) {
    static_assert(sizeof(SharedLitsClause) <= 32, "Unsupported Padding");
    shared_ = addRef ? shared_lits->share() : shared_lits;
    std::memcpy(head_, w, std::min(head_lits, shared_lits->size()) * sizeof(Literal));
    attach(s);
    if (learnt()) {
        s.addLearntBytes(32);
    }
}

ClauseHead* SharedLitsClause::cloneAttach(Solver& other) {
    return newClause(other, shared_, InfoType(this->type()), head_);
}

bool SharedLitsClause::updateWatch(Solver& s, uint32_t pos) {
#define REPLACE_CACHE_OR()                                                                                             \
    if (not s.isFalse(*++r) && *r != other) {                                                                          \
        head_[2] = *r;                                                                                                 \
        return true;                                                                                                   \
    }
    Literal other = head_[1 ^ pos];
    for (const Literal *r = shared_->begin(), *end = shared_->end(); r != end; ++r) {
        // at this point we know that head_[2] is false, so we only need to check
        // that we do not watch the other watched literal twice!
        if (not s.isFalse(*r) && *r != other) {
            head_[pos] = *r; // replace watch
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
    for (auto r : *shared_) {
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
    return std::ranges::all_of(*shared_, [&](Literal r) { return r == p || s.ccMinimize(~r, rec); });
}

bool SharedLitsClause::isReverseReason(const Solver& s, Literal p, uint32_t maxL, uint32_t maxN) {
    uint32_t notSeen = 0;
    for (auto r : *shared_) {
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
    if (uint32_t optSize = shared_->simplify(s); optSize == 0) {
        detach(s);
        return true;
    }
    else if (optSize <= max_short_len) {
        Literal  lits[max_short_len];
        Literal* j = lits;
        for (auto r : *shared_) {
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
    else if (s.isFalse(head_[2])) {
        // try to replace cache lit with non-false literal
        for (auto r : *shared_) {
            if (not s.isFalse(r) && std::find(head_, head_ + 2, r) == head_ + 2) {
                head_[2] = r;
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
    shared_->release();
    void* mem = this;
    this->~SharedLitsClause();
    if (s) {
        s->freeSmall(mem);
    }
}

uint32_t SharedLitsClause::isOpen(const Solver& s, const TypeSet& x, LitVec& freeLits) {
    if (not x.contains(ClauseHead::type()) || satisfied(s)) {
        return 0;
    }
    Literal* head = head_;
    for (auto r : *shared_) {
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

LitView SharedLitsClause::toLits(SmallBuffer&) const { return {shared_->begin(), shared_->end()}; }

ClauseHead::StrengthenResult SharedLitsClause::strengthen(Solver&, Literal, bool) { return {}; }

uint32_t SharedLitsClause::size() const { return shared_->size(); }
} // end namespace mt

/////////////////////////////////////////////////////////////////////////////////////////
// LoopFormula
/////////////////////////////////////////////////////////////////////////////////////////
LoopFormula* LoopFormula::newLoopFormula(Solver& s, const ClauseRep& c1, LitView atoms, bool heu) {
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
Constraint::PropResult LoopFormula::propagate(Solver& s, Literal p, uint32_t& data) {
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
uint32_t LoopFormula::size() const { return size_ - (2u + xPos_); }
bool     LoopFormula::locked(const Solver& s) const {
    if (other_ != xPos_ || not s.isTrue(lits_[other_])) {
        return s.isTrue(lits_[other_]) && s.reason(lits_[other_]) == this;
    }
    auto& self = const_cast<LoopFormula&>(*this);
    return std::ranges::any_of(self.xSpan(), [&](Literal lit) { return s.isTrue(lit) && s.reason(lit) == this; });
}
uint32_t LoopFormula::isOpen(const Solver& s, const TypeSet& xs, LitVec& freeLits) {
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
