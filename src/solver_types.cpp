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
#include <clasp/solver_types.h>

#include <clasp/solver.h>
#include <clasp/statistics.h>

#include <potassco/error.h>

#include <new>
#if defined(__GNUC__) && __GNUC__ >= 8
#pragma GCC diagnostic ignored "-Wclass-memaccess"
#endif
namespace Clasp {
/////////////////////////////////////////////////////////////////////////////////////////
// Statistics
/////////////////////////////////////////////////////////////////////////////////////////
// clang-format off
#define NO_ARG
#define CLASP_STAT_ACCU(m, k, a, accu) accu;
#define CLASP_STAT_KEY(m, k, a, accu)  k,
#define CLASP_STAT_GET(m, k, a, accu)  if (key == (k)) return a;
// clang-format on
// NOLINTBEGIN(*-macro-parentheses)
#define CLASP_DEFINE_ISTATS(T, STATS, name)                                                                            \
    static constexpr std::string_view const T##_s[] = {STATS(CLASP_STAT_KEY, NO_ARG, NO_ARG)};                         \
    auto                                    T::size() -> uint32_t { return size32(T##_s); }                            \
    auto                                    T::key(uint32_t i) -> std::string_view {                                   \
        POTASSCO_CHECK(i < size(), ERANGE, "%s: key %u is out of bounds", #T, i);   \
        return T##_s[i];                                                            \
    }                                                                                                                  \
    void T::accu(const T& o) { STATS(CLASP_STAT_ACCU, (*this), o); }                                                   \
    auto T::at(std::string_view key) const -> StatisticObject {                                                        \
        STATS(CLASP_STAT_GET, NO_ARG, NO_ARG);                                                                         \
        POTASSCO_FAIL(ERANGE, "%s: unknown key '%" PRIsv "'", #T, PRI_SV(key));                                        \
    }
// NOLINTEND(*-macro-parentheses)
/////////////////////////////////////////////////////////////////////////////////////////
// CoreStats/JumpStats/ExtendedStats
/////////////////////////////////////////////////////////////////////////////////////////
#define VALUE(X)      StatisticObject::value(&X)          // NOLINT(*-macro-parentheses)
#define SUM(X)        StatisticObject::value<sum_fun>(&X) // NOLINT(*-macro-parentheses)
#define MAP(X)        StatisticObject::map(&X)            // NOLINT(*-macro-parentheses)
#define MAX_MEM(X, Y) X = std::max((X), (Y))
namespace {
constexpr auto sum_fun(const ExtendedStats::Array* arr) -> double {
    return static_cast<double>(ExtendedStats::sum(*arr));
}
} // namespace
CLASP_DEFINE_ISTATS(CoreStats, CLASP_CORE_STATS, "core")
CLASP_DEFINE_ISTATS(JumpStats, CLASP_JUMP_STATS, "jumps")
CLASP_DEFINE_ISTATS(ExtendedStats, CLASP_EXTENDED_STATS, "extra")
#undef NO_ARG
#undef VALUE
#undef SUM
#undef MAP
#undef MAX_MEM
#undef CLASP_STAT_ACCU
#undef CLASP_STAT_KEY
#undef CLASP_STAT_GET
#undef CLASP_DEFINE_ISTATS
/////////////////////////////////////////////////////////////////////////////////////////
// SolverStats
/////////////////////////////////////////////////////////////////////////////////////////
SolverStats::SolverStats(const SolverStats& o) : CoreStats(o) {
    if (o.extra && enableExtended()) {
        extra->accu(*o.extra);
    }
}
SolverStats::~SolverStats() { delete extra; }
bool SolverStats::enableExtended() {
    return extra != nullptr || (extra = new (std::nothrow) ExtendedStats()) != nullptr;
}
void SolverStats::reset() {
    static_cast<CoreStats&>(*this) = {};
    if (extra) {
        *extra = {};
    }
}
void SolverStats::accu(const SolverStats& o) {
    CoreStats::accu(o);
    if (extra && o.extra) {
        extra->accu(*o.extra);
    }
}
void SolverStats::accu(const SolverStats& o, bool enableRhs) {
    if (enableRhs) {
        enable(o);
    }
    accu(o);
}
void SolverStats::flush() const { // NOLINT(*-no-recursion)
    if (multi) {
        multi->enable(*this);
        multi->accu(*this);
        multi->flush();
    }
}
void SolverStats::swapStats(SolverStats& o) {
    std::swap(static_cast<CoreStats&>(*this), static_cast<CoreStats&>(o));
    std::swap(extra, o.extra);
}
auto SolverStats::size() const -> uint32_t { return CoreStats::size() + (extra != nullptr); }
auto SolverStats::key(uint32_t i) const -> std::string_view {
    POTASSCO_CHECK(i < size(), ERANGE);
    return i < CoreStats::size() ? CoreStats::key(i) : "extra";
}
auto SolverStats::at(std::string_view key) const -> StatisticObject {
    if (extra && key == "extra") {
        return StatisticObject::map(extra);
    }
    return CoreStats::at(key);
}
/////////////////////////////////////////////////////////////////////////////////////////
// ClauseHead
/////////////////////////////////////////////////////////////////////////////////////////
ClauseHead::ClauseHead(const InfoType& init) : info_(init) {
    static_assert(sizeof(ClauseHead) <= 32, "Unsupported Alignment");
    head_[2] = lit_false;
}
void ClauseHead::resetScore(ScoreType sc) { info_.setScore(sc); }
void ClauseHead::attach(Solver& s) {
    assert(head_[0] != head_[1] && head_[1] != head_[2]);
    s.addWatch(~head_[0], ClauseWatch(this));
    s.addWatch(~head_[1], ClauseWatch(this));
}

void ClauseHead::detach(Solver& s) {
    s.removeWatch(~head_[0], this);
    s.removeWatch(~head_[1], this);
}

bool ClauseHead::locked(const Solver& s) const {
    return (s.isTrue(head_[0]) && s.reason(head_[0]) == this) || (s.isTrue(head_[1]) && s.reason(head_[1]) == this);
}

bool ClauseHead::satisfied(const Solver& s) const {
    return s.isTrue(head_[0]) || s.isTrue(head_[1]) || s.isTrue(head_[2]);
}

bool ClauseHead::toImplication(Solver& s) {
    uint32_t  sz       = isSentinel(head_[1]) ? 1 : 2 + (not s.isFalse(head_[2]) || s.level(head_[2].var()) > 0);
    ClauseRep rep      = ClauseRep::create({head_, sz}, InfoType(ClauseHead::type()).setLbd(2).setTagged(tagged()));
    bool      implicit = s.allowImplicit(rep);
    bool      locked   = ClauseHead::locked(s) && s.decisionLevel() > 0;
    if ((locked || not implicit) && sz > 1) {
        return false;
    }
    rep.prep = 1;
    s.add(rep, false);
    detach(s);
    return true;
}
/////////////////////////////////////////////////////////////////////////////////////////
// SmallClauseAlloc
/////////////////////////////////////////////////////////////////////////////////////////
SmallClauseAlloc::SmallClauseAlloc() : blocks_(nullptr), freeList_(nullptr) {}
SmallClauseAlloc::~SmallClauseAlloc() {
    Block* r = blocks_;
    while (r) {
        Block* t = r;
        r        = r->next;
        ::operator delete(t);
    }
}

void SmallClauseAlloc::allocBlock() {
    auto* r = static_cast<Block*>(::operator new(sizeof(Block)));
    for (auto i : irange(Block::num_chunks - 1)) { r->chunk[i].next = &r->chunk[i + 1]; }
    r->chunk[Block::num_chunks - 1].next = freeList_;
    freeList_                            = r->chunk;
    r->next                              = blocks_;
    blocks_                              = r;
}

} // namespace Clasp
