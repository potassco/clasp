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

#include <clasp/constraint.h>

#include <potassco/error.h>
namespace Clasp {
/////////////////////////////////////////////////////////////////////////////////////////
// Constraint
/////////////////////////////////////////////////////////////////////////////////////////
Constraint::Constraint()  = default;
Constraint::~Constraint() = default;
void        Constraint::destroy(Solver*, bool) { delete this; }
auto        Constraint::type() const -> ConstraintType { return ConstraintType::static_; }
bool        Constraint::simplify(Solver&, bool) { return false; }
void        Constraint::undoLevel(Solver&) {}
uint32_t    Constraint::estimateComplexity(const Solver&) const { return 1; }
bool        Constraint::valid(Solver&) { return true; }
ClauseHead* Constraint::clause() { return nullptr; }
void        Constraint::decreaseActivity() {}
void        Constraint::resetActivity() {}
auto        Constraint::activity() const -> ConstraintScore { return ConstraintScore{}; }
bool        Constraint::locked(const Solver&) const { return true; }
uint32_t    Constraint::isOpen(const Solver&, const TypeSet&, LitVec&) { return 0; }
/////////////////////////////////////////////////////////////////////////////////////////
// PostPropagator
/////////////////////////////////////////////////////////////////////////////////////////
PostPropagator::PostPropagator() : next(nullptr) {}
PostPropagator::~PostPropagator() = default;
bool PostPropagator::init(Solver&) { return true; }
void PostPropagator::reset() {}
bool PostPropagator::isModel(Solver& s) { return valid(s); }
void PostPropagator::reason(Solver&, Literal, LitVec&) {}
auto PostPropagator::propagate(Solver&, Literal, uint32_t&) -> PropResult { return PropResult(true, false); }
void PostPropagator::cancelPropagation() { // NOLINT(readability-make-member-function-const)
    for (PostPropagator* n = this->next; n; n = n->next) { n->reset(); }
}
MessageHandler::MessageHandler() = default;
/////////////////////////////////////////////////////////////////////////////////////////
// PropagatorList
/////////////////////////////////////////////////////////////////////////////////////////
PropagatorList::PropagatorList() : head_(nullptr) {}
PropagatorList::~PropagatorList() { clear(); }
void PropagatorList::clear() {
    for (auto* r = head_; r;) {
        auto* t = r;
        r       = r->next;
        t->destroy();
    }
    head_ = nullptr;
}
void PropagatorList::add(PostPropagator* p) {
    POTASSCO_CHECK_PRE(p && p->next == nullptr, "Invalid post propagator");
    uint32_t prio = p->priority();
    for (PostPropagator **r = head(), *x;; r = &x->next) {
        if (x = *r; x == nullptr || prio < x->priority()) {
            p->next = x;
            *r      = p;
            break;
        }
    }
}
void PropagatorList::remove(PostPropagator* p) {
    POTASSCO_CHECK_PRE(p, "Invalid post propagator");
    for (PostPropagator **r = head(), *x; *r; r = &x->next) {
        if (x = *r; x == p) {
            *r      = x->next;
            p->next = nullptr;
            break;
        }
    }
}

bool PropagatorList::init(Solver& s) {
    for (PostPropagator **r = head(), *pp = nullptr; (pp = *r) != nullptr; r = pp == *r ? &pp->next : r) {
        if (not pp->init(s)) {
            return false;
        }
    }
    return true;
}

bool PropagatorList::simplify(Solver& s, bool reinit) {
    for (PostPropagator **r = head(), *pp = nullptr; (pp = *r) != nullptr; r = pp == *r ? &pp->next : r) {
        if (pp->simplify(s, reinit)) {
            *r = pp->next;
            pp->destroy(&s, false);
        }
    }
    return false;
}

bool PropagatorList::isModel(Solver& s) {
    for (PostPropagator **r = head(), *pp = nullptr; (pp = *r) != nullptr; r = pp == *r ? &pp->next : r) {
        if (not pp->isModel(s)) {
            return false;
        }
    }
    return true;
}

} // namespace Clasp
