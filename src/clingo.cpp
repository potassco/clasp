//
// Copyright (c) 2015-2017 Benjamin Kaufmann
//
// This file is part of Clasp. See http://www.cs.uni-potsdam.de/clasp/
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
#include <clasp/clingo.h>
#include <clasp/solver.h>
#include <clasp/clause.h>
#include <algorithm>
#include POTASSCO_EXT_INCLUDE(unordered_map)
namespace Clasp { namespace {
	template <class O, class L, void (L::*enter)(), void (L::*exit)(), class OP>
	struct Scoped {
		Scoped(L* lock, O* obj, const OP& op = OP()) : lock_(lock), obj_(obj), op_(op) { if (lock) (lock->*enter)(); }
		~Scoped() { if (lock_) (lock_->*exit)(); }
		O* operator->() const { op_(); return obj_; }
		L* lock_;
		O* obj_;
		OP op_;
	};
	struct Nop { void operator()() const {} };
	struct Inc { Inc(LitVec::size_type& e) : epoch_(&e) {} void operator()() const { ++*epoch_; } LitVec::size_type* epoch_; };
	typedef Scoped<Potassco::AbstractPropagator, ClingoPropagatorLock, &ClingoPropagatorLock::lock, &ClingoPropagatorLock::unlock, Inc> ScopedLock;
	typedef Scoped<ClingoPropagator, ClingoPropagatorLock, &ClingoPropagatorLock::unlock, &ClingoPropagatorLock::lock, Nop> ScopedUnlock;
}
ClingoPropagatorLock::~ClingoPropagatorLock() {}
/////////////////////////////////////////////////////////////////////////////////////////
// ClingoPropagator::Control
/////////////////////////////////////////////////////////////////////////////////////////
class ClingoPropagator::Control : public Potassco::AbstractSolver, Potassco::AbstractAssignment {
public:
	Control(ClingoPropagator& ctx, Solver& s, uint32 st = 0u) : ctx_(&ctx), s_(&s), state_(st | state_ctrl) {}
	const AbstractAssignment& assignment() const { return *this; }
	// AbstractAssignment
	virtual uint32_t size()            const { return s_->numVars(); }
	virtual uint32_t unassigned()      const { return s_->numFreeVars(); }
	virtual bool     isTotal()         const { return s_->numFreeVars() == 0u; }
	virtual bool     hasConflict()     const { return s_->hasConflict(); }
	virtual uint32_t level()           const { return s_->decisionLevel(); }
	virtual bool     hasLit(Lit_t lit) const { return s_->validVar(decodeVar(lit)); }
	virtual Value_t  value(Lit_t lit)  const {
		POTASSCO_REQUIRE(Control::hasLit(lit), "Invalid literal");
		switch (s_->value(decodeVar(lit))) {
			default: return Value_t::Free;
			case value_true:  return lit >= 0 ? Value_t::True  : Value_t::False;
			case value_false: return lit >= 0 ? Value_t::False : Value_t::True;
		}
	}
	virtual uint32_t level(Lit_t lit)  const { return Control::value(lit) != Potassco::Value_t::Free ? s_->level(decodeVar(lit)) : UINT32_MAX; }
	virtual Lit_t    decision(uint32_t dl) const {
		POTASSCO_REQUIRE(dl <= s_->decisionLevel(), "Invalid decision level");
		return encodeLit(dl ? s_->decision(dl) : lit_true());
	}

	// Potassco::AbstractSolver
	virtual Potassco::Id_t id() const { return s_->id(); }
	virtual bool addClause(const Potassco::LitSpan& clause, Potassco::Clause_t prop);
	virtual bool propagate();
	virtual Lit  addVariable();
	virtual bool hasWatch(Lit lit) const;
	virtual void addWatch(Lit lit);
	virtual void removeWatch(Lit lit);
private:
	typedef ClingoPropagator::State State;
	ClingoPropagatorLock* lock() const { return (state_ & state_init) == 0 ? ctx_->call_->lock() : 0; }
	ClingoPropagator* ctx_;
	Solver*           s_;
	uint32            state_;
};
bool ClingoPropagator::Control::addClause(const Potassco::LitSpan& clause, Potassco::Clause_t prop) {
	POTASSCO_REQUIRE(!s_->hasConflict(), "Invalid addClause() on conflicting assignment");
	ScopedUnlock pp(lock(), ctx_);
	pp->toClause(*s_, clause, prop);
	return pp->addClause(*s_, state_);
}
bool ClingoPropagator::Control::propagate() {
	ScopedUnlock unlocked(lock(), ctx_);
	if (s_->hasConflict())    { return false; }
	if (s_->queueSize() == 0) { return true;  }
	ClingoPropagator::size_t epoch = ctx_->epoch_;
	return (state_ & state_prop) != 0u && s_->propagateUntil(unlocked.obj_) && epoch == ctx_->epoch_;
}
Potassco::Lit_t ClingoPropagator::Control::addVariable() {
	POTASSCO_REQUIRE(!s_->hasConflict(), "Invalid addVariable() on conflicting assignment");
	ScopedUnlock unlocked(lock(), ctx_);
	return encodeLit(posLit(s_->pushAuxVar()));
}
bool ClingoPropagator::Control::hasWatch(Lit_t lit) const {
	ScopedUnlock unlocked(lock(), ctx_);
	return Control::hasLit(lit) && s_->hasWatch(decodeLit(lit), ctx_);
}
void ClingoPropagator::Control::addWatch(Lit_t lit) {
	ScopedUnlock unlocked(lock(), ctx_);
	POTASSCO_REQUIRE(Control::hasLit(lit), "Invalid literal");
	Literal p = decodeLit(lit);
	if (!s_->hasWatch(p, ctx_)) {
		s_->addWatch(p, ctx_);
		if ((state_ & state_init) != 0u && s_->isTrue(p)) {
			// are we too late?
			bool inQ = std::find(s_->trail().begin() + s_->assignment().front, s_->trail().end(), p) != s_->trail().end();
			if (!inQ && !ctx_->inTrail(p)) {
				uint32 ignore = 0;
				ctx_->propagate(*s_, p, ignore);
			}
		}
	}
}
void ClingoPropagator::Control::removeWatch(Lit_t lit) {
	ScopedUnlock unlocked(lock(), ctx_);
	if (Control::hasLit(lit)) {
		s_->removeWatch(decodeLit(lit), ctx_);
	}
}
/////////////////////////////////////////////////////////////////////////////////////////
// ClingoPropagator
/////////////////////////////////////////////////////////////////////////////////////////
// flags for clauses from propagator
static const uint32 ccFlags_s[2] = {
	/* 0: learnt */ ClauseCreator::clause_not_sat | Clasp::ClauseCreator::clause_int_lbd,
	/* 1: static */ ClauseCreator::clause_no_add  | ClauseCreator::clause_explicit
};
ClingoPropagator::ClingoPropagator(Propagator* p)
	: call_(p)
	, prop_(0), epoch_(0), level_(0), init_(0) {
}
uint32 ClingoPropagator::priority() const { return static_cast<uint32>(priority_class_general); }

void ClingoPropagator::destroy(Solver* s, bool detach) {
	if (s && detach) {
		for (Var v = 1; v <= s->numVars(); ++v) {
			s->removeWatch(posLit(v), this);
			s->removeWatch(negLit(v), this);
		}
	}
	destroyDB(db_, s, detach);
	PostPropagator::destroy(s, detach);
}

bool ClingoPropagator::init(Solver& s) {
	POTASSCO_REQUIRE(s.decisionLevel() == 0 && prop_ == trail_.size(), "Invalid init");
	Control ctrl(*this, s, state_init);
	init_  = call_->init(init_, ctrl);
	front_ = call_->checkMode() == ClingoPropagatorCheck_t::Fixpoint ? -1 : INT32_MAX;
	return true;
}

bool ClingoPropagator::inTrail(Literal p) const {
	return std::find(trail_.begin(), trail_.end(), encodeLit(p)) != trail_.end();
}

void ClingoPropagator::registerUndo(Solver& s) {
	uint32 dl = s.decisionLevel();
	if (dl != level_) {
		POTASSCO_REQUIRE(dl > level_, "Stack property violated");
		POTASSCO_REQUIRE(front_ == INT32_MAX || (dl - level_) == 1, "Propagate must be called on each level");
		// first time we see this level
		s.addUndoWatch(level_ = dl, this);
		undo_.push_back(static_cast<uint32>(trail_.size()));
	}
}
Constraint::PropResult ClingoPropagator::propagate(Solver& s, Literal p, uint32&) {
	registerUndo(s);
	trail_.push_back(encodeLit(p));
	return PropResult(true, true);
}
void ClingoPropagator::undoLevel(Solver& s) {
	POTASSCO_REQUIRE(s.decisionLevel() == level_, "Invalid undo");
	uint32 beg = undo_.back();
	undo_.pop_back();
	if (prop_ > beg) {
		Potassco::LitSpan change = Potassco::toSpan(&trail_[0] + beg, prop_ - beg);
		ScopedLock(call_->lock(), call_->propagator(), Inc(epoch_))->undo(Control(*this, s), change);
		prop_ = beg;
	}
	trail_.resize(beg);
	if (front_ != INT32_MAX) {
		front_ = -1;
		--level_;
	}
	else {
		level_ = !trail_.empty() ? s.level(decodeLit(trail_.back()).var()) : 0;
	}
}
bool ClingoPropagator::propagateFixpoint(Clasp::Solver& s, Clasp::PostPropagator*) {
	POTASSCO_REQUIRE(prop_ <= trail_.size(), "Invalid propagate");
	for (Control ctrl(*this, s, state_prop); prop_ != trail_.size() || front_ < (int32)s.numAssignedVars();) {
		if (prop_ != trail_.size()) {
			// create copy because trail might change during call to user propagation
			temp_.assign(trail_.begin() + prop_, trail_.end());
			prop_ = static_cast<uint32>(trail_.size());
			ScopedLock(call_->lock(), call_->propagator(), Inc(epoch_))->propagate(ctrl, Potassco::toSpan(temp_));
		}
		else {
			registerUndo(s);
			front_ = (int32)s.numAssignedVars();
			ScopedLock(call_->lock(), call_->propagator(), Inc(epoch_))->check(ctrl);
		}
		if (!addClause(s, state_prop) || (s.queueSize() && !s.propagateUntil(this))) {
			return false;
		}
	}
	return true;
}

void ClingoPropagator::toClause(Solver& s, const Potassco::LitSpan& clause, Potassco::Clause_t prop) {
	POTASSCO_REQUIRE(todo_.empty(), "Assignment not propagated");
	Literal max;
	LitVec& mem = todo_.mem;
	for (const Potassco::Lit_t* it = Potassco::begin(clause); it != Potassco::end(clause); ++it) {
		Literal p = decodeLit(*it);
		if (max < p) { max = p; }
		mem.push_back(p);
	}
	if (aux_ < max) { aux_ = max; }
	if ((Potassco::Clause_t::isVolatile(prop) || s.auxVar(max.var())) && !isSentinel(s.sharedContext()->stepLiteral())) {
		mem.push_back(~s.sharedContext()->stepLiteral());
	}
	todo_.clause = ClauseCreator::prepare(s, mem, Clasp::ClauseCreator::clause_force_simplify, Constraint_t::Other);
	todo_.flags  = ccFlags_s[int(Potassco::Clause_t::isStatic(prop))];
	if (mem.empty()) {
		mem.push_back(lit_false());
	}
}
bool ClingoPropagator::addClause(Solver& s, uint32 st) {
	if (s.hasConflict()) { todo_.clear(); return false; }
	if (todo_.empty())   { return true; }
	const ClauseRep& clause = todo_.clause;
	Literal w0 = clause.size > 0 ? clause.lits[0] : lit_false();
	Literal w1 = clause.size > 1 ? clause.lits[1] : lit_false();
	uint32  cs = (ClauseCreator::status(s, clause) & (ClauseCreator::status_unit|ClauseCreator::status_unsat));
	if (cs && s.level(w1.var()) < s.decisionLevel() && s.isUndoLevel()) {
		if ((st & state_ctrl) != 0u) { return false; }
		if ((st & state_prop) != 0u) { ClingoPropagator::reset(); cancelPropagation(); }
		s.undoUntil(s.level(w1.var()));
	}
	bool local = (todo_.flags & ClauseCreator::clause_no_add) != 0;
	if (!s.isFalse(w0) || local || s.force(w0, this)) {
		ClauseCreator::Result res = ClauseCreator::create(s, clause, todo_.flags);
		if (res.local && local) { db_.push_back(res.local); }
	}
	todo_.clear();
	return !s.hasConflict();
}

void ClingoPropagator::reason(Solver&, Literal p, LitVec& r) {
	if (!todo_.empty() && todo_.mem[0] == p) {
		for (LitVec::const_iterator it = todo_.mem.begin() + 1, end = todo_.mem.end(); it != end; ++it) {
			r.push_back(~*it);
		}
	}
}

bool ClingoPropagator::simplify(Solver& s, bool) {
	if (!s.validVar(aux_.var())) {
		ClauseDB::size_type i, j, end = db_.size();
		LitVec cc;
		Var last = s.numVars();
		aux_ = lit_true();
		for (i = j = 0; i != end; ++i) {
			db_[j++] = db_[i];
			ClauseHead* c = db_[i]->clause();
			if (c && c->aux()) {
				cc.clear();
				c->toLits(cc);
				Literal x = *std::max_element(cc.begin(), cc.end());
				if (x.var() > last) {
					c->destroy(&s, true);
					--j;
				}
				else if (aux_ < x) { aux_ = x; }
			}
		}
		db_.erase(db_.begin()+j, db_.end());
	}
	simplifyDB(s, db_, false);
	return false;
}

bool ClingoPropagator::isModel(Solver& s) {
	POTASSCO_REQUIRE(prop_ == trail_.size(), "Assignment not propagated");
	if (call_->checkMode() == ClingoPropagatorCheck_t::Total) {
		Control ctrl(*this, s);
		ScopedLock(call_->lock(), call_->propagator(), Inc(epoch_))->check(ctrl);
		return addClause(s, 0u) && s.numFreeVars() == 0 && s.queueSize() == 0;
	}
	return true;
}
/////////////////////////////////////////////////////////////////////////////////////////
// ClingoPropagatorInit
/////////////////////////////////////////////////////////////////////////////////////////
ClingoPropagatorInit::Change::Change(Lit_t p, Action a)
	: lit(p), sId(-1), action(static_cast<int16>(a)) {}
ClingoPropagatorInit::Change::Change(Lit_t p, Action a, uint32 sId)
	: lit(p), sId(static_cast<int16>(sId)), action(static_cast<int16>(a)) {}
bool ClingoPropagatorInit::Change::operator<(const Change& rhs) const {
	int cmp = std::abs(lit) - std::abs(rhs.lit);
	return cmp != 0 ? cmp < 0 : lit < rhs.lit;
}
void ClingoPropagatorInit::Change::apply(Potassco::AbstractSolver& s) const {
	switch (action) {
		case AddWatch:    s.addWatch(lit);    break;
		case RemoveWatch: s.removeWatch(lit); break;
		default: break;
	}
}

struct ClingoPropagatorInit::History : POTASSCO_EXT_NS::unordered_map<Potassco::Lit_t, uint64>{
	void add(const Change& change) {
		const uint64 mask = change.sId < 0 ? UINT64_MAX : bit_mask<uint64>(static_cast<uint32>(change.sId));
		if (change.action == AddWatch) {
			std::pair<iterator, bool> x = insert(value_type(change.lit, 0));
			x.first->second |= mask;
		}
		else if (change.action == RemoveWatch) {
			iterator it = find(change.lit);
			if (it != end() && (it->second &= ~mask) == 0) {
				erase(it);
			}
		}
	}
};

ClingoPropagatorInit::ClingoPropagatorInit(Potassco::AbstractPropagator& cb, ClingoPropagatorLock* lock, CheckType m)
	: prop_(&cb), lock_(lock), history_(0), step_(1), check_(m) {
}
ClingoPropagatorInit::~ClingoPropagatorInit()       { delete history_; }
void ClingoPropagatorInit::prepare(SharedContext&)  {}
bool ClingoPropagatorInit::addPost(Solver& s)       { return s.addPost(new ClingoPropagator(this)); }
void ClingoPropagatorInit::unfreeze(SharedContext&) {
	if (history_) {
		for (ChangeList::const_iterator it = changes_.begin(), end = changes_.end(); it != end; ++it) {
			history_->add(*it);
		}
	}
	ChangeList().swap(changes_);
	++step_;
}

Potassco::Lit_t ClingoPropagatorInit::addWatch(Literal lit) {
	changes_.push_back(Change(encodeLit(lit), AddWatch));
	return changes_.back().lit;
}

Potassco::Lit_t ClingoPropagatorInit::addWatch(uint32 sId, Literal lit) {
	POTASSCO_REQUIRE(sId < 64, "Invalid solver id");
	changes_.push_back(Change(encodeLit(lit), AddWatch, sId));
	return changes_.back().lit;
}

void ClingoPropagatorInit::removeWatch(Literal lit) {
	changes_.push_back(Change(encodeLit(lit), RemoveWatch));
}

void ClingoPropagatorInit::removeWatch(uint32 sId, Literal lit) {
	POTASSCO_REQUIRE(sId < 64, "Invalid solver id");
	changes_.push_back(Change(encodeLit(lit), RemoveWatch, sId));
}

uint32 ClingoPropagatorInit::init(uint32 lastStep, Potassco::AbstractSolver& s) {
	POTASSCO_REQUIRE(s.id() < 64, "Invalid solver id");
	int16 sId = static_cast<int16>(s.id());
	if (history_ && (step_ - lastStep) > 1) {
		for (History::const_iterator it = history_->begin(), end = history_->end(); it != end; ++it) {
			if (test_bit(it->second, sId)) { Change(it->first, AddWatch, sId).apply(s); }
		}
	}
	ChangeList changesForSolver;
	for (ChangeList::const_iterator it = changes_.begin(), end = changes_.end(); it != end; ++it) {
		if (it->sId < 0 || it->sId == sId) { changesForSolver.push_back(*it); }
	}
	std::stable_sort(changesForSolver.begin(), changesForSolver.end());
	for (ChangeList::const_iterator it = changesForSolver.begin(), end = changesForSolver.end(); it != end; ++it) {
		Lit_t lit = it->lit;
		// skip all but the last change for a given literal
		while ((it + 1) != end && (it + 1)->lit == lit) { ++it; }
		it->apply(s);
	}
	return step_;
}

void ClingoPropagatorInit::enableClingoPropagatorCheck(CheckType checkMode) {
	check_ = checkMode;
}

void ClingoPropagatorInit::enableHistory(bool b) {
	if (!b)             { delete history_; history_ = 0; }
	else if (!history_) { history_ = new History(); }
}

}
