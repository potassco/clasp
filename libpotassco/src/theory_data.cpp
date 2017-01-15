//
// Copyright (c) 2015, Benjamin Kaufmann
//
// This file is part of Potassco.
//
// Clasp is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2 of the License, or
// (at your option) any later version.
//
// Clasp is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with Clasp; if not, write to the Free Software
// Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
//
#include <potassco/theory_data.h>
#include <memory>
#include <stdexcept>
#include <algorithm>
#include <cstring>
namespace Potassco {
template <class T>
static std::size_t nBytes(const IdSpan& ids) {
	return sizeof(T) + (ids.size * sizeof(Id_t));
}
struct FuncData {
	static FuncData* newFunc(int32_t base, const IdSpan& args);
	static void destroy(FuncData*);
	int32_t  base;
	uint32_t size;
POTASSCO_WARNING_BEGIN_RELAXED
	Id_t     args[0];
POTASSCO_WARNING_END_RELAXED
};
FuncData* FuncData::newFunc(int32_t base, const IdSpan& args) {
	std::size_t nb = nBytes<FuncData>(args);
	FuncData* f = new (::operator new(nb)) FuncData;
	f->base = base;
	f->size = static_cast<uint32_t>(Potassco::size(args));
	std::memcpy(f->args, begin(args), f->size * sizeof(Id_t));
	return f;
}
void FuncData::destroy(FuncData* f) {
	if (f) { f->~FuncData(); ::operator delete(f); }
}
const uint64_t nulTerm  = static_cast<uint64_t>(-1);
const uint64_t typeMask = static_cast<uint64_t>(3);

TheoryTerm::TheoryTerm() : data_(nulTerm) {}
TheoryTerm::TheoryTerm(int num) {
	data_ = (static_cast<uint64_t>(num) << 2) | Theory_t::Number;
}
TheoryTerm::TheoryTerm(const char* sym) {
	data_ = (assertPtr(sym) | Theory_t::Symbol);
	assert(sym == symbol());
}
TheoryTerm::TheoryTerm(const FuncData* c) {
	data_ = (assertPtr(c) | Theory_t::Compound);
}
uint64_t TheoryTerm::assertPtr(const void* p) const {
	uint64_t data = static_cast<uint64_t>(reinterpret_cast<uintptr_t>(p));
	POTASSCO_REQUIRE((data & 3u) == 0u, "Invalid pointer alignment");
	return data;
}
void TheoryTerm::assertType(Theory_t t) const {
	POTASSCO_REQUIRE(type() == t, "Invalid term cast");
}
bool TheoryTerm::valid() const { return data_ != nulTerm; }
Theory_t TheoryTerm::type() const { POTASSCO_REQUIRE(valid(), "Invalid term"); return static_cast<Theory_t>(data_&typeMask); }
int TheoryTerm::number() const {
	assertType(Theory_t::Number);
	return static_cast<int>(data_ >> 2);
}
uintptr_t TheoryTerm::getPtr() const {
	return static_cast<uintptr_t>(data_ & ~typeMask);
}
const char* TheoryTerm::symbol() const {
	assertType(Theory_t::Symbol);
	return reinterpret_cast<const char*>(getPtr());
}
FuncData* TheoryTerm::func() const {
	return reinterpret_cast<FuncData*>(getPtr());
}
int TheoryTerm::compound() const {
	assertType(Theory_t::Compound);
	return func()->base;
}
bool TheoryTerm::isFunction() const { return type() == Theory_t::Compound && func()->base >= 0; }
bool TheoryTerm::isTuple()    const { return type() == Theory_t::Compound && func()->base < 0; }
Id_t TheoryTerm::function()   const { POTASSCO_REQUIRE(isFunction(), "Term is not a function"); return static_cast<Id_t>(func()->base); }
Tuple_t TheoryTerm::tuple()   const { POTASSCO_REQUIRE(isTuple(), "Term is not a tuple"); return static_cast<Tuple_t>(func()->base); }
uint32_t TheoryTerm::size()   const { return type() == Theory_t::Compound ? func()->size : 0; }
TheoryTerm::iterator TheoryTerm::begin() const { return type() == Theory_t::Compound ? func()->args : 0; }
TheoryTerm::iterator TheoryTerm::end()   const { return type() == Theory_t::Compound ? func()->args + func()->size : 0; }

TheoryElement::TheoryElement(const IdSpan& terms, Id_t c) : nTerms_(static_cast<uint32_t>(Potassco::size(terms))), nCond_(c != 0) {
	std::memcpy(term_, Potassco::begin(terms), nTerms_ * sizeof(Id_t));
	if (nCond_ != 0) { term_[nTerms_] = c; }
}
TheoryElement* TheoryElement::newElement(const IdSpan& terms, Id_t c) {
	std::size_t nb = nBytes<TheoryElement>(terms);
	if (c != 0) { nb += sizeof(Id_t); }
	return new (::operator new(nb)) TheoryElement(terms, c);
}
void TheoryElement::destroy(TheoryElement* e) {
	if (e) {
		e->~TheoryElement();
		::operator delete(e);
	}
}
Id_t TheoryElement::condition() const {
	return nCond_ == 0 ? 0 : term_[nTerms_];
}
void TheoryElement::setCondition(Id_t c) {
	term_[nTerms_] = c;
}

TheoryAtom::TheoryAtom(Id_t a, Id_t term, const IdSpan& args, Id_t* op, Id_t* rhs)
	: atom_(a)
	, guard_(op != 0)
	, termId_(term)
	, nTerms_(static_cast<uint32_t>(Potassco::size(args))) {
	std::memcpy(term_, Potassco::begin(args), nTerms_ * sizeof(Id_t));
	if (op) {
		term_[nTerms_] = *op;
		term_[nTerms_ + 1] = *rhs;
	}
}

TheoryAtom* TheoryAtom::newAtom(Id_t a, Id_t term, const IdSpan& args) {
	return new (::operator new(nBytes<TheoryAtom>(args))) TheoryAtom(a, term, args, 0, 0);
}
TheoryAtom* TheoryAtom::newAtom(Id_t a, Id_t term, const IdSpan& args, Id_t op, Id_t rhs) {
	std::size_t nb = nBytes<TheoryAtom>(args) + (2*sizeof(Id_t));
	return new (::operator new(nb)) TheoryAtom(a, term, args, &op, &rhs);
}
void TheoryAtom::destroy(TheoryAtom* a) {
	if (a) {
		a->~TheoryAtom();
		::operator delete(a);
	}
}
const Id_t* TheoryAtom::guard() const {
	return guard_ != 0 ? &term_[nTerms_] : 0;
}
const Id_t* TheoryAtom::rhs() const {
	return guard_ != 0 ? &term_[nTerms_ + 1] : 0;
}
//////////////////////////////////////////////////////////////////////////////////////////////////////
// TheoryData
//////////////////////////////////////////////////////////////////////////////////////////////////////
struct TheoryData::DestroyT {
	template <class T> void operator()(T* x) const { return T::destroy(x); }
	void operator()(TheoryTerm& t) const {
		if (t.valid()) {
			if (t.type() == Theory_t::Compound) {
				this->operator()(t.func());
			}
			else if (t.type() == Theory_t::Symbol) {
				delete[] const_cast<char*>(t.symbol());
			}
		}
	}
};
TheoryData::TheoryData()  {}
TheoryData::~TheoryData() {
	reset();
}
const TheoryTerm& TheoryData::addTerm(Id_t termId, int number) {
	return setTerm(termId) = TheoryTerm(number);
}
const TheoryTerm& TheoryData::addTerm(Id_t termId, const StringSpan& name) {
	TheoryTerm& t = setTerm(termId);
	char* buf = new char[name.size + 1];
	*std::copy(Potassco::begin(name), Potassco::end(name), buf) = 0;
	return (t = TheoryTerm(buf));
}
const TheoryTerm& TheoryData::addTerm(Id_t termId, const char* name) {
	return addTerm(termId, Potassco::toSpan(name, name ? std::strlen(name) : 0));
}
const TheoryTerm& TheoryData::addTerm(Id_t termId, Id_t funcId, const IdSpan& args) {
	return setTerm(termId) = TheoryTerm(FuncData::newFunc(static_cast<int32_t>(funcId), args));
}
const TheoryTerm& TheoryData::addTerm(Id_t termId, Tuple_t type, const IdSpan& args) {
	return setTerm(termId) = TheoryTerm(FuncData::newFunc(static_cast<int32_t>(type), args));
}
void TheoryData::removeTerm(Id_t termId) {
	if (hasTerm(termId)) {
		DestroyT()(terms()[termId]);
		terms()[termId] = Term();
	}
}
const TheoryElement& TheoryData::addElement(Id_t id, const IdSpan& terms, Id_t cId) {
	if (!hasElement(id)) {
		while (numElems() <= id) { elems_.push(static_cast<TheoryElement*>(0)); }
	}
	else {
		POTASSCO_REQUIRE(!isNewElement(id), "Redefinition of theory element '%u'", id);
		DestroyT()(elems()[id]);
	}
	return *(elems()[id] = TheoryElement::newElement(terms, cId));
}

const TheoryAtom& TheoryData::addAtom(Id_t atomOrZero, Id_t termId, const IdSpan& elems) {
	atoms_.push(static_cast<TheoryAtom*>(0));
	return *(atoms()[numAtoms()-1] = TheoryAtom::newAtom(atomOrZero, termId, elems));
}
const TheoryAtom& TheoryData::addAtom(Id_t atomOrZero, Id_t termId, const IdSpan& elems, Id_t op, Id_t rhs) {
	atoms_.push(static_cast<TheoryAtom*>(0));
	return *(atoms()[numAtoms()-1] = TheoryAtom::newAtom(atomOrZero, termId, elems, op, rhs));
}

TheoryTerm& TheoryData::setTerm(Id_t id) {
	if (!hasTerm(id)) {
		while (numTerms() <= id) { terms_.push(TheoryTerm()); }
	}
	else {
		POTASSCO_REQUIRE(!isNewTerm(id), "Redefinition of theory term '%u'", id);
		removeTerm(id);
	}
	return terms()[id];
}
void TheoryData::setCondition(Id_t elementId, Id_t newCond) {
	POTASSCO_ASSERT(getElement(elementId).condition() == COND_DEFERRED);
	elems()[elementId]->setCondition(newCond);
}

void TheoryData::reset() {
	DestroyT destroy;
	std::for_each(terms(), terms() + numTerms(), destroy);
	std::for_each(elems(), elems() + numElems(), destroy);
	std::for_each(atoms(), atoms() + numAtoms(), destroy);
	PtrStack().swap(terms_);
	PtrStack().swap(elems_);
	TermStack().swap(atoms_);
	frame_ = Up();
}
void TheoryData::update() {
	frame_.atom = numAtoms();
	frame_.term = numTerms();
	frame_.elem = numElems();
}
TheoryTerm* TheoryData::terms() const {
	return static_cast<TheoryTerm*>(terms_.get(0));
}
TheoryElement** TheoryData::elems() const {
	return static_cast<TheoryElement**>(elems_.get(0));
}
TheoryAtom** TheoryData::atoms() const {
	return static_cast<TheoryAtom**>(atoms_.get(0));
}

uint32_t TheoryData::numAtoms() const {
	return atoms_.top() / sizeof(TheoryAtom*);
}
uint32_t TheoryData::numTerms() const {
	return terms_.top() / sizeof(TheoryTerm);
}
uint32_t TheoryData::numElems() const {
	return elems_.top() / sizeof(TheoryElement*);
}
TheoryData::atom_iterator TheoryData::begin() const {
	return atoms();
}
TheoryData::atom_iterator TheoryData::currBegin() const {
	return begin() + frame_.atom;
}
TheoryData::atom_iterator TheoryData::end() const {
	return begin() + numAtoms();
}
bool TheoryData::hasTerm(Id_t id) const {
	return id < numTerms() && terms()[id].valid();
}
bool TheoryData::isNewTerm(Id_t id) const {
	return hasTerm(id) && id >= frame_.term;
}
bool TheoryData::hasElement(Id_t id) const {
	return id < numElems() && elems()[id] != 0;
}
bool TheoryData::isNewElement(Id_t id) const {
	return hasElement(id) && id >= frame_.elem;
}
const TheoryTerm& TheoryData::getTerm(Id_t id) const {
	POTASSCO_REQUIRE(hasTerm(id), "Unknown term '%u'", unsigned(id));
	return terms()[id];
}
const TheoryElement& TheoryData::getElement(Id_t id) const {
	POTASSCO_REQUIRE(hasElement(id), "Unknown element '%u'", unsigned(id));
	return *elems()[id];
}
void TheoryData::accept(Visitor& out, VisitMode m) const {
	for (atom_iterator aIt = m == visit_current ? currBegin() : begin(), aEnd = end(); aIt != aEnd; ++aIt) {
		out.visit(*this, **aIt);
	}
}
void TheoryData::accept(const TheoryTerm& t, Visitor& out, VisitMode m) const {
	if (t.type() == Theory_t::Compound) {
		for (TheoryTerm::iterator it = t.begin(), end = t.end(); it != end; ++it) {
			if (doVisitTerm(m, *it)) out.visit(*this, *it, getTerm(*it));
		}
		if (t.isFunction() && doVisitTerm(m, t.function())) { out.visit(*this, t.function(), getTerm(t.function())); }
	}
}
void TheoryData::accept(const TheoryElement& e, Visitor& out, VisitMode m) const {
	for (TheoryElement::iterator it = e.begin(), end = e.end(); it != end; ++it) {
		if (doVisitTerm(m, *it)) { out.visit(*this, *it, getTerm(*it)); }
	}
}
void TheoryData::accept(const TheoryAtom& a, Visitor& out, VisitMode m) const {
	if (doVisitTerm(m, a.term())) { out.visit(*this, a.term(), getTerm(a.term())); }
	for (TheoryElement::iterator eIt = a.begin(), eEnd = a.end(); eIt != eEnd; ++eIt) {
		if (doVisitElem(m, *eIt)) { out.visit(*this, *eIt, getElement(*eIt)); }
	}
	if (a.guard() && doVisitTerm(m, *a.guard())) { out.visit(*this, *a.guard(), getTerm(*a.guard())); }
	if (a.rhs() && doVisitTerm(m, *a.rhs()))     { out.visit(*this, *a.rhs(),   getTerm(*a.rhs())); }
}
TheoryData::Visitor::~Visitor() {}
StringSpan toSpan(const char* x) {
	return Potassco::toSpan(x, std::strlen(x));
}

} // namespace Potassco
