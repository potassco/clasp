//
// Copyright (c) 2016, Benjamin Kaufmann
//
// This file is part of Potassco.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
#ifndef LIBLP_ASPIF_TEXT_H_INCLUDED
#define LIBLP_ASPIF_TEXT_H_INCLUDED
#include <potassco/match_basic_types.h>
#include <potassco/theory_data.h>
#include <cstring>
namespace Potassco {

//! Class for parsing logic programs in ground text format.
/*!
 * \addtogroup ParseType
 */
class AspifTextInput : public ProgramReader {
public:
	//! Creates a new object and associates it with the given output if any.
	AspifTextInput(AbstractProgram* out);
	//! Sets the program to which parsed elements should be output.
	void setOutput(AbstractProgram& out);
protected:
	//! Checks whether stream starts with a valid token.
	virtual bool doAttach(bool& inc);
	//! Attempts to parses the current step or throws an exception on error.
	/*!
	 * The function calls beginStep()/endStep() on the associated
	 * output object before/after parsing the current step.
	 */
	virtual bool doParse();
	//! Parses statements until next step directive or input is exhausted.
	bool parseStatements();
private:
	void   skipws();
	bool   matchDirective();
	void   matchRule(char peek);
	void   matchAtoms(const char* seps);
	void   matchLits();
	void   matchCondition();
	void   matchAgg();
	bool   match(const char* ts, bool required = true);
	Atom_t matchId();
	Lit_t  matchLit();
	int    matchInt();
	void   matchTerm();
	void   matchAtomArg();
	void   matchStr();
	void   startString();
	void   push(char c);
	void   endString();
	AbstractProgram* out_;
	BasicStack       data_;
	uint32_t         strStart_;
	uint32_t         strPos_;
};

class AspifTextOutput : public Potassco::AbstractProgram {
public:
	AspifTextOutput(std::ostream& os);
	~AspifTextOutput();
	virtual void initProgram(bool incremental);
	virtual void beginStep();
	virtual void rule(Head_t ht, const AtomSpan& head, const LitSpan& body);
	virtual void rule(Head_t ht, const AtomSpan& head, Weight_t bound, const WeightLitSpan& lits);
	virtual void minimize(Weight_t prio, const WeightLitSpan& lits);
	virtual void output(const StringSpan& str, const LitSpan& cond);
	virtual void external(Atom_t a, Value_t v);
	virtual void assume(const LitSpan& lits);
	virtual void project(const AtomSpan& atoms);
	virtual void acycEdge(int s, int t, const LitSpan& condition);
	virtual void heuristic(Atom_t a, Heuristic_t t, int bias, unsigned prio, const LitSpan& condition);

	virtual void theoryTerm(Id_t termId, int number);
	virtual void theoryTerm(Id_t termId, const StringSpan& name);
	virtual void theoryTerm(Id_t termId, int compound, const IdSpan& args);
	virtual void theoryElement(Id_t elementId, const IdSpan& terms, const LitSpan& cond);
	virtual void theoryAtom(Id_t atomOrZero, Id_t termId, const IdSpan& elements);
	virtual void theoryAtom(Id_t atomOrZero, Id_t termId, const IdSpan& elements, Id_t op, Id_t rhs);
	virtual void endStep();
private:
	template <class T>
	T pop() {
		const T* x = static_cast<T*>(directives_.get(front_));
		front_ += sizeof(T);
		return *x;
	}
	template <class T>
	AspifTextOutput& pushSpan(const Span<T>& span) {
		uint32_t n = static_cast<uint32_t>(size(span));
		directives_.push(n);
		std::memcpy(directives_.makeSpan<T>(n), begin(span), n * sizeof(T));
		return *this;
	}
	AspifTextOutput& push(uint32_t t) {
		directives_.push(t);
		return *this;
	}
	AspifTextOutput& push(int32_t t) {
		directives_.push(t);
		return *this;
	}
	AspifTextOutput& push(Directive_t t) {
		return push(static_cast<uint32_t>(t));
	}
	Id_t addString(const StringSpan& str);
	std::ostream& printName(std::ostream& os, Lit_t lit) const;
	void addAtom(Atom_t id, const StringSpan& str);
	void writeDirectives();
	AspifTextOutput(const AspifTextOutput&);
	AspifTextOutput& operator=(const AspifTextOutput&);
	std::ostream& os_;
	struct Extra;
	BasicStack directives_;
	TheoryData theory_;
	Extra*     extra_;
	int        step_;
	uint32_t   front_;
};

}
#endif
