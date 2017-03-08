//
// Copyright (c) 2016-2017 Benjamin Kaufmann
//
// This file is part of Potassco.
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
#ifndef LIBLP_ASPIF_TEXT_H_INCLUDED
#define LIBLP_ASPIF_TEXT_H_INCLUDED
#include <potassco/match_basic_types.h>
#include <potassco/theory_data.h>
#include <cstring>
#include <string>
namespace Potassco {

//! Class for parsing logic programs in ground text format.
/*!
 * \ingroup ParseType
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

//! Class for writing logic programs in ground text format.
/*!
 * Writes a logic program in human-readable text format.
 * \ingroup WriteType
 */
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

	void addAtom(Atom_t id, const StringSpan& str);
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
	std::ostream& printName(std::ostream& os, Lit_t lit) const;
	void writeDirectives();
	void visitTheories();
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

//! Converts a given theory atom to a string.
class TheoryAtomStringBuilder {
public:
	std::string toString(const TheoryData& td, const TheoryAtom& a);
private:
	TheoryAtomStringBuilder& add(char c) { res_.append(1, c); return *this; }
	TheoryAtomStringBuilder& add(const char* s) { res_.append(s); return *this; }
	TheoryAtomStringBuilder& add(const std::string& s) { res_.append(s); return *this; }
	TheoryAtomStringBuilder& term(const TheoryData& td, const TheoryTerm& a);
	TheoryAtomStringBuilder& element(const TheoryData& td, const TheoryElement& a);
	bool function(const TheoryData& td, const TheoryTerm& f);

	virtual LitSpan     getCondition(Id_t condId) const = 0;
	virtual std::string getName(Atom_t atomId)    const = 0;
	std::string res_;
};

} // namespace Potassco
#endif
