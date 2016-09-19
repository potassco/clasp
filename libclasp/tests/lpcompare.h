// 
// Copyright (c) Benjamin Kaufmann
// 
// This file is part of Clasp. See http://www.cs.uni-potsdam.de/clasp/ 
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

#ifndef TEST_LPCOMPARE_H_INCLUDED
#define TEST_LPCOMPARE_H_INCLUDED

#include <string>
#include <vector>
#include <sstream>
#include <algorithm>
#include <clasp/logic_program.h>
#include <clasp/parser.h>
#include <potassco/aspif_text.h>

namespace Clasp { namespace Test {
inline std::string& trimR(std::string& r) {
	std::string::size_type p = r.find_last_not_of(" ");
	if (p != r.size() - 1) {
		r.erase(p+1);
	}
	return r;
}
inline bool compareProgram(std::stringstream& exp, std::stringstream& actual) {
	std::vector<std::string> lines;
	if (!exp) return !actual;
	while (exp) {
		for (std::string r; std::getline(exp, r) && r != "0";) {
			lines.push_back(trimR(r));
		}
		for (std::string r; std::getline(actual, r) && r != "0";) {
			std::vector<std::string>::iterator it = std::find(lines.begin(), lines.end(), trimR(r));
			if (it == lines.end()) { return false; }
			lines.erase(it);
		}
		if (!lines.empty()) { return false; }
	}
	return true;
}
inline bool findProgram(std::stringstream& what, std::stringstream& actual) {
	std::vector<std::string> lines;
	for (std::string r; std::getline(what, r);) {
		if (r != "0") { lines.push_back(trimR(r)); }
	}
	for (std::string r; std::getline(actual, r) && !lines.empty();) {
		std::vector<std::string>::iterator it;
		if (r != "0" && (it = std::find(lines.begin(), lines.end(), trimR(r))) != lines.end()) {
			lines.erase(it);
		}
	}
	return lines.empty();
}
inline bool compareSmodels(std::stringstream& exp, Asp::LogicProgram& prg) {
	std::stringstream str;
	AspParser::write(prg, str, AspParser::format_smodels);
	return compareProgram(exp, str);
}
inline bool findSmodels(std::stringstream& exp, Asp::LogicProgram& prg) {
	std::stringstream str;
	AspParser::write(prg, str, AspParser::format_smodels);
	return findProgram(exp, str);
}
struct NoStep : Asp::LogicProgramAdapter {
	NoStep(Asp::LogicProgram& p) : Asp::LogicProgramAdapter(p) {}
	void initProgram(bool) {}
	void beginStep()       {}
	void endStep()         {}
};
inline void lpAdd(Asp::LogicProgram& lp, const char* prg) {
	NoStep adapt(lp);
	Potassco::AspifTextInput input(&adapt);
	std::stringstream str;
	str << prg << "\n";
	CLASP_FAIL_IF(!input.accept(str) || !input.parse(), "invalid program");
}

}}
#endif
