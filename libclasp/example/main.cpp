// 
// Copyright (c) 2009, Benjamin Kaufmann
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
#include "example.h"
#include <clasp/enumerator.h>
#include <clasp/Solver.h>
void printModel(const Clasp::SymbolTable& symTab, const Clasp::Model& model) {
	std::cout << "Model " << model.num << ": \n";
	// Print each named atom that is true w.r.t the current model.
	for (Clasp::SymbolTable::const_iterator it = symTab.begin(); it != symTab.end(); ++it) {
		if (model.isTrue(it->second.lit) && !it->second.name.empty()) {
			std::cout << it->second.name.c_str() << " ";
		}
	}
	std::cout << std::endl;
}

#define RUN(x) try { std::cout << "*** Running " << static_cast<const char*>(#x) << " ***" << std::endl; x(); } catch (const std::exception& e) { std::cout << " *** ERROR: " << e.what() << std::endl; }

int main() {
	RUN(example1);
	RUN(example2);
#if WITH_THREADS
	RUN(example3);
#endif
	RUN(example4);
}
