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

// Add the libclasp directory to the list of 
// include directoies of your build system.
#include <clasp/clasp_facade.h>
#include <clasp/solver.h>
#include "example.h"

// This example uses the ClaspFacade to compute
// the stable models of the program
//    a :- not b.
//    b :- not a.
//
// The ClaspFacade is a convenient wrapper for the services of the clasp library.
// See clasp_facade.h for details.


// In order to get models from the ClaspFacade, we must provide a suitable
// event handler.
class ModelPrinter : public Clasp::EventHandler {
public:
	ModelPrinter() {}
	bool onModel(const Clasp::Solver& s, const Clasp::Model& m) {
		printModel(s.symbolTable(), m);
		return true;
	}
};

void example2() {
	// Aggregates configuration options.
	// Using config, you can control many parts of the search, e.g.
	// - the amount and kind of preprocessing
	// - the enumerator to use and the number of models to compute
	// - the heuristic used for decision making
	// - the restart strategy
	// - ...
	Clasp::ClaspConfig config;
	// We want to compute all models but
	// otherwise we use the default configuration.
	config.solve.numModels = 0;
	
	// The "interface" to the clasp library.
	Clasp::ClaspFacade libclasp;

	// LogicProgram provides the interface for defining logic programs.
	// The returned object is already setup and ready to use.
	// See logic_program.h for details.
	Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config);
	asp.setAtomName(1, "a");
	asp.setAtomName(2, "b");
	asp.startRule(Clasp::Asp::BASICRULE).addHead(1).addToBody(2, false).endRule();
	asp.startRule(Clasp::Asp::BASICRULE).addHead(2).addToBody(1, false).endRule();
	
	// We are done with problem setup. 
	// Prepare the problem for solving.
	libclasp.prepare();

	// Start the actual solving process.
	ModelPrinter printer;
	libclasp.solve(&printer);
	std::cout << "No more models!" << std::endl;
}