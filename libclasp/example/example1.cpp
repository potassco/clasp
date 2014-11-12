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
// Add the libclasp directory to the list of 
// include directoies of your build system.
#include <clasp/logic_program.h>    // for defining logic programs
#include <clasp/unfounded_check.h>  // unfounded set checkers
#include <clasp/model_enumerators.h>// for enumerating answer sets
#include <clasp/solve_algorithms.h> // for enumerating answer sets


// Compute the stable models of the program
//    a :- not b.
//    b :- not a.
void example1() {
	// LogicProgram provides the interface for 
	// defining logic programs.
	// It also preprocesses the program and converts it
	// to the internal solver format.
	// See logic_program.h for details.
	Clasp::Asp::LogicProgram lp;
	
	// Among other things, SharedContext maintains a Solver object 
	// which hosts the data and functions for CDNL answer set solving.
	// SharedContext also contains the symbol table which stores the 
	// mapping between atoms of the logic program and the 
	// propositional literals in the solver.
	// See shared_context.h for details.
	Clasp::SharedContext ctx;
	
	// startProgram must be called once before we can add atoms/rules
	lp.startProgram(ctx);
	
	// Populate symbol table. Each atoms must have a unique id, the name is optional.
	// The symbol table then maps the ids to the propositional 
	// literals in the solver.
	lp.setAtomName(1, "a");
	lp.setAtomName(2, "b");
	
	// Define the rules of the program.
	lp.startRule(Clasp::Asp::BASICRULE).addHead(1).addToBody(2, false).endRule();
	lp.startRule(Clasp::Asp::BASICRULE).addHead(2).addToBody(1, false).endRule();
	
	// Once all rules are defined, call endProgram() to load the (simplified)
	// program into the context object.
	lp.endProgram();
	
	// Since we want to compute more than one
	// answer set, we need an enumerator.
	// See enumerator.h for details
	Clasp::ModelEnumerator enumerator;
	enumerator.init(ctx, 0);

	// We are done with problem setup. 
	// Prepare for solving.
	ctx.endInit();
	// BasicSolve implements a basic search for a model.
	// It handles the various strategies like restarts, deletion, etc.
	Clasp::BasicSolve solve(*ctx.master());
	// Prepare the solver for enumeration.
	enumerator.start(solve.solver());
	while (solve.solve() == Clasp::value_true) {
		// Make the enumerator aware of the new model and
		// let it compute a new constraint and/or backtracking level.
		if (enumerator.commitModel(solve.solver())) { printModel(ctx.symbolTable(), enumerator.lastModel()); }
		// Integrate the model into the search and thereby prepare 
		// the solver for the search for the next model.
		enumerator.update(solve.solver());
	}
	std::cout << "No more models!" << std::endl;
}


