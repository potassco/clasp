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
void example1(bool basicSolve) {
	// LogicProgram provides the interface for
	// defining logic programs.
	// It also preprocesses the program and converts it
	// to the internal solver format.
	// See logic_program.h for details.
	Clasp::Asp::LogicProgram lp;
	Potassco::RuleBuilder rb;

	// Among other things, SharedContext maintains a Solver object
	// which hosts the data and functions for CDNL answer set solving.
	// See shared_context.h for details.
	Clasp::SharedContext ctx;

	// startProgram must be called once before we can add atoms/rules
	lp.startProgram(ctx);

	// Define the rules of the program.
	Potassco::Atom_t a = lp.newAtom();
	Potassco::Atom_t b = lp.newAtom();
	lp.addRule(rb.start().addHead(a).addGoal(Potassco::neg(b)));
	lp.addRule(rb.start().addHead(b).addGoal(Potassco::neg(a)));

	// Populate output table.
	// The output table defines what is printed for a literal
	// that is part of an answer set.
	lp.addOutput("a", a);
	lp.addOutput("b", b);
	// It is not limited to atoms. For example, the following
	// statement results in the ouput "~b" whenever b is not
	// in a stable model.
	lp.addOutput("~b", Potassco::neg(b));
	// And we always want to have "eureka"...
	lp.addOutput("eureka", Potassco::toSpan<Potassco::Lit_t>());

	// Once all rules are defined, call endProgram() to load the (simplified)
	// program into the context object.
	lp.endProgram();

	// Since we want to compute more than one
	// answer set, we need an enumerator.
	// See enumerator.h for details
	Clasp::ModelEnumerator enumerator;
	enumerator.init(ctx);

	// We are done with problem setup.
	// Prepare for solving.
	ctx.endInit();

	if (basicSolve) {
		std::cout << "With Clasp::BasicSolve" << std::endl;
		// BasicSolve implements a basic search for a model.
		// It handles the various strategies like restarts, deletion, etc.
		Clasp::BasicSolve solve(*ctx.master());
		// Prepare the solver for enumeration.
		enumerator.start(solve.solver());
		while (solve.solve() == Clasp::value_true) {
			// Make the enumerator aware of the new model and
			// let it compute a new constraint and/or backtracking level.
			if (enumerator.commitModel(solve.solver())) { printModel(ctx.output, enumerator.lastModel()); }
			// Integrate the model into the search and thereby prepare
			// the solver for the search for the next model.
			enumerator.update(solve.solver());
		}
		std::cout << "No more models!" << std::endl;
	}
	else {
		std::cout << "With Clasp::SequentialSolve" << std::endl;
		// SequentialSolve combines a BasicSolve object,
		// which implements search for a model and handles
		// various strategies like restarts, deletion, etc.,
		// with an enumerator to provide more complex reasoning,
		// like enumeration or optimization.
		Clasp::SequentialSolve solve;
		solve.setEnumerator(enumerator);
		// Start the solve algorithm and prepare solver for enumeration.
		solve.start(ctx);
		// Extract and print models one by one.
		while (solve.next()) {
			printModel(ctx.output, solve.model());
		}
		if (!solve.more()) {
			std::cout << "No more models!" << std::endl;
		}
	}
}

void example1() {
	example1(true);
	example1(false);
}
