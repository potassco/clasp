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

// This example demonstrates how user code can influence model enumeration.

static void excludeModel(const Clasp::Solver& s, const Clasp::Model& m) {
	Clasp::LitVec clause;
	for (uint32 i = 1; i <= s.decisionLevel(); ++i) {
		clause.push_back(~s.decision(i));
	}
	m.ctx->commitClause(clause);
}

void example4() {
	Clasp::ClaspConfig config;
	config.solve.enumMode  = Clasp::EnumOptions::enum_user;
	config.solve.numModels = 0;

	// The "interface" to the clasp library.
	Clasp::ClaspFacade libclasp;

	Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config);
	addSimpleProgram(asp);

	libclasp.prepare();

	// Start the actual solving process.
	for (Clasp::ClaspFacade::SolveHandle h = libclasp.solve(Clasp::SolveMode_t::Yield); h.next();) {
		// print the model
		printModel(libclasp.ctx.output, *h.model());
		// exclude this model
		excludeModel(*libclasp.ctx.solver(h.model()->sId), *h.model());
	}
	std::cout << "No more models!" << std::endl;
}
