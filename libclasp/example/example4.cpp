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

// Gets models from the ClaspFacade and guides enumeration by adding constraints.
class ModelHandler : public Clasp::EventHandler {
public:
	ModelHandler() {}
	bool onModel(const Clasp::Solver& s, const Clasp::Model& m) {
		printModel(s.symbolTable(), m);
		// exclude this model
		Clasp::LitVec clause;
		for (uint32 i = 1; i <= s.decisionLevel(); ++i) {
			clause.push_back( ~s.decision(i) );
		}
		return m.ctx->commitClause(clause);
	}
};

void example4() {
	Clasp::ClaspConfig config;
	config.solve.enumMode  = Clasp::EnumOptions::enum_user;
	config.solve.numModels = 0;
	
	// The "interface" to the clasp library.
	Clasp::ClaspFacade libclasp;

	Clasp::Asp::LogicProgram& asp = libclasp.startAsp(config);
	asp.setAtomName(1, "a");
	asp.setAtomName(2, "b");
	asp.startRule(Clasp::Asp::BASICRULE).addHead(1).addToBody(2, false).endRule();
	asp.startRule(Clasp::Asp::BASICRULE).addHead(2).addToBody(1, false).endRule();
	
	libclasp.prepare();

	// Start the actual solving process.
	ModelHandler handler;
	libclasp.solve(&handler);
	std::cout << "No more models!" << std::endl;
}