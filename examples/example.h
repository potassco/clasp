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
#include <clasp/config.h>
#include <iostream>
namespace Clasp {
	struct Model;
	class  OutputTable;
	namespace Asp { class  LogicProgram; }
}
void printModel(const Clasp::OutputTable& out, const Clasp::Model& model);
void addSimpleProgram(Clasp::Asp::LogicProgram& prg);

void example1();
void example2();
void example3();
void example4();
