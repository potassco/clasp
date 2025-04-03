//
// Copyright (c) 2013-present Benjamin Kaufmann
//
// This file is part of Clasp. See https://potassco.org/clasp/
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
#pragma once
/*!
 * \file
 * \brief Forward declarations of important clasp types.
 */

//! Root namespace for all types and functions of libclasp.
namespace Clasp {
class SharedContext;
class MinimizeBuilder;
class SharedMinimizeData;
class Configuration;
class Constraint;
class ConstraintInfo;
class Solver;
struct Model;
//! Supported problem types.
enum class ProblemType { sat = 0, pb = 1, asp = 2 };
class ProgramBuilder;
class ProgramParser;
class SatBuilder;
class PBBuilder;
class ExtDepGraph;
//! Namespace for types and functions used to define ASP programs.
namespace Asp {
class LogicProgram;
class Preprocessor;
class LpStats;
class PrgAtom;
class PrgBody;
class PrgDisj;
class PrgHead;
class PrgNode;
class PrgDepGraph;
struct PrgEdge;
} // namespace Asp
} // namespace Clasp
