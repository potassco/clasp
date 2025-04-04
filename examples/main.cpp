//
// Copyright (c) 2009-present Benjamin Kaufmann
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
#include "example.h"
#include <clasp/enumerator.h>
#include <clasp/solver.h>
void printModel(const Clasp::OutputTable& out, const Clasp::Model& model) {
    std::cout << "Model " << model.num << ": \n";
    // Print elements that are true wrt the current model.
    for (const auto& p : out.pred_range()) {
        if (model.isTrue(p.cond)) {
            std::cout << p.name.view() << " ";
        }
    }
    // Print additional output variables.
    for (auto v : out.vars_range()) {
        std::cout << (model.isTrue(Clasp::posLit(v)) ? static_cast<int>(v) : -static_cast<int>(v)) << " ";
    }
    std::cout << std::endl;
}

#define RUN(x)                                                                                                         \
    try {                                                                                                              \
        std::cout << "*** Running " << static_cast<const char*>(#x) << " ***" << std::endl;                            \
        x();                                                                                                           \
    }                                                                                                                  \
    catch (const std::exception& e) {                                                                                  \
        std::cout << " *** ERROR: " << e.what() << std::endl;                                                          \
    }

int main() {
    RUN(example1);
    RUN(example2);
    RUN(example3);
    RUN(example4);
}
