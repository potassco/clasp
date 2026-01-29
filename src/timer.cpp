//
// Copyright (c) 2006-present Benjamin Kaufmann
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
#include <clasp/util/timer.h>
#include <potassco/platform.h>

#include <chrono>
#include <cmath>

namespace Clasp {
bool isValidTime(double d) { return std::isfinite(d); }
template <typename X, typename Y>
static constexpr auto toSeconds(std::chrono::duration<X, Y> d) -> double {
    using Seconds = std::chrono::duration<double>;
    return std::chrono::duration_cast<Seconds>(d).count();
}
template <typename T>
static double diffTimeChecked(double start, const double* optEnd = nullptr) {
    if (not isValidTime(start)) {
        return start;
    }
    auto end = optEnd ? *optEnd : T::getTime();
    return isValidTime(end) ? diffTimeUnchecked(end, start) : end;
}

double RealTime::getTime() { return toSeconds(std::chrono::steady_clock::now().time_since_epoch()); }
double ProcessTime::getTime() { return Potassco::getProcessTime(); }
double ProcessTime::diffTime(double tEnd, double tStart) { return diffTimeChecked<ProcessTime>(tStart, &tEnd); }
double ProcessTime::diffTime(double tStart) { return diffTimeChecked<ProcessTime>(tStart); }
double ThreadTime::getTime() { return Potassco::getThreadTime(); }
double ThreadTime::diffTime(double tEnd, double tStart) { return diffTimeChecked<ThreadTime>(tStart, &tEnd); }
double ThreadTime::diffTime(double tStart) { return diffTimeChecked<ThreadTime>(tStart); }

} // namespace Clasp
