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
#pragma once

/*!
 * \file
 * \brief Defines various types for getting absolute times.
 */
namespace Clasp {
//! Returns the difference between the two given timepoints clamped to zero if it is negative.
constexpr auto diffTimeUnchecked(double tEnd, double tStart) -> double {
    double diff = tEnd - tStart;
    return diff >= 0 ? diff : 0.0;
}
//! A type for getting the current process time.
struct ProcessTime {
    static auto getTime() -> double;
    static auto diffTime(double tEnd, double tStart) -> double;
    static auto diffTime(double tStart) -> double;
};
//! A type for getting the current thread time.
struct ThreadTime {
    static auto getTime() -> double;
    static auto diffTime(double tEnd, double tStart) -> double;
    static auto diffTime(double tStart) -> double;
};
//! A tpe for getting the current wall-clock time.
struct RealTime {
    static auto getTime() -> double;
    static constexpr auto diffTime(double tEnd, double tStart) -> double { return diffTimeUnchecked(tEnd, tStart); }
    static auto diffTime(double tStart) -> double { return diffTime(getTime(), tStart); }
};
//! Returns whether the given value is a valid timepoint (normal or zero).
bool isValidTime(double d);

//! A class for measuring elapsed time.
/*!
 * \tparam TimeType must provide a static function TimeType::getTime() returning an absolute time
 *         and a static function TimeType::diffTime() returning the difference between two timepoints.
 */
template <typename TimeType>
class Timer {
public:
    constexpr Timer() = default;

    void start() { start_ = TimeType::getTime(); }
    void stop() { split(TimeType::getTime()); }
    void reset() { *this = Timer(); }
    //! Same as stop(), start();
    void lap() {
        double t;
        split(t = TimeType::getTime());
        start_ = t;
    }
    //! Returns the elapsed time (in seconds) for last start-stop cycle.
    [[nodiscard]] auto elapsed() const -> double { return split_; }
    //! Returns the total elapsed time for all start-stop cycles.
    [[nodiscard]] auto total() const -> double { return total_; }

private:
    void   split(double t) { total_ += (split_ = TimeType::diffTime(t, start_)); }
    double start_{0};
    double split_{0};
    double total_{0};
};

} // namespace Clasp
