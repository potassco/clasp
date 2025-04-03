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

#include <chrono>

#ifdef _WIN32
#define WIN32_LEAN_AND_MEAN // exclude APIs such as Cryptography, DDE, RPC, Shell, and Windows Sockets.
#define NOMINMAX            // do not let windows.h define macros min and max
#include <windows.h>        // GetProcessTimes, GetCurrentProcess, FILETIME

namespace Clasp {
using DurationType = std::chrono::duration<int64_t, std::ratio<1, std::nano::den / 100>>;
static DurationType toDuration(const FILETIME& t) {
    union Convert {
        FILETIME time;
        __int64  asUint;
    };
    return DurationType(Convert(t).asUint);
}
static double toSeconds(DurationType d) { return std::chrono::duration_cast<std::chrono::duration<double>>(d).count(); }

double RealTime::getTime() {
    FILETIME now;
    GetSystemTimeAsFileTime(&now);
    return toSeconds(toDuration(now));
}

double ProcessTime::getTime() {
    FILETIME ignoreStart, ignoreExit, user, system;
    GetProcessTimes(GetCurrentProcess(), &ignoreStart, &ignoreExit, &user, &system);
    return toSeconds(toDuration(user) + toDuration(system));
}

double ThreadTime::getTime() {
    FILETIME ignoreStart, ignoreExit, user, system;
    GetThreadTimes(GetCurrentThread(), &ignoreStart, &ignoreExit, &user, &system);
    return toSeconds(toDuration(user) + toDuration(system));
}

} // namespace Clasp
#else
#include <sys/resource.h> // getrusage
#include <sys/time.h>     // gettimeofday()
#ifdef __APPLE__
#include <mach/mach.h>
#include <mach/thread_info.h>
#endif
namespace Clasp {

template <std::integral T, std::integral U>
static double toSeconds(T seconds, U micros) {
    using S = std::chrono::duration<double>;
    return (S(seconds) + std::chrono::duration_cast<S>(std::chrono::microseconds(micros))).count();
}

static double toSeconds(const timeval& t) { return toSeconds(t.tv_sec, t.tv_usec); }

double RealTime::getTime() {
    struct timeval now = {};
    return gettimeofday(&now, nullptr) == 0 ? toSeconds(now) : 0.0;
}
inline double rusageTime(int who) {
    struct rusage usage = {};
    getrusage(who, &usage);
    return toSeconds(usage.ru_utime) + toSeconds(usage.ru_stime);
}
double ProcessTime::getTime() { return rusageTime(RUSAGE_SELF); }
double ThreadTime::getTime() {
    double res = 0.0;
#if defined(RUSAGE_THREAD)
    res = rusageTime(RUSAGE_THREAD);
#elif __APPLE__
    struct thread_basic_info t_info;
    mach_msg_type_number_t   t_info_count = TASK_BASIC_INFO_COUNT;
    if (thread_info(mach_thread_self(), THREAD_BASIC_INFO, (thread_info_t) &t_info, &t_info_count) == KERN_SUCCESS) {
        time_value_add(&t_info.user_time, &t_info.system_time);
        res = toSeconds(t_info.user_time.seconds, t_info.user_time.microseconds);
    }
#endif
    return res;
}

} // namespace Clasp
#endif
