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

#include <clasp/config.h>
#include <potassco/bits.h>

#include <algorithm>
#include <ranges>
#if defined(__cpp_lib_saturation_arithmetic) && __cpp_lib_saturation_arithmetic == 202311L
#include <numeric>
#endif

#if defined(__GNUC__) || defined(__clang__)
// Disable deprecation warnings from std::{unary,binary}_function
#pragma GCC system_header
#endif

/*!
 * \file
 * \brief Some utility types and functions.
 */
namespace Clasp {

/*!
 * \defgroup misc Miscellaneous
 * \brief Miscellaneous and Internal Stuff not specific to clasp.
 */
//@{

//! Computes n choose k.
constexpr uint64_t choose(unsigned n, unsigned k) {
    if (k > n) {
        return 0;
    }
    if (auto sym = n - k; k > sym) {
        k = sym;
    }
    uint64_t res = k > 0 ? n : 1;
    for (unsigned i = 2; i <= k; ++i) {
        res *= (n + 1 - i);
        res /= i;
    }
    return res;
}
constexpr double ratio(uint64_t x, uint64_t y) { return y ? static_cast<double>(x) / static_cast<double>(y) : 0; }
constexpr double ratio(uint64_t x, uint64_t y, double z) { return y ? ratio(x, y) : z; }
constexpr double percent(uint64_t x, uint64_t y) { return ratio(x, y) * 100.0; }

//! A very simple but fast Pseudo-random number generator.
/*!
 * \note This class is a replacement for the standard rand-function. It is provided
 * in order to get reproducible random numbers among different compilers.
 */
class Rng {
public:
    constexpr explicit Rng(uint32_t seed = 1) : seed_(seed) {}

    //! Sets the starting point for random-number generation.
    /*!
     * The function sets the starting point for generating a series of pseudorandom integers.
     * To reinitialize the generator, use 1 as the seed argument. Any other value for seed
     * sets the generator to a random starting point. Calling rand() before any call to srand()
     * generates the same sequence as calling srand() with seed passed as 1.
     */
    constexpr void srand(uint32_t seed) { seed_ = seed; }

    //! Generates a pseudorandom number
    /*!
     * The rand function returns a pseudorandom integer in the range 0 to 32767
     * Use the srand function to seed the pseudorandom-number generator before calling rand.
     */
    constexpr uint32_t rand() { return (((seed_ = seed_ * 214013L + 2531011L) >> 16) & 0x7fff); }

    //! random floating point number in the range [0, 1.0)
    constexpr double drand() { return this->rand() / static_cast<double>(0x8000u); }

    //! random number in the range [0, max)
    constexpr unsigned irand(unsigned max) { return static_cast<unsigned>(drand() * max); }

    [[nodiscard]] constexpr uint32_t seed() const { return seed_; }

    constexpr uint32_t operator()(unsigned max) { return irand(max); }
    constexpr uint32_t operator()() { return rand(); }

    // Replacement for deprecated std::random_shuffle(first, last, *this).
    template <typename RandIt>
    constexpr void shuffle(RandIt first, RandIt last) {
        for (auto it = first + (first != last); it != last; ++it) {
            if (auto n = first + (*this)(static_cast<unsigned>(it - first) + 1); it != n) {
                std::iter_swap(it, n);
            }
        }
    }

private:
    uint32_t seed_;
};

class MovingAvg {
public:
    enum Type { avg_sma = 0, avg_ema = 1, avg_ema_log = 2, avg_ema_smooth = 3, avg_ema_log_smooth = 4 };

    MovingAvg(uint32_t window, Type type) : win_(window), full_(window == 0), ema_(type != avg_sma), smooth_(0) {
        assert(window > 0 || type == avg_sma);
        if (ema_) {
            smooth_      = (type >= avg_ema_smooth);
            extra_.alpha = (type & 1u) != 0 ? 2.0 / (window + 1) : 1.0 / (1u << Potassco::log2(window));
        }
        else if (window) {
            extra_.sma = new uint32_t[window];
        }
        else {
            extra_.num = 0;
        }
    }
    MovingAvg(const MovingAvg&)            = delete;
    MovingAvg& operator=(const MovingAvg&) = delete;

    ~MovingAvg() {
        if (not ema_ && win_) {
            delete[] extra_.sma;
        }
    }

    //! Updates the given exponential moving average with the given sample.
    /*!
     * Computes ema = current + ((sample - current)*alpha);
     */
    static constexpr double ema(double current, double sample, double alpha) {
        return current + (alpha * (sample - current));
    }

    //! Updates the given cumulative moving average with the given sample.
    static constexpr double cma(double current, double sample, uint64_t numSeen) {
        return (sample + (current * static_cast<double>(numSeen))) / static_cast<double>(numSeen + 1);
    }

    //! Updates the given simple moving average with the given sample.
    static constexpr double sma(double current, uint32_t sample, uint32_t* buffer, uint32_t cap, uint32_t pos,
                                bool full) {
        assert(pos < cap);
        auto oldS   = static_cast<double>(buffer[pos]);
        auto newS   = static_cast<double>(sample);
        buffer[pos] = sample;
        return full ? current + ((newS - oldS) / cap) : cma(current, newS, pos);
    }

    static constexpr double smoothAlpha(double alpha, uint32_t pos) {
        return pos < 32 ? std::max(alpha, 1.0 / static_cast<double>(1u << pos)) : alpha;
    }

    bool push(uint32_t val) {
        if (not win_) {
            avg_ = cma(avg_, val, extra_.num++);
        }
        else if (not ema_) {
            avg_ = sma(avg_, val, extra_.sma, win_, pos_, valid());
        }
        else if (valid()) {
            avg_ = ema(avg_, val, extra_.alpha);
        }
        else {
            avg_ = smooth_ ? ema(avg_, val, smoothAlpha(extra_.alpha, pos_)) : cma(avg_, val, pos_);
        }
        if (++pos_ == win_) {
            pos_  = 0;
            full_ = 1;
        }
        return valid();
    }

    void clear() {
        avg_ = 0.0;
        pos_ = 0;
        not win_ ? extra_.num = 0 : full_ = 0;
    }

    [[nodiscard]] double   get() const { return avg_; }
    [[nodiscard]] bool     valid() const { return full_ != 0; }
    [[nodiscard]] uint32_t win() const { return win_; }

private:
    union Extra {
        uint32_t* sma;   // Buffer for SMA
        double    alpha; // Smoothing factor for EMA
        uint64_t  num;   // Number of data points for CMA
    };
    double   avg_{0.0};    // Current average
    Extra    extra_{};     // Additional data for active average type
    uint32_t pos_{0};      // Number of data points % window size
    uint32_t win_    : 29; // Window size (for SMA/EMA)
    uint32_t full_   : 1;  // Enough data points seen?
    uint32_t ema_    : 1;  // Exponential Moving Average?
    uint32_t smooth_ : 1;  // Use smoothing or cumulative moving average for first (ema) data points?
};

//! Unary operator function that calls p->destroy().
struct DestroyObject {
    template <typename T>
    void operator()(T* p) const {
        if (p) {
            p->destroy();
        }
    }
};
//! Unary operator function that calls delete p.
struct DeleteObject {
    template <typename T>
    void operator()(T* p) const {
        std::default_delete<T>()(p);
    }
};
//! Unary operator function that calls p->release().
struct ReleaseObject {
    template <typename T>
    void operator()(T* p) const {
        if (p) {
            p->release();
        }
    }
};

template <typename T, std::size_t N = 1>
class TaggedPtr {
public:
    static_assert(N > 0 && N < (sizeof(void*) * CHAR_BIT), "invalid number of tag bits");
    static constexpr auto c_mask = Potassco::bit_max<uintptr_t>(N);

    constexpr TaggedPtr() noexcept = default;
    constexpr explicit TaggedPtr(T* ptr) noexcept : ptr_(reinterpret_cast<uintptr_t>(ptr)) {
        static_assert(alignof(T) > c_mask, "too many tag bits");
    }

    template <auto I>
    requires(static_cast<std::size_t>(I) < N)
    [[nodiscard]] constexpr bool test() const noexcept {
        return Potassco::test_bit(ptr_, I);
    }
    [[nodiscard]] constexpr bool any() const noexcept { return Potassco::test_any(ptr_, c_mask); }
    template <auto I>
    requires(static_cast<std::size_t>(I) < N)
    constexpr void set() noexcept {
        Potassco::store_set_bit(ptr_, I);
    }
    template <auto I>
    requires(static_cast<std::size_t>(I) < N)
    constexpr void clear() noexcept {
        Potassco::store_clear_bit(ptr_, I);
    }

    constexpr explicit operator bool() const noexcept { return get() != nullptr; }

    constexpr T&   operator*() const noexcept { return *get(); }
    constexpr T*   operator->() const noexcept { return get(); }
    constexpr T*   get() const noexcept { return reinterpret_cast<T*>(Potassco::clear_mask(ptr_, c_mask)); }
    constexpr void swap(TaggedPtr& o) noexcept { std::swap(ptr_, o.ptr_); }

private:
    uintptr_t ptr_{};
};

template <std::integral T>
constexpr T clamp(T val, std::type_identity_t<T> lo, std::type_identity_t<T> hi) {
    return std::clamp(val, lo, hi);
}
#if defined(__cpp_lib_saturation_arithmetic) && __cpp_lib_saturation_arithmetic != 202311L
using std::saturate_cast;
#else
template <std::integral Res, std::integral U>
constexpr Res saturate_cast(U x) noexcept {
    if (std::in_range<Res>(x)) {
        return static_cast<Res>(x);
    }
    if (Res lo = std::numeric_limits<Res>::min(); x < static_cast<U>(lo)) {
        return lo;
    }
    return std::numeric_limits<Res>::max();
}
#endif

//! A (numerical) range represented by a low and a high value.
struct Range32 {
    constexpr Range32(uint32_t x, uint32_t y) : lo(x), hi(y) {
        if (x > y) {
            hi = x;
            lo = y;
        }
    }
    [[nodiscard]] constexpr uint32_t clamp(uint32_t val) const { return std::clamp(val, lo, hi); }

    uint32_t lo;
    uint32_t hi;
};

//! Generator functions for creating (lazy) half-open integer ranges.
//@{
//! Returns a (lazy) half-open range of integers [begin, end).
template <std::integral T>
constexpr auto irange(T begin, std::type_identity_t<T> end) {
    return std::views::iota(begin, end);
}
//! Behaves like irange(0u, size).
constexpr auto irange(unsigned size) { return irange(0u, size); }
//! Behaves like irange(r.size()).
template <typename T>
requires requires(const T& x) {
    { x.size() } -> std::unsigned_integral;
}
constexpr auto irange(const T& r) {
    return irange(0u, size32(r));
}
//! Behaves like irange(N).
template <typename T, unsigned N>
constexpr auto irange(const T (&)[N]) {
    return irange(0u, N);
}
//@}
//@}

//! Base class for library events.
struct Event {
    template <typename T>
    struct Id {
        static const uint32_t id_s;
    };

    //! Set of known event sources.
    enum Subsystem { subsystem_facade = 0, subsystem_load = 1, subsystem_prepare = 2, subsystem_solve = 3 };
    //! Possible verbosity levels.
    enum Verbosity { verbosity_quiet = 0, verbosity_low = 1, verbosity_high = 2, verbosity_max = 3 };
    template <typename SelfType>
    Event(SelfType*, Subsystem sys, Verbosity verbosity)
        : system(sys)
        , verb(verbosity)
        , op(0)
        , id(eventId<SelfType>()) {
        static_assert(std::is_base_of_v<Event, SelfType>);
    }
    static uint32_t nextId();
    template <typename T>
    static uint32_t eventId() {
        return Id<T>::id_s;
    }

    uint32_t system : 2;  //!< One of Event::Subsystem - subsystem that produced the event.
    uint32_t verb   : 2;  //!< One of Event::Verbosity - the verbosity level of this event.
    uint32_t op     : 8;  //!< Operation that triggered the event.
    uint32_t id     : 16; //!< Type id of event.
};
template <typename T>
const uint32_t Event::Id<T>::id_s = Event::nextId();

template <typename ToType>
const ToType* event_cast(const Event& ev) {
    return ev.id == Event::eventId<ToType>() ? static_cast<const ToType*>(&ev) : nullptr;
}

template <typename... Ts>
struct Overload : Ts... {
    using Ts::operator()...;
};

//! Unsigned type with N-1 bits payload and 1-bit spin-lock or pointer type with LSB used as spin-lock bit.
template <typename T = uint32_t>
class LockedValue {
public:
    static_assert(std::unsigned_integral<T> || std::is_pointer_v<T>, "must be unsigned or pointer");

    explicit LockedValue(T val = {}) : val_(fromVal(val, 0u)) {}

    [[nodiscard]] T value() const noexcept { return toVal(val_.load(mt::memory_order_acquire)); }

    T lock() noexcept {
        T ret;
        while (not try_lock(&ret)) { wait(val_.ref(), ret); }
        return ret;
    }
    bool try_lock(T* out = nullptr) noexcept {
        T ignore;
        return try_lock(val_.ref(), out ? *out : ignore);
    }
    void store_unlock(T value) noexcept {
        val_.store(fromVal(value, 0u), mt::memory_order_release);
        notify(val_.ref());
    }
    void unlock() noexcept { store_unlock({}); }

private:
    using StoreType = std::conditional_t<std::is_pointer_v<T>, uintptr_t, T>;
    static T toVal(StoreType in) {
        if constexpr (std::is_pointer_v<T>) {
            return reinterpret_cast<T>(Potassco::clear_mask(in, 1u));
        }
        else {
            return in >> 1u;
        }
    }
    static StoreType fromVal(T in, StoreType locked) {
        if constexpr (std::is_pointer_v<T>) {
            assert(not Potassco::test_bit(reinterpret_cast<uintptr_t>(in), 0u));
            return reinterpret_cast<uintptr_t>(in) | locked;
        }
        else {
            assert(in < std::numeric_limits<T>::max() / 2);
            return (in << 1u) | locked;
        }
    }

    template <typename A>
    static bool try_lock(A& address, T& out) {
        auto x = address.fetch_or(1u, mt::memory_order_acquire);
        out    = toVal(x);
        return not Potassco::test_bit(x, 0u);
    }
    template <typename A>
    static void wait(A& address, T v) {
        if constexpr (requires { address.wait(fromVal(v, 1u), mt::memory_order_relaxed); }) {
            address.wait(fromVal(v, 1u), mt::memory_order_relaxed);
        }
    }
    template <typename A>
    static void notify(A& address) {
        if constexpr (requires { address.notify_one(); }) {
            address.notify_one();
        }
    }
    mt::ThreadSafe<StoreType> val_;
};

class RefCount {
public:
    explicit RefCount(uint32_t init = 1) : rc_{init} {}
    [[nodiscard]] uint32_t count() const noexcept { return rc_.load(mt::memory_order_acquire); }
    operator uint32_t() const noexcept { return count(); }
    void     reset(uint32_t n) { rc_.store(n, mt::memory_order_relaxed); }
    void     add(uint32_t n = 1) { rc_.add(n, mt::memory_order_relaxed); }
    bool     release(uint32_t n = 1) { return release_fetch(n) == 0; }
    uint32_t release_fetch(uint32_t n = 1) { return rc_.sub(n); }

private:
    mt::ThreadSafe<uint32_t> rc_;
};

class SigAtomic {
public:
    SigAtomic() = default;
    [[nodiscard]] int value() const noexcept { return sig_.load(mt::memory_order_acquire); }
    operator int() const noexcept { return value(); }
    bool set_if_unset(int sig) {
        int unset = 0;
        return sig_.compare_exchange_strong(unset, sig);
    }
    int exchange(int sig) { return sig_.exchange(sig, mt::memory_order_acquire); }

private:
    mt::ThreadSafe<int> sig_{0};
};

} // namespace Clasp
