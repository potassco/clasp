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
#include <clasp/util/pod_vector.h>

#include <cassert>
#include <span>
#if CLASP_USE_STD_VECTOR
#include <vector>
#endif

namespace Clasp {

/*!
 * \defgroup misc Miscellaneous
 * \brief Vector extension API and (range) helpers.
 */
//@{

#if CLASP_USE_STD_VECTOR
template <typename T>
using PodVector_t = std::vector<T>;
using std::erase;
using std::erase_if;
template <typename T>
constexpr void destructVec(std::vector<T>& vec) {
    vec.clear();
}
#else
template <typename T>
using PodVector_t = bk_lib::pod_vector<T>;
template <typename T>
constexpr void destructVec(bk_lib::pod_vector<T>& vec) {
    std::destroy(vec.begin(), vec.end());
    vec.clear();
}
#endif

constexpr auto toU32(std::size_t x) -> uint32_t {
    assert(std::in_range<uint32_t>(x));
    return static_cast<uint32_t>(x);
}
template <typename T>
POTASSCO_ATTR_INLINE constexpr auto size32(const T& c) -> uint32_t {
    if constexpr (std::is_same_v<decltype(std::size(c)), uint32_t>) {
        return std::size(c);
    }
    else {
        return toU32(std::size(c));
    }
}

//! Discard the contents of the given vector and restore it to its default-constructed state.
template <typename T>
constexpr void discardVec(PodVector_t<T>& vec) {
    static_assert(not std::is_same_v<PodVector_t<T>, bk_lib::pod_vector<T>> || std::is_trivially_destructible_v<T>);
    if constexpr (requires { vec.reset(); }) {
        vec.reset();
    }
    else {
        vec = PodVector_t<T>();
    }
}

//! Truncates the vector to the given size by removing the last `vec.size() - ns` elements.
/*!
 * \pre ns <= size().
 * \return The number of elements that were removed.
 */
template <typename T>
constexpr auto truncateVec(PodVector_t<T>& vec, typename PodVector_t<T>::size_type ns) -> uint32_t {
    auto n = size32(vec) - toU32(ns);
    if constexpr (requires { vec.pop(n); }) {
        vec.pop(n);
    }
    else {
        vec.erase(vec.begin() + static_cast<PodVector_t<T>::difference_type>(ns), vec.end());
    }
    return n;
}
//! Truncates the vector to the range `[vec.begin(), last)`.
/*!
 * \return The number of elements that were removed.
 */
template <typename T>
constexpr auto truncateVec(PodVector_t<T>& vec, typename PodVector_t<T>::iterator last) -> uint32_t {
    auto n = static_cast<uint32_t>(vec.end() - last);
    if constexpr (requires { vec.pop(n); }) {
        vec.pop(n);
    }
    else {
        vec.erase(last, vec.end());
    }
    return n;
}

//! Appends the elements in the range `[first, last)` to the vector.
template <typename T, typename It>
requires(not std::integral<It>)
constexpr void appendVec(PodVector_t<T>& vec, It first, It last) {
    if constexpr (requires { vec.append(first, last); }) {
        return vec.append(first, last);
    }
    else {
        vec.insert(vec.end(), first, last);
    }
}

//! Appends `n` copies of `val` to the vector.
template <typename T, typename ValT>
constexpr void appendVec(PodVector_t<T>& vec, uint32_t n, const ValT& val) {
    if constexpr (requires { vec.append(n, val); }) {
        return vec.append(n, val);
    }
    else {
        vec.insert(vec.end(), n, val);
    }
}

//! Appends the elements in the given range to the vector.
template <typename T, std::ranges::range R>
constexpr void appendVec(PodVector_t<T>& vec, R&& range) {
    appendVec(vec, range.begin(), range.end());
}

template <std::ranges::random_access_range R>
constexpr auto moveLeft(R& r, std::ranges::range_size_t<R> from,
                        std::ranges::range_size_t<R> to) -> std::ranges::iterator_t<R> {
    assert(from >= to);
    using DiffT = std::ranges::range_difference_t<R>;
    if (auto tail = r.size() - from; tail) {
        return std::move(r.begin() + static_cast<DiffT>(from), r.end(), r.begin() + static_cast<DiffT>(to));
    }
    return r.begin() + static_cast<DiffT>(to);
}

template <typename It, typename V>
constexpr auto contains(It first, It last, const V& v) -> decltype(std::find(first, last, v) != last) {
    return std::find(first, last, v) != last;
}

template <typename R, typename V>
constexpr auto contains(const R& range, const V& v) -> decltype(contains(range.begin(), range.end(), v)) {
    return contains(range.begin(), range.end(), v);
}

template <typename R>
constexpr auto drop(R&& range, std::size_t offset) {
    assert(offset <= range.size());
    return std::span(range.data() + offset, range.size() - offset);
}

//@}

//! A simple vector-based fifo queue for storing POD-types.
template <typename T>
struct PodQueue {
    PodQueue() = default;

    [[nodiscard]] bool empty() const { return qFront == size32(vec); }
    [[nodiscard]] auto size() const -> uint32_t { return size32(vec) - qFront; }
    [[nodiscard]] auto front() const -> const T& { return vec[qFront]; }
    [[nodiscard]] auto back() const -> const T& { return vec.back(); }

    auto front() -> T& { return vec[qFront]; }
    auto back() -> T& { return vec.back(); }
    void push(const T& x) { vec.push_back(x); }
    void pop() { ++qFront; }
    auto pop_ret() -> T { return vec[qFront++]; }
    void rewind() { qFront = 0; }
    void clear() {
        vec.clear();
        qFront = 0;
    }
    PodVector_t<T> vec;       // the underlying vector holding the items
    uint32_t       qFront{0}; // front position
};

} // namespace Clasp
