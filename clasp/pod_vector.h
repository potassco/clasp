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
#include <vector>

namespace Clasp {

#if CLASP_USE_STD_VECTOR
template <class Type>
struct PodVector {
    using type = std::vector<Type>;
    static void destruct(type& t) { t.clear(); }
};
using std::erase;
using std::erase_if;
#else
//! Type selector for a vector type optimized for storing POD-types.
template <typename Type>
struct PodVector {
    using type = bk_lib::pod_vector<Type>;
    static void destruct(type& t) {
        std::destroy(t.begin(), t.end());
        t.clear();
    }
};
#endif
template <typename T>
using PodVector_t = typename PodVector<T>::type;

constexpr uint32_t toU32(std::size_t x) {
    assert(std::in_range<uint32_t>(x));
    return static_cast<uint32_t>(x);
}
template <typename T>
POTASSCO_ATTR_INLINE constexpr uint32_t size32(const T& c) {
    if constexpr (std::is_same_v<decltype(c.size()), uint32_t>) {
        return c.size();
    }
    else {
        return toU32(c.size());
    }
}
template <typename T>
inline void discardVec(T& t) {
    T().swap(t);
}

template <typename T>
inline void shrinkVecTo(T& t, typename T::size_type j) {
    t.erase(t.begin() + static_cast<typename T::difference_type>(j), t.end());
}

template <typename T>
inline void growVecTo(T& vec, typename T::size_type j, const typename T::value_type& val = typename T::value_type()) {
    if (vec.size() < j) {
        if (vec.capacity() < j) {
            vec.reserve(j + j / 2);
        }
        vec.resize(j, val);
    }
}

template <typename T>
void moveDown(T& t, typename T::size_type from, typename T::size_type to) {
    for (typename T::size_type end = t.size(); from != end;) { t[to++] = t[from++]; }
    shrinkVecTo(t, to);
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

//! A simple vector-based fifo queue for storing POD-types.
template <typename T>
struct PodQueue {
    using vec_type  = PodVector_t<T>;
    using size_type = typename vec_type::size_type;
    PodQueue() : qFront(0) {}
    [[nodiscard]] bool empty() const { return qFront == vec.size(); }
    size_type          size() const { return vec.size() - qFront; }
    const T&           front() const { return vec[qFront]; }
    const T&           back() const { return vec.back(); }
    T&                 front() { return vec[qFront]; }
    T&                 back() { return vec.back(); }
    void               push(const T& x) { vec.push_back(x); }
    void               pop() { ++qFront; }
    T                  pop_ret() { return vec[qFront++]; }
    void               clear() {
        vec.clear();
        qFront = 0;
    }
    void      rewind() { qFront = 0; }
    vec_type  vec;    // the underlying vector holding the items
    size_type qFront; // front position
};

} // namespace Clasp
