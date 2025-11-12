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

#include "pod_vector.h"

namespace bk_lib { // NOLINT

// Note: Uses a Max-Heap!
template <std::unsigned_integral T,
          typename Cmp // sort-predicate - if Cmp(n1, n2) == true, n1 has higher priority than n2
          >
class indexed_priority_queue { // NOLINT
public:
    using key_type             = T;
    using heap_type            = pod_vector<T>;
    using idx_type             = typename heap_type::size_type;
    using index_container_type = pod_vector<idx_type>;
    using size_type            = idx_type;
    using compare_type         = Cmp;
    static_assert(sizeof(T) <= sizeof(idx_type));

    explicit indexed_priority_queue(const compare_type& c = {}) noexcept : indices_(), heap_(), compare_(c) {}

    const compare_type& key_compare() const { return compare_; }

    [[nodiscard]] bool empty() const { return heap_.empty(); }
    void               reserve(size_type n) { indices_.reserve(n); }

    void push(key_type k) {
        assert(not is_in_queue(k));
        if (k >= max_pos(indices_)) {
            if (k >= indices_.capacity()) {
                indices_.reserve(((k + 1) * 3) >> 1);
            }
            indices_.resize(k + 1, no_pos);
        }
        indices_[k] = max_pos(heap_);
        heap_.push_back(k);
        siftup(indices_[k]);
    }

    void pop() {
        assert(not empty());
        key_type x         = heap_[0];
        heap_[0]           = heap_.back();
        indices_[heap_[0]] = 0;
        indices_[x]        = no_pos;
        heap_.pop_back();
        if (heap_.size() > 1) {
            siftdown(0);
        }
    }

    void clear() {
        heap_.clear();
        indices_.clear();
    }

    [[nodiscard]] size_type size() const { return heap_.size(); }

    [[nodiscard]] key_type top() const {
        assert(not empty());
        return heap_[0];
    }

    void update(key_type k) {
        if (not is_in_queue(k)) {
            push(k);
        }
        else {
            siftup(indices_[k]);
            siftdown(indices_[k]);
        }
    }
    // call if priority of k has increased
    void increase(key_type k) {
        assert(is_in_queue(k));
        siftup(indices_[k]);
    }
    // call if priority of k has decreased
    void decrease(key_type k) {
        assert(is_in_queue(k));
        siftdown(indices_[k]);
    }

    [[nodiscard]] bool is_in_queue(key_type k) const { return k < max_pos(indices_) && indices_[k] != no_pos; }

    void remove(key_type k) {
        if (is_in_queue(k)) {
            idx_type kInHeap       = indices_[k];
            heap_[kInHeap]         = heap_.back();
            indices_[heap_.back()] = kInHeap;
            heap_.pop_back();
            indices_[k] = no_pos;
            if (heap_.size() > 1 && kInHeap != max_pos(heap_)) {
                siftup(kInHeap);
                siftdown(kInHeap);
            }
        }
    }

private:
    static constexpr idx_type no_pos = static_cast<idx_type>(-1);
    template <typename C>
    static constexpr idx_type max_pos(const C& c) {
        return static_cast<idx_type>(c.size());
    }
    static constexpr idx_type heap_parent(idx_type i) { return (i - 1) >> 1; }
    static constexpr idx_type heap_left(idx_type i) { return (i << 1) + 1; }
    static constexpr idx_type heap_right(idx_type i) { return (i + 1) << 1; }

    void siftup(idx_type n) {
        using namespace detail;
        key_type x = heap_[n];
        idx_type p = heap_parent(n);
        while (n != 0 && compare_(x, heap_[p])) {
            heap_[n]           = heap_[p];
            indices_[heap_[n]] = n;
            n                  = p;
            p                  = heap_parent(n);
        }
        heap_[n]    = x;
        indices_[x] = n;
    }

    void siftdown(idx_type n) {
        using namespace detail;
        key_type x = heap_[n];
        while (heap_left(n) < max_pos(heap_)) {
            idx_type child = smaller_child(n);
            if (not compare_(heap_[child], x)) {
                break;
            }
            heap_[n]           = heap_[child];
            indices_[heap_[n]] = n;
            n                  = child;
        }
        heap_[n]    = x;
        indices_[x] = n;
    }

    [[nodiscard]] idx_type smaller_child(idx_type n) const {
        using namespace detail;
        return heap_right(n) < max_pos(heap_) && compare_(heap_[heap_right(n)], heap_[heap_left(n)]) ? heap_right(n)
                                                                                                     : heap_left(n);
    }
    index_container_type indices_;
    heap_type            heap_;
    compare_type         compare_;
};
namespace Detail {
constexpr std::ptrdiff_t heap_parent(std::ptrdiff_t i) { return (i - 1) >> 1; }
constexpr std::ptrdiff_t heap_left(std::ptrdiff_t i) { return (i << 1) + 1; }
constexpr std::ptrdiff_t heap_right(std::ptrdiff_t i) { return (i + 1) << 1; }
constexpr std::ptrdiff_t heap_last_non_leaf(std::ptrdiff_t len) { return (len - 2) >> 1; }
template <typename RandIter, typename T, typename Cmp>
constexpr void pushHeap(RandIter beg, std::ptrdiff_t tIdx, T value, std::ptrdiff_t hIdx, const Cmp& cmp) {
    for (auto p = heap_parent(hIdx); hIdx > tIdx && cmp(*(beg + p), value); p = heap_parent(hIdx)) {
        *(beg + hIdx) = std::move(*(beg + p));
        hIdx          = p;
    }
    *(beg + hIdx) = std::move(value);
}
template <typename RandIter, typename T, typename Cmp>
constexpr void adjustHeap(RandIter beg, std::ptrdiff_t len, T value, std::ptrdiff_t hIdx, const Cmp& cmp) {
    const auto tIdx = hIdx;
    auto       cIdx = hIdx;
    while (cIdx < heap_parent(len)) {
        cIdx = heap_right(cIdx);
        if (cmp(*(beg + cIdx), *(beg + (cIdx - 1)))) {
            --cIdx;
        }
        *(beg + hIdx) = std::move(*(beg + cIdx));
        hIdx          = cIdx;
    }
    if ((len & 1) == 0 && cIdx == heap_last_non_leaf(len)) {
        cIdx          = heap_right(cIdx) - 1;
        *(beg + hIdx) = std::move(*(beg + cIdx));
        hIdx          = cIdx;
    }
    pushHeap(beg, tIdx, std::move(value), hIdx, cmp);
}
} // namespace Detail

// Standalone max heap functions similar to the ones in <algorithm>

//! Inserts the element at the position end - 1 into the max heap [beg, end - 1).
/*!
 * \pre The range [beg, end - 1) is a valid max heap.
 * \post The max heap after the insertion will be [beg, end).
 */
template <typename RandIter, typename Cmp>
constexpr void pushHeap(RandIter beg, RandIter end, const Cmp& cmp) {
    assert(beg < end);
    Detail::pushHeap(beg, 0, std::move(*(end - 1)), (end - beg) - 1, cmp);
}

//! Removes the first (i.e. root) element from the max heap [beg, end).
/*!
 * \pre The range [beg, end) is a valid non-empty max heap.
 * \post The max heap after the removal will be [beg, end - 1) and *(end-1) will contain the removed element.
 */
template <typename RandIter, typename Cmp>
constexpr void popHeap(RandIter beg, RandIter end, const Cmp& cmp) {
    assert(beg < end);
    if (auto len = end - beg; len > 1) {
        --end;
        --len;
        auto value = std::move(*end);
        *end       = std::move(*beg);
        Detail::adjustHeap(beg, len, std::move(value), 0, cmp);
    }
}
//! Removes and returns the root element of the max heap [beg, end) and inserts the given value.
/*!
 * This function behaves like a combination of popHeap followed by pushHeap, but is more efficient.
 * \return The old root element.
 */
template <typename RandIter, typename T, typename Cmp>
constexpr T replaceHeap(RandIter beg, RandIter end, T value, const Cmp& cmp) {
    assert(beg < end);
    auto old = std::move(*beg);
    Detail::adjustHeap(beg, end - beg, std::move(value), 0, cmp);
    return old;
}
//! Turns the range [beg, end) into a max heap.
template <typename RandIter, typename Cmp>
constexpr void makeHeap(RandIter beg, RandIter end, const Cmp& cmp) {
    if (const auto len = end - beg; len > 1) {
        for (auto p = Detail::heap_last_non_leaf(len);; --p) {
            Detail::adjustHeap(beg, len, std::move(*(beg + p)), p, cmp);
            if (p == 0) {
                return;
            }
        }
    }
}

} // namespace bk_lib
