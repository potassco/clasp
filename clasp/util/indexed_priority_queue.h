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
namespace Detail {
template <std::integral T>
constexpr auto heap_parent(T i) -> T {
    return (i - 1) >> 1;
}
template <std::integral T>
constexpr auto heap_left(T i) -> T {
    return (i << 1) + 1;
}
template <std::integral T>
constexpr auto heap_right(T i) -> T {
    return (i << 1) + 2;
}
template <std::integral T>
constexpr auto heap_last_non_leaf(T len) -> T {
    return (len - 2) >> 1;
}
} // namespace Detail
//! Indexed priority queue implemented as a binary heap.
/*!
 * Maintains a priority queue of unique unsigned integral keys, backed by
 * a binary heap and an auxiliary index map.
 *
 * The comparator defines priority: if `Cmp(a, b)` is true, then `a` has higher priority than `b`.
 * \note This differs from the semantics used by e.g. std::priority_queue!
 *
 * Supports O(log n) insertion, removal, and priority updates, as well as O(1) membership tests.
 *
 * \tparam T   Unsigned integral key type
 * \tparam Cmp Strict priority comparator (must induce a strict-weak-ordering)
 */
template <std::unsigned_integral T,
          typename Cmp // sort-predicate - if Cmp(n1, n2) == true, n1 has higher priority than n2
          >
class indexed_priority_queue { // NOLINT
public:
    using key_type             = T;                             // NOLINT
    using heap_type            = pod_vector<T>;                 // NOLINT
    using idx_type             = typename heap_type::size_type; // NOLINT
    using index_container_type = pod_vector<idx_type>;          // NOLINT
    using size_type            = idx_type;                      // NOLINT
    using compare_type         = Cmp;                           // NOLINT
    static_assert(sizeof(T) <= sizeof(idx_type));
    static constexpr idx_type no_pos = static_cast<idx_type>(-1);

    //! Constructs an empty priority queue.
    /*!
     * \param c Comparator used to establish priority.
     */
    explicit indexed_priority_queue(const compare_type& c = {}) noexcept : indices_(), heap_(), compare_(c) {}

    //! Returns the comparator used by the queue.
    auto key_compare() const -> const compare_type& { return compare_; }
    //! Returns whether the queue is empty.
    [[nodiscard]] bool empty() const { return heap_.empty(); }
    //! Returns the number of elements in the queue.
    [[nodiscard]] auto size() const -> size_type { return heap_.size(); }
    //! Returns the highest-priority key.
    /*!
     * \pre The queue is not empty.
     */
    [[nodiscard]] auto top() const -> key_type {
        assert(not empty());
        return heap_[0];
    }
    //! Returns whether the given key is currently contained in the queue.
    [[nodiscard]] bool contains(key_type k) const { return index(k) != no_pos; }
    //! Returns the position of the given key in the queue.
    [[nodiscard]] auto index(key_type k) const -> idx_type { return k < indices_.size() ? indices_[k] : no_pos; }

    //! Reserves internal storage for at least `n` keys.
    void reserve(size_type n) { indices_.reserve(n); }

    //! Inserts the given key into the queue.
    /*!
     * \pre The key is not already present.
     * \param k Key to insert.
     */
    void push(key_type k) {
        assert(not contains(k));
        if (k >= indices_.size()) {
            if (k >= indices_.capacity()) {
                indices_.reserve(((k + 1) * 3) >> 1);
            }
            indices_.resize(k + 1, no_pos);
        }
        indices_[k] = heap_.size();
        heap_.push_back(k);
        siftup(indices_[k]);
    }

    //! Remove the highest-priority key.
    /*!
     * @pre The queue is not empty.
     */
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

    //! Removes the given key from the queue.
    /*!
     * \param k Key to remove
     * \post not contains(k)
     */
    void remove(key_type k) {
        if (auto pos = index(k); pos != no_pos) {
            assign(pos, heap_.back());
            indices_[k] = no_pos;
            heap_.pop_back();
            if (pos < heap_.size()) {
                siftup(pos);
                siftdown(pos);
            }
        }
    }

    //! Removes all keys from the queue.
    /*!
     * \post empty()
     */
    void clear() {
        heap_.clear();
        indices_.clear();
    }

    //! Updates the position of the given key after a priority change.
    /*!
     * \note Inserts the given key if it is not present.
     * \param k Key to update
     * \post contains(k)
     */
    void update(key_type k) {
        if (not contains(k)) {
            push(k);
        }
        else {
            siftup(indices_[k]);
            siftdown(indices_[k]);
        }
    }
    //! Restores the heap order after increasing the priority of the given key.
    /*!
     * \pre The key is present in the queue
     */
    void increase(key_type k) {
        assert(contains(k));
        siftup(indices_[k]);
    }
    //! Restores the heap order after decreasing the priority of the given key.
    /*!
     * \pre The key is present in the queue
     */
    void decrease(key_type k) {
        assert(contains(k));
        siftdown(indices_[k]);
    }

private:
    void assign(idx_type pos, key_type val) {
        heap_[pos]    = val;
        indices_[val] = pos;
    }

    void siftup(idx_type n) {
        using namespace Detail;
        key_type x = heap_[n];
        idx_type p = heap_parent(n);
        while (n != 0 && compare_(x, heap_[p])) {
            assign(n, heap_[p]);
            n = p;
            p = heap_parent(n);
        }
        assign(n, x);
    }

    void siftdown(idx_type n) {
        using namespace Detail;
        key_type x = heap_[n];
        for (idx_type child, size = heap_.size(); (child = heap_left(n)) < size;) {
            if (child + 1 < size && compare_(heap_[child + 1], heap_[child])) {
                ++child;
            }
            if (not compare_(heap_[child], x)) {
                break;
            }
            assign(n, heap_[child]);
            n = child;
        }
        assign(n, x);
    }
    index_container_type indices_;
    heap_type            heap_;
    compare_type         compare_;
};
namespace Detail {
template <typename RandIter, typename T, typename Cmp>
constexpr void pushHeap(RandIter beg, std::ptrdiff_t tIdx, T value, std::ptrdiff_t hIdx, Cmp& cmp) {
    for (auto p = heap_parent(hIdx); hIdx > tIdx && cmp(*(beg + p), value); p = heap_parent(hIdx)) {
        *(beg + hIdx) = std::move(*(beg + p));
        hIdx          = p;
    }
    *(beg + hIdx) = std::move(value);
}
template <typename RandIter, typename T, typename Cmp>
constexpr void adjustHeap(RandIter beg, std::ptrdiff_t len, T value, std::ptrdiff_t hIdx, Cmp& cmp) {
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
constexpr void pushHeap(RandIter beg, RandIter end, Cmp&& cmp) {
    assert(beg < end);
    Detail::pushHeap(beg, 0, std::move(*(end - 1)), (end - beg) - 1, cmp);
}
template <typename Cont, typename Cmp>
constexpr void pushHeap(Cont&& c, Cmp&& cmp) {
    pushHeap(c.begin(), c.end(), std::forward<Cmp>(cmp));
}

//! Removes the first (i.e. root) element from the max heap [beg, end).
/*!
 * \pre The range [beg, end) is a valid non-empty max heap.
 * \post The max heap after the removal will be [beg, end - 1) and *(end-1) will contain the removed element.
 */
template <typename RandIter, typename Cmp>
constexpr void popHeap(RandIter beg, RandIter end, Cmp&& cmp) {
    assert(beg < end);
    if (auto len = end - beg; len > 1) {
        --end;
        --len;
        auto value = std::move(*end);
        *end       = std::move(*beg);
        Detail::adjustHeap(beg, len, std::move(value), 0, cmp);
    }
}
template <typename Cont, typename Cmp>
constexpr void popHeap(Cont&& c, Cmp&& cmp) {
    popHeap(c.begin(), c.end(), std::forward<Cmp>(cmp));
}

//! Removes and returns the root element of the max heap [beg, end) and inserts the given value.
/*!
 * This function behaves like a combination of popHeap followed by pushHeap, but is more efficient.
 * \return The old root element.
 */
template <typename RandIter, typename T, typename Cmp>
constexpr T replaceHeap(RandIter beg, RandIter end, T value, Cmp&& cmp) {
    assert(beg < end);
    auto old = std::move(*beg);
    Detail::adjustHeap(beg, end - beg, std::move(value), 0, cmp);
    return old;
}
template <typename Cont, typename T, typename Cmp>
constexpr auto replaceHeap(Cont&& c, T&& value, Cmp&& cmp) -> std::remove_cvref_t<T> {
    return replaceHeap(c.begin(), c.end(), std::forward<T>(value), std::forward<Cmp>(cmp));
}
//! Turns the range [beg, end) into a max heap.
template <typename RandIter, typename Cmp>
constexpr void makeHeap(RandIter beg, RandIter end, Cmp&& cmp) {
    if (const auto len = end - beg; len > 1) {
        for (auto p = Detail::heap_last_non_leaf(len);; --p) {
            Detail::adjustHeap(beg, len, std::move(*(beg + p)), p, cmp);
            if (p == 0) {
                return;
            }
        }
    }
}
template <typename Cont, typename Cmp>
constexpr void makeHeap(Cont&& c, Cmp&& cmp) {
    return makeHeap(c.begin(), c.end(), std::forward<Cmp>(cmp));
}

//! Sorts the max heap given in [beg, end) with respect to the given comparator.
/*!
 * \note The sorted range no longer maintains the heap property.
 */
template <typename RandIter, typename Cmp>
constexpr void sortHeap(RandIter beg, RandIter end, Cmp&& cmp) {
    for (auto len = end - beg; len-- > 1;) {
        --end;
        auto value = std::move(*end);
        *end       = std::move(*beg);
        Detail::adjustHeap(beg, len, std::move(value), 0, cmp);
    }
}
template <typename Cont, typename Cmp>
constexpr void sortHeap(Cont&& c, Cmp&& cmp) {
    sortHeap(c.begin(), c.end(), std::forward<Cmp>(cmp));
}

} // namespace bk_lib
