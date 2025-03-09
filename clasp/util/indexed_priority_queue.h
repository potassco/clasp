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

} // namespace bk_lib
