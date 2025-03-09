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

#include <algorithm>
#include <cassert>
#include <cstring>
#include <initializer_list>
#include <iterator>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>

#if defined(__GNUC__)
#pragma GCC system_header
#endif

namespace bk_lib {
namespace detail {
template <typename T>
void fill(T* first, T* last, const T& x) {
    assert(first <= last);
    switch ((last - first) & 7u) {
        default:
            while (first != last) {
                new (first++) T(x);
                case 7: new (first++) T(x); [[fallthrough]];
                case 6: new (first++) T(x); [[fallthrough]];
                case 5: new (first++) T(x); [[fallthrough]];
                case 4: new (first++) T(x); [[fallthrough]];
                case 3: new (first++) T(x); [[fallthrough]];
                case 2: new (first++) T(x); [[fallthrough]];
                case 1: new (first++) T(x); assert(first <= last);
            }
    }
}
template <typename Iter, typename T>
void copy(Iter first, Iter last, std::size_t s, T* out) {
    switch (s & 7u) {
        default:
            while (first != last) {
                new (out++) T(*first++);
                case 7: new (out++) T(*first++); [[fallthrough]];
                case 6: new (out++) T(*first++); [[fallthrough]];
                case 5: new (out++) T(*first++); [[fallthrough]];
                case 4: new (out++) T(*first++); [[fallthrough]];
                case 3: new (out++) T(*first++); [[fallthrough]];
                case 2: new (out++) T(*first++); [[fallthrough]];
                case 1: new (out++) T(*first++); [[fallthrough]];
            }
    }
}

template <typename Iter>
struct Copy {
    Copy(Iter b, Iter e) : first(b), last(e) {}
    template <typename T>
    void operator()(T* out, std::size_t n) const {
        detail::copy(first, last, n, out);
    }
    Iter first;
    Iter last;
};
template <typename T>
struct Memcpy {
    Memcpy(const T* b) : first(b) {}
    void     operator()(T* out, std::size_t n) const { not out || std::memcpy(out, first, n * sizeof(T)); }
    const T* first;
};

} // namespace detail

//! A std::vector-replacement for POD-Types.
/*!
 * \pre T is a POD-Type
 * \see https://en.cppreference.com/w/cpp/named_req/PODType for a description of POD-Types.
 * \note Does not call any destructors and uses std::memcpy to copy/move elements
 * \note On LP64-machines size and capacity are represented as unsigned integers (instead of e.g. std::size_t)
 */
template <typename T, typename Allocator = std::allocator<T>>
class pod_vector {
public:
    // NOLINTBEGIN
    // types:
    using this_type              = pod_vector<T, Allocator>; // not standard
    using alloc_traits           = std::allocator_traits<Allocator>;
    using allocator_type         = Allocator;
    using reference              = T&;
    using const_reference        = const T&;
    using iterator               = typename alloc_traits::pointer;
    using const_iterator         = typename alloc_traits::const_pointer;
    using pointer                = typename alloc_traits::pointer;
    using const_pointer          = typename alloc_traits::const_pointer;
    using reverse_iterator       = std::reverse_iterator<iterator>;
    using const_reverse_iterator = std::reverse_iterator<const_iterator>;
    using value_type             = T;
    using size_type              = std::conditional_t<sizeof(typename Allocator::size_type) < sizeof(unsigned int),
                                                      typename Allocator::size_type, unsigned int>;
    using difference_type        = std::conditional_t<sizeof(typename Allocator::difference_type) < sizeof(int),
                                                      typename Allocator::difference_type, int>;
    // NOLINTEND

    // ctors
    //! constructs an empty pod_vector.
    /*!
     * \post size() == capacity() == 0
     */
    pod_vector() : ebo_(0, allocator_type()) {}

    //! constructs an empty pod_vector that uses a copy of a for memory allocations.
    /*!
     * \post size() == capacity() == 0
     */
    explicit pod_vector(const allocator_type& a) : ebo_(0, a) {}

    //! constructs a pod_vector containing n copies of value.
    /*!
     * \post size() == n
     */
    explicit pod_vector(size_type n, const T& value = T(), const allocator_type& a = allocator_type()) : ebo_(n, a) {
        detail::fill(ebo_.buf, ebo_.buf + n, value);
        ebo_.size = n;
    }

    //! constructs a pod_vector equal to the range [first, last).
    /*!
     * \post size() = distance between first and last.
     */
    template <std::input_iterator Iter>
    pod_vector(Iter first, Iter last, const allocator_type& a = allocator_type()) : ebo_(0, a) {
        insert_range(end(), first, last);
    }

    //! construct a pod_vector from an initializer list.
    pod_vector(std::initializer_list<value_type> l, const allocator_type& a = allocator_type())
        : pod_vector(l.begin(), l.end(), a) {}

    //! creates a copy of other
    /*!
     * \post size() == other.size() && capacity() == other.size()
     */
    pod_vector(const pod_vector& other) : ebo_(other.size(), other.get_allocator()) {
        if (auto* buf = other.begin()) {
            std::memcpy(ebo_.buf, buf, other.size() * sizeof(T));
        }
        ebo_.size = other.size();
    }

    pod_vector(pod_vector&& other) noexcept : ebo_(std::move(other.ebo_)) {}

    pod_vector& operator=(const pod_vector& other) {
        if (this != &other) {
            assign(other.begin(), other.end());
        }
        return *this;
    }

    pod_vector& operator=(pod_vector&& other) noexcept {
        pod_vector(std::move(other)).swap(*this);
        return *this;
    }

    pod_vector& operator=(std::initializer_list<value_type> l) {
        assign(l.begin(), l.end());
        return *this;
    }

    //! frees all memory allocated by this pod_vector.
    /*!
     * \note Won't call any destructors, because PODs don't have those.
     */
    ~pod_vector() = default;

    /** @name inspectors
     * inspector-functions
     */
    //@{

    //! returns the number of elements currently stored in this pod_vector.
    size_type size() const { return ebo_.size; }
    //! size of the largest possible pod_vector
    size_type max_size() const {
        typename allocator_type::size_type x = get_allocator().max_size();
        std::size_t                        y = size_type(-1) / sizeof(T);
        return static_cast<size_type>(std::min(static_cast<std::size_t>(x), y));
    }
    //! returns the total number of elements this pod_vector can hold without requiring reallocation.
    size_type capacity() const { return ebo_.cap; }
    //! returns size() == 0
    [[nodiscard]] bool empty() const { return ebo_.size == 0; }

    const_pointer data() const { return ebo_.buf; }
    pointer       data() { return ebo_.buf; }

    const_iterator         begin() const { return ebo_.buf; }
    const_iterator         end() const { return ebo_.buf + ebo_.size; }
    const_reverse_iterator rbegin() const { return const_reverse_iterator(end()); }
    const_reverse_iterator rend() const { return const_reverse_iterator(begin()); }

    iterator         begin() { return ebo_.buf; }
    iterator         end() { return ebo_.buf + ebo_.size; }
    reverse_iterator rbegin() { return reverse_iterator(end()); }
    reverse_iterator rend() { return reverse_iterator(begin()); }

    //! returns a copy of the allocator used by this pod_vector
    allocator_type get_allocator() const { return ebo_; }

    //@}
    /** @name elemacc
     * element access
     */
    //@{

    //! returns a reference to the element at position n
    /*!
     * \pre n < size()
     */
    reference operator[](size_type n) {
        assert(n < size());
        return ebo_.buf[n];
    }

    //! returns a reference-to-const to the element at position n
    /*!
     * \pre n < size()
     */
    const_reference operator[](size_type n) const {
        assert(n < size());
        return ebo_.buf[n];
    }

    //! same as operator[] but throws std::out_of_range if pre-condition is not met.
    const_reference at(size_type n) const {
        if (n < size()) {
            return ebo_.buf[n];
        }
        throw std::out_of_range("pod_vector::at");
    }
    //! same as operator[] but throws std::out_of_range if pre-condition is not met.
    reference at(size_type n) {
        if (n < size()) {
            return ebo_.buf[n];
        }
        throw std::out_of_range("pod_vector::at");
    }

    //! equivalent to *begin()
    reference front() {
        assert(not empty());
        return *ebo_.buf;
    }
    //! equivalent to *begin()
    const_reference front() const {
        assert(not empty());
        return *ebo_.buf;
    }

    //! equivalent to *--end()
    reference back() {
        assert(not empty());
        return ebo_.buf[ebo_.size - 1];
    }

    //! equivalent to *--end()
    const_reference back() const {
        assert(not empty());
        return ebo_.buf[ebo_.size - 1];
    }

    //@}
    /** @name mutators
     * mutator functions
     */
    //@{

    //! erases all elements in the range [begin(), end)
    /*!
     * \post size() == 0
     */
    void clear() { ebo_.size = 0; }

    void assign(size_type n, const T& val) {
        clear();
        insert(end(), n, val);
    }

    template <typename Iter>
    void assign(Iter first, Iter last) {
        clear();
        insert(end(), first, last);
    }

    void assign(std::initializer_list<value_type> l) { assign(l.begin(), l.end()); }

    //! erases the element pointed to by pos.
    /*!
     * \pre pos != end() && !empty()
     * \return an iterator pointing to the element following pos (before that element was erased)
     * of end() if no such element exists.
     *
     * \note invalidates all iterators and references referring to elements after pos.
     */
    iterator erase(iterator pos) {
        assert(not empty() && pos != end());
        erase(pos, pos + 1);
        return pos;
    }

    //! erases the elements in the range [first, last)
    /*!
     * \pre [first, last) must be a valid range.
     */
    iterator erase(iterator first, iterator last) {
        if (end() - last > 0) {
            std::memmove(first, last, (end() - last) * sizeof(T));
        }
        ebo_.size -= static_cast<size_type>(last - first);
        return first;
    }

    //! adjusts the size of this pod_vector to ns.
    /*!
     * resize is equivalent to:
     * if ns > size insert(end(), ns - size(), val)
     * if ns < size erase(begin() + ns, end())
     *
     * \post size() == ns
     */
    void resize(size_type ns, const T& val = T()) {
        if (ns > size()) {
            ns <= capacity() ? detail::fill(end(), end() + (ns - size()), val) : append_realloc(ns - size(), val);
        }
        ebo_.size = ns;
    }

    //! reallocates storage if necessary but never changes the size() of this pod_vector.
    /*!
     * \note if n is <= capacity() reserve is a noop. Otherwise, a reallocation takes place
     * and capacity() >= n after reserve returned.
     * \note reallocation invalidates all references, pointers and iterators referring to
     * elements in this pod_vector.
     *
     * \note when reallocation occurs elements are copied from the old storage using memcpy.
     */
    void reserve(size_type n) {
        if (n > capacity()) {
            T* temp = ebo_.allocate(n);
            not ebo_.buf || std::memcpy(temp, ebo_.buf, size() * sizeof(T));
            ebo_.release();
            ebo_.buf = temp;
            ebo_.cap = n;
        }
    }

    void swap(pod_vector& other) noexcept {
        std::swap(ebo_.buf, other.ebo_.buf);
        std::swap(ebo_.size, other.ebo_.size);
        std::swap(ebo_.cap, other.ebo_.cap);
    }

    //! equivalent to insert(end(), x);
    void push_back(const T& x) {
        if (size() < capacity()) {
            new ((ebo_.buf + ebo_.size++)) T(x);
        }
        else {
            append_realloc(1, x);
        }
    }

    //! equivalent to erase(--end());
    /*!
     * \pre !empty()
     */
    void pop_back() {
        assert(not empty());
        --ebo_.size;
    }

    //! inserts a copy of val before pos.
    /*!
     * \pre pos is a valid iterator.
     * \return an iterator pointing to the copy of val that was inserted.
     * \note if size() + 1 > capacity() reallocation occurs. Otherwise, iterators and
     * references referring to elements before pos remain valid.
     *
     */
    iterator insert(iterator pos, const T& val) { return insert(pos, static_cast<size_type>(1), val); }

    //! inserts n copies of val before pos.
    /*!
     * \pre pos is a valid iterator.
     */
    iterator insert(iterator pos, size_type n, const T& val) {
        auto off = static_cast<size_type>(pos - begin());
        insert_impl(pos, n, [&val](T* first, std::size_t num) { detail::fill(first, first + num, val); });
        return ebo_.buf + off;
    }

    //! inserts copies of elements in the range [first, last) before pos.
    /*!
     * \pre first and last are not iterators into this pod_vector.
     * \pre pos is a valid iterator.
     * \note if first and last are pointers, memcpy is used to insert the elements
     * in the range [first, last) into this container.
     *
     */
    template <std::input_iterator Iter>
    void insert(iterator pos, Iter first, Iter last) {
        insert_range(pos, first, last);
    }

    iterator insert(const_iterator pos, std::initializer_list<value_type> l) { return insert(pos, l.begin(), l.end()); }

    /** @name nonstd
     * Non-standard interface
     */
    //@{

    //! adjusts the size of this pod_vector to ns.
    /*!
     * In contrast to pod_vector::resize this function does not
     * initialize new elements in case ns > size().
     * This reflects the behaviour of built-in arrays of pod-types.
     * \note
     *  Any access to an uninitialized element is illegal unless it is accessed
     *  in order to assign a new value.
     */
    void resize_no_init(size_type ns) {
        reserve(ns);
        ebo_.size = ns;
    }
    //@}
private:
    size_type grow_size(size_type n) {
        size_type new_cap = size() + n;
        assert(new_cap > size() && "pod_vector: max size exceeded!");
        assert(new_cap > capacity());
        if (new_cap < 4) {
            new_cap = 1 << (new_cap + 1);
        }
        size_type x = (capacity() * 3) >> 1;
        if (new_cap < x) {
            new_cap = x;
        }
        return new_cap;
    }
    void append_realloc(size_type n, const T& x) {
        size_type new_cap = grow_size(n);
        pointer   temp    = ebo_.allocate(new_cap);
        not ebo_.buf || std::memcpy(temp, ebo_.buf, size() * sizeof(T));
        detail::fill(temp + size(), temp + size() + n, x);
        ebo_.release();
        ebo_.buf   = temp;
        ebo_.cap   = new_cap;
        ebo_.size += n;
    }
    void move_right(iterator pos, size_type n) {
        assert((pos || n == 0) && (ebo_.eos() - pos) >= static_cast<difference_type>(n));
        not pos || std::memmove(pos + n, pos, (end() - pos) * sizeof(T));
    }

    template <std::contiguous_iterator It>
    void insert_range(iterator pos, It first, It last) {
        typename allocator_type::difference_type diff = std::distance(first, last);
        assert(diff == 0 || (static_cast<size_type>(size() + diff) > size() && "pod_vector: max size exceeded!"));
        if (diff == 0) {
            return;
        }
        if constexpr (std::is_same_v<pointer, It> || std::is_same_v<const_pointer, It>) {
            assert((first < begin() || first >= end()) && "pod_vec::insert(): Precondition violated!");
            insert_impl(pos, static_cast<size_type>(diff), detail::Memcpy<T>(first));
        }
        else if constexpr (std::is_constructible_v<const T*, decltype(&*first)>) {
            insert_impl(pos, static_cast<size_type>(diff), detail::Memcpy<T>(&*first));
        }
        else {
            insert_impl(pos, static_cast<size_type>(diff), detail::Copy<It>(first, last));
        }
    }

    template <std::forward_iterator It>
    void insert_range(iterator pos, It first, It last) {
        typename allocator_type::difference_type diff = std::distance(first, last);
        assert(diff == 0 || (static_cast<size_type>(size() + diff) > size() && "pod_vector: max size exceeded!"));
        insert_impl(pos, static_cast<size_type>(diff), detail::Copy<It>(first, last));
    }

    template <std::input_iterator It>
    void insert_range(iterator pos, It first, It last) {
        pod_vector<T> temp;
        while (first != last) { temp.push_back(*first++); }
        insert(pos, temp.begin(), temp.end());
    }

    // NOTE: template parameter ST should always equal size_type
    // and is only needed to work around an internal compiler error
    // in gcc 3.4.3
    template <typename ST, typename P>
    void insert_impl(iterator pos, ST n, const P& pred) {
        assert(n == 0 || (size() + n) > size());
        if (size() + n <= capacity()) {
            move_right(pos, n);
            pred(pos, n);
            ebo_.size += n;
        }
        else {
            size_type new_cap = grow_size(n);
            pointer   temp    = ebo_.allocate(new_cap);
            auto      prefix  = static_cast<size_type>(pos - begin());
            if (pos) {
                // copy prefix
                std::memcpy(temp, begin(), prefix * sizeof(T));
                // insert new stuff
                pred(temp + prefix, n);
                // copy suffix
                std::memcpy(temp + prefix + n, pos, (end() - pos) * sizeof(T));
            }
            else {
                assert(not begin() && not prefix);
                // insert new stuff
                pred(temp, n);
            }
            ebo_.release();
            ebo_.buf   = temp;
            ebo_.size += n;
            ebo_.cap   = new_cap;
        }
    }
    struct ebo : public Allocator { // empty-base-optimization
        using size_type = typename this_type::size_type;
        using A         = typename this_type::allocator_type;
        pointer   buf;  // pointer to array
        size_type size; // current size (used elements)
        size_type cap;  // max size before regrow
        ebo(size_type n, const Allocator& a) : Allocator(a), buf(0), size(0), cap(n) {
            if (n > 0) {
                buf = A::allocate(n);
            }
        }
        ebo(ebo&& other) noexcept
            : Allocator(static_cast<Allocator&&>(other))
            , buf(std::exchange(other.buf, nullptr))
            , size(std::exchange(other.size, 0))
            , cap(std::exchange(other.cap, 0)) {}
        ~ebo() { release(); }
        void release() {
            if (buf) {
                A::deallocate(buf, cap);
            }
        }
        T* eos() const { return buf + cap; }
    } ebo_;
};

template <typename T, typename A>
inline bool operator==(const pod_vector<T, A>& lhs, const pod_vector<T, A>& rhs) {
    return lhs.size() == rhs.size() && std::equal(lhs.begin(), lhs.end(), rhs.begin());
}

template <typename T, typename A>
inline bool operator!=(const pod_vector<T, A>& lhs, const pod_vector<T, A>& rhs) {
    return !(lhs == rhs);
}

template <typename T, typename A>
inline bool operator<(const pod_vector<T, A>& lhs, const pod_vector<T, A>& rhs) {
    return std::lexicographical_compare(lhs.begin(), lhs.end(), rhs.begin(), rhs.end());
}

template <typename T, typename A>
inline bool operator>(const pod_vector<T, A>& lhs, const pod_vector<T, A>& rhs) {
    return rhs < lhs;
}

template <typename T, typename A>
inline bool operator<=(const pod_vector<T, A>& lhs, const pod_vector<T, A>& rhs) {
    return !(rhs < lhs);
}

template <typename T, typename A>
inline bool operator>=(const pod_vector<T, A>& lhs, const pod_vector<T, A>& rhs) {
    return !(lhs < rhs);
}

template <typename T, typename A>
inline void swap(pod_vector<T, A>& lhs, pod_vector<T, A>& rhs) noexcept {
    lhs.swap(rhs);
}

template <typename T, typename Alloc, typename Pred>
constexpr typename pod_vector<T, Alloc>::size_type erase_if(pod_vector<T, Alloc>& c, Pred pred) {
    auto sz = c.size();
    c.erase(std::remove_if(c.begin(), c.end(), pred), c.end());
    return sz - c.size();
}
template <typename T, typename Alloc>
constexpr typename pod_vector<T, Alloc>::size_type erase(pod_vector<T, Alloc>& c, const T& v) {
    auto sz = c.size();
    c.erase(std::remove(c.begin(), c.end(), v), c.end());
    return sz - c.size();
}

} // namespace bk_lib
