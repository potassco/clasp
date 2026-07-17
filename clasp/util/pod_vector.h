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
                case 1: new (out++) T(*first++); assert(first <= last);
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
struct Memcpy {
    template <typename U>
    explicit Memcpy(const U* ptr) : first(ptr)
                                  , valSize(sizeof(U)) {}
    void operator()(void* out, std::size_t n) const { not out || std::memcpy(out, first, n * valSize); }

    const void* first;
    std::size_t valSize;
};
template <typename SrcIt, typename T>
static consteval auto canMemCpy() -> bool {
    if constexpr (not std::contiguous_iterator<SrcIt>) {
        return false;
    }
    else {
        using ValT = std::remove_cvref_t<decltype(*std::declval<SrcIt>())>;
        using PtrT = decltype(&*std::declval<SrcIt>());
        return std::is_constructible_v<const T*, PtrT> ||
               (sizeof(T) == sizeof(ValT) && std::integral<T> && std::integral<ValT>);
    }
}
static_assert(canMemCpy<int*, int>());
static_assert(canMemCpy<const int*, int>());
static_assert(canMemCpy<unsigned*, int>());
static_assert(canMemCpy<const unsigned*, int>());
static_assert(not canMemCpy<double*, int>());
static_assert(canMemCpy<std::initializer_list<int>::iterator, int>());

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
    //! Constructs an empty pod_vector.
    /*!
     * \post size() == capacity() == 0
     */
    pod_vector() : ebo_(0, allocator_type()) {}

    //! Constructs an empty pod_vector that uses a copy of a for memory allocations.
    /*!
     * \post size() == capacity() == 0
     */
    explicit pod_vector(const allocator_type& a) : ebo_(0, a) {}

    //! Constructs a pod_vector containing n copies of value.
    /*!
     * \post size() == n
     */
    explicit pod_vector(size_type n, const T& value = T(), const allocator_type& a = allocator_type()) : ebo_(n, a) {
        detail::fill(ebo_.buf, ebo_.buf + n, value);
        ebo_.size = n;
    }

    //! Constructs a pod_vector equal to the range [first, last).
    /*!
     * \post size() = distance between first and last.
     */
    template <std::input_iterator Iter>
    pod_vector(Iter first, Iter last, const allocator_type& a = allocator_type()) : ebo_(0, a) {
        append(first, last);
    }

    //! Construct a pod_vector from an initializer list.
    pod_vector(std::initializer_list<value_type> l, const allocator_type& a = allocator_type())
        : pod_vector(l.begin(), l.end(), a) {}

    //! Creates a copy of other.
    /*!
     * \post size() == other.size() && capacity() == other.size()
     */
    pod_vector(const pod_vector& other) : ebo_(other.size(), other.get_allocator()) {
        if (auto* buf = other.begin()) {
            std::memcpy(ebo_.buf, buf, other.size() * sizeof(T));
        }
        ebo_.size = other.size();
    }

    //! Steals the contents of other.
    pod_vector(pod_vector&& other) noexcept : ebo_(std::move(other.ebo_)) {}

    //! Replaces this pod_vector with a copy of other.
    auto operator=(const pod_vector& other) -> pod_vector& {
        if (this != &other) {
            assign(other.begin(), other.end());
        }
        return *this;
    }

    //! Replaces this pod_vector by stealing the elements of other.
    auto operator=(pod_vector&& other) noexcept -> pod_vector& {
        pod_vector(std::move(other)).swap(*this);
        return *this;
    }

    //! Assigns the elements from l to this pod_vector.
    auto operator=(std::initializer_list<value_type> l) -> pod_vector& {
        assign(l.begin(), l.end());
        return *this;
    }

    //! Frees all memory allocated by this pod_vector.
    /*!
     * \note Won't call any destructors, because PODs don't have those.
     */
    ~pod_vector() = default;

    /** @name inspectors
     * inspector-functions
     */
    //@{

    //! Returns the number of elements currently stored in this pod_vector.
    auto size() const -> size_type { return ebo_.size; }
    //! Returns the size of the largest possible pod_vector.
    auto max_size() const -> size_type {
        typename allocator_type::size_type x = get_allocator().max_size();
        std::size_t                        y = size_type(-1) / sizeof(T);
        return static_cast<size_type>(std::min(static_cast<std::size_t>(x), y));
    }
    //! Returns the total number of elements this pod_vector can hold without requiring reallocation.
    auto capacity() const -> size_type { return ebo_.cap; }
    //! Returns size() == 0
    [[nodiscard]] bool empty() const { return ebo_.size == 0; }

    auto data() const -> const_pointer { return ebo_.buf; }
    auto data() -> pointer { return ebo_.buf; }

    auto begin() const -> const_iterator { return ebo_.buf; }
    auto end() const -> const_iterator { return ebo_.buf + ebo_.size; }
    auto rbegin() const -> const_reverse_iterator { return const_reverse_iterator(end()); }
    auto rend() const -> const_reverse_iterator { return const_reverse_iterator(begin()); }

    auto begin() -> iterator { return ebo_.buf; }
    auto end() -> iterator { return ebo_.buf + ebo_.size; }
    auto rbegin() -> reverse_iterator { return reverse_iterator(end()); }
    auto rend() -> reverse_iterator { return reverse_iterator(begin()); }

    //! Returns a copy of the allocator used by this pod_vector
    auto get_allocator() const -> allocator_type { return ebo_; }

    //@}
    /** @name elemacc
     * element access
     */
    //@{

    //! Returns a reference to the element at position n.
    /*!
     * \pre n < size()
     */
    auto operator[](size_type n) -> reference {
        assert(n < size());
        return ebo_.buf[n];
    }

    //! Returns a reference-to-const to the element at position n.
    /*!
     * \pre n < size()
     */
    auto operator[](size_type n) const -> const_reference {
        assert(n < size());
        return ebo_.buf[n];
    }

    //! Same as operator[] but throws std::out_of_range if pre-condition is not met.
    auto at(size_type n) const -> const_reference {
        if (n < size()) {
            return ebo_.buf[n];
        }
        throw std::out_of_range("pod_vector::at");
    }
    //! Same as operator[] but throws std::out_of_range if pre-condition is not met.
    auto at(size_type n) -> reference {
        if (n < size()) {
            return ebo_.buf[n];
        }
        throw std::out_of_range("pod_vector::at");
    }

    //! Equivalent to *begin().
    auto front() -> reference {
        assert(not empty());
        return *ebo_.buf;
    }
    //! Equivalent to *begin().
    auto front() const -> const_reference {
        assert(not empty());
        return *ebo_.buf;
    }

    //! Equivalent to *--end().
    auto back() -> reference {
        assert(not empty());
        return ebo_.buf[ebo_.size - 1];
    }

    //! Equivalent to *--end().
    auto back() const -> const_reference {
        assert(not empty());
        return ebo_.buf[ebo_.size - 1];
    }

    //@}
    /** @name mutators
     * mutator functions
     */
    //@{

    //! Erases all elements in the range [begin(), end).
    /*!
     * \post size() == 0
     */
    void clear() { ebo_.size = 0; }

    //! Replaces the elements in this pod_vector with `n` copies of `val`.
    void assign(size_type n, const T& val) {
        clear();
        append(n, val);
    }

    //! Replaces the elements in this pod_vector with the elements from the given range.
    template <std::input_iterator Iter>
    void assign(Iter first, Iter last) {
        clear();
        append(first, last);
    }

    //! Replaces the elements in this pod_vector with the elements from the given initializer list.
    void assign(std::initializer_list<value_type> l) { assign(l.begin(), l.end()); }

    //! Erases the element pointed to by pos.
    /*!
     * \pre pos != end() && !empty()
     * \return An iterator pointing to the element following pos (before that element was erased)
     * of end() if no such element exists.
     *
     * \note Invalidates all iterators and references referring to elements after pos.
     */
    auto erase(iterator pos) -> iterator {
        assert(not empty() && pos != end());
        erase(pos, pos + 1);
        return pos;
    }

    //! Erases the elements in the range [first, last).
    /*!
     * \pre [first, last) must be a valid range.
     */
    auto erase(iterator first, iterator last) -> iterator {
        if (end() - last > 0) {
            std::memmove(first, last, (end() - last) * sizeof(T));
        }
        ebo_.size -= static_cast<size_type>(last - first);
        return first;
    }

    //! Adjusts the size of this pod_vector to ns.
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

    //! Reallocates storage if necessary but never changes the size() of this pod_vector.
    /*!
     * \note If n is <= capacity() reserve is a noop. Otherwise, a reallocation takes place
     * and capacity() >= n after reserve returned.
     * \note Reallocation invalidates all references, pointers and iterators referring to
     * elements in this pod_vector.
     *
     * \note When reallocation occurs elements are copied from the old storage using memcpy.
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

    //! Equivalent to insert(end(), x);
    void push_back(const T& x) {
        if (size() < capacity()) {
            new ((ebo_.buf + ebo_.size++)) T(x);
        }
        else {
            append_realloc(1, x);
        }
    }
    template <typename... Args>
    void emplace_back(Args&&... args) {
        if (size() == capacity()) {
            reserve(grow_size(1u));
        }
        new ((ebo_.buf + ebo_.size++)) T(std::forward<Args>(args)...);
    }
    //! Equivalent to erase(--end());
    /*!
     * \pre !empty()
     */
    void pop_back() {
        assert(not empty());
        --ebo_.size;
    }

    //! Inserts a copy of val before pos.
    /*!
     * \pre pos is a valid iterator.
     * \return An iterator pointing to the copy of val that was inserted.
     * \note If size() + 1 > capacity() reallocation occurs. Otherwise, iterators and
     * references referring to elements before pos remain valid.
     *
     */
    auto insert(iterator pos, const T& val) -> iterator { return insert(pos, static_cast<size_type>(1), val); }

    //! Inserts n copies of val before pos.
    /*!
     * \pre pos is a valid iterator.
     */
    auto insert(iterator pos, size_type n, const T& val) -> iterator {
        auto off = static_cast<size_type>(pos - begin());
        insert_impl(pos, n, [&val](T* first, std::size_t num) { detail::fill(first, first + num, val); });
        return ebo_.buf + off;
    }

    //! Inserts copies of elements in the range [first, last) before pos.
    /*!
     * \pre first and last are not iterators into this pod_vector.
     * \pre pos is a valid iterator.
     * \note If first and last are pointers, memcpy is used to insert the elements
     * in the range [first, last) into this container.
     *
     */
    template <std::input_iterator Iter>
    void insert(iterator pos, Iter first, Iter last) {
        insert_range(pos, first, last);
    }

    auto insert(const_iterator pos, std::initializer_list<value_type> l) -> iterator {
        return insert(pos, l.begin(), l.end());
    }

    //! Reduces excess capacity.
    void shrink_to_fit() {
        if (capacity() > size()) {
            pod_vector(*this).swap(*this);
        }
    }

    /** @name nonstd
     * Non-standard interface
     */
    //@{

    //! Appends `n` copies of val to this vector.
    void append(size_type n, const T& val) {
        if (size() + n <= capacity()) {
            detail::fill(end(), end() + n, val);
            ebo_.size += n;
        }
        else {
            append_realloc(n, val);
        }
    }

    //! Appends copies of elements in the range [first, last).
    /*!
     * \pre first and last are not iterators into this pod_vector.
     */
    template <std::input_iterator It>
    void append(It first, It last) {
        if constexpr (std::forward_iterator<It>) {
            auto n = check_size(first, last);
            if (n == 0) {
                return;
            }
            if (size() + n > capacity()) {
                reserve(grow_size(n));
            }
            make_copy_op(first, last)(end(), n);
            ebo_.size += n;
        }
        else {
            while (first != last) { push_back(*first++); }
        }
    }
    //! Removes the last `n` elements from this vector.
    /*!
     * \pre n <= size()
     */
    void pop(size_type n) {
        assert(n <= size());
        ebo_.size -= n;
    }
    //! Discards the contents this vector and restores it to its default-constructed state.
    void reset() { ebo_.reset(); }
    //@}
private:
    template <std::forward_iterator It>
    constexpr auto make_copy_op(It first, It last) const
        -> std::conditional_t<detail::canMemCpy<It, T>(), detail::Memcpy, detail::Copy<It>> {
        if constexpr (detail::canMemCpy<It, T>()) {
            if constexpr (std::is_constructible_v<const T*, It>) {
                assert((first < begin() || first >= end()) && "pod_vec::insert(): Precondition violated!");
            }
            return detail::Memcpy{&*first};
        }
        else {
            return detail::Copy<It>(first, last);
        }
    }
    template <typename It>
    auto check_size(It first, It last) const -> size_type {
        typename allocator_type::difference_type diff = std::distance(first, last);
        assert(diff == 0 || (static_cast<size_type>(size() + diff) > size() && "pod_vector: max size exceeded!"));
        return static_cast<size_type>(diff);
    }
    auto grow_size(size_type n) -> size_type {
        size_type nc = size() + n;
        assert(nc > size() && "pod_vector: max size exceeded!");
        assert(nc > capacity());
        if (nc < 4) {
            nc = 1 << (nc + 1);
        }
        size_type x = (capacity() * 3) >> 1;
        if (nc < x) {
            nc = x;
        }
        return nc;
    }
    void append_realloc(size_type n, const T& x) {
        size_type nc   = grow_size(n);
        pointer   temp = ebo_.allocate(nc);
        not ebo_.buf || std::memcpy(temp, ebo_.buf, size() * sizeof(T));
        detail::fill(temp + size(), temp + size() + n, x);
        ebo_.release();
        ebo_.buf   = temp;
        ebo_.cap   = nc;
        ebo_.size += n;
    }
    void move_right(iterator pos, size_type n) {
        assert((pos || n == 0) && (ebo_.eos() - pos) >= static_cast<difference_type>(n));
        not pos || std::memmove(pos + n, pos, (end() - pos) * sizeof(T));
    }

    template <std::forward_iterator It>
    void insert_range(iterator pos, It first, It last) {
        insert_impl(pos, check_size(first, last), make_copy_op(first, last));
    }

    template <std::input_iterator It>
    void insert_range(iterator pos, It first, It last) {
        pod_vector<T> temp;
        while (first != last) { temp.push_back(*first++); }
        insert_impl(pos, temp.size(), detail::Memcpy{temp.begin()});
    }

    template <typename P>
    void insert_impl(iterator pos, size_type n, const P& pred) {
        assert(n == 0 || (size() + n) > size());
        if (size() + n <= capacity()) {
            move_right(pos, n);
            pred(pos, n);
            ebo_.size += n;
        }
        else {
            size_type nc     = grow_size(n);
            pointer   temp   = ebo_.allocate(nc);
            auto      prefix = static_cast<size_type>(pos - begin());
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
            ebo_.cap   = nc;
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
        void reset() {
            release();
            buf  = nullptr;
            size = 0u;
            cap  = 0u;
        }
        T* eos() const { return buf + cap; }
    } ebo_;
};

template <typename T, typename A>
inline auto operator==(const pod_vector<T, A>& lhs,
                       const pod_vector<T, A>& rhs) -> decltype(lhs.front() == rhs.front()) {
    return lhs.size() == rhs.size() && std::equal(lhs.begin(), lhs.end(), rhs.begin());
}
template <typename T, typename A>
inline auto operator<=>(const pod_vector<T, A>& lhs,
                        const pod_vector<T, A>& rhs) -> decltype(lhs.front() <=> rhs.front()) {
    return std::lexicographical_compare_three_way(lhs.begin(), lhs.end(), rhs.begin(), rhs.end());
}

template <typename T, typename A>
inline void swap(pod_vector<T, A>& lhs, pod_vector<T, A>& rhs) noexcept {
    lhs.swap(rhs);
}

template <typename T, typename Alloc, typename Pred>
constexpr auto erase_if(pod_vector<T, Alloc>& c, Pred pred) -> typename pod_vector<T, Alloc>::size_type {
    auto sz = c.size();
    c.erase(std::remove_if(c.begin(), c.end(), pred), c.end());
    return sz - c.size();
}
template <typename T, typename Alloc>
constexpr auto erase(pod_vector<T, Alloc>& c, const T& v) -> typename pod_vector<T, Alloc>::size_type {
    auto sz = c.size();
    c.erase(std::remove(c.begin(), c.end(), v), c.end());
    return sz - c.size();
}

} // namespace bk_lib
