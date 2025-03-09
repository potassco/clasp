//
// Copyright (c) 2010-present Benjamin Kaufmann
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
#ifdef _MSC_VER
#pragma warning(push)
#pragma warning(disable : 4200)
#endif
#if defined(__GNUC__) && __GNUC__ >= 8
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wclass-memaccess"
#endif

#include <cassert>
#include <cstring>
#include <iterator>
#include <ranges>

namespace bk_lib { // NOLINT
namespace detail { // NOLINT

// base class for left_right_sequence
// see below
template <typename L, typename R>
class left_right_rep { // NOLINT
public:
    using left_type            = L;
    using right_type           = R;
    using size_type            = unsigned int;
    using left_iterator        = L*;
    using const_left_iterator  = const L*;
    using right_iterator       = std::reverse_iterator<R*>;
    using const_right_iterator = std::reverse_iterator<const R*>;
    using left_view_type       = std::span<const L>;
    using right_view_type      = std::ranges::reverse_view<std::span<const R>>;
    using max_type             = std::conditional_t<sizeof(left_type) >= sizeof(right_type), left_type, right_type>;
    using align_type           = std::conditional_t<alignof(left_type) >= alignof(right_type), left_type, right_type>;
    static_assert(sizeof(left_type) >= alignof(left_type) && sizeof(right_type) >= alignof(right_type));
    static constexpr auto block_size = static_cast<size_type>(
        ((sizeof(max_type) + (sizeof(align_type) - 1)) / sizeof(align_type)) * sizeof(align_type));

    left_right_rep() = default;
    [[nodiscard]] bool      empty() const { return left_ == 0 && right_ == cap_; }
    [[nodiscard]] size_type size() const { return left_size() + right_size(); }

    [[nodiscard]] size_type      left_size() const { return left_ / sizeof(left_type); }
    [[nodiscard]] size_type      left_capacity() const { return (cap_ / sizeof(left_type)); }
    const_left_iterator          left_begin() const { return ptr<const left_type>(begin()); }
    const_left_iterator          left_end() const { return ptr<const left_type>(buf_ + left_); }
    left_iterator                left_begin() { return ptr<left_type>(begin()); }
    left_iterator                left_end() { return ptr<left_type>(buf_ + left_); }
    [[nodiscard]] left_view_type left_view() const { return {left_begin(), left_size()}; }
    const left_type&             left(size_type i) const { return *(left_begin() + i); }
    left_type&                   left(size_type i) { return *(left_begin() + i); }

    [[nodiscard]] size_type right_size() const { return (cap_ - right_) / sizeof(right_type); }
    [[nodiscard]] size_type right_capacity() const { return (cap_ / sizeof(right_type)); }
    const_right_iterator    right_begin() const { return const_right_iterator(ptr<const right_type>(end())); }
    const_right_iterator    right_end() const { return const_right_iterator(ptr<const right_type>(buf_ + right_)); }
    right_iterator          right_begin() { return right_iterator(ptr<right_type>(end())); }
    right_iterator          right_end() { return right_iterator(ptr<right_type>(buf_ + right_)); }
    [[nodiscard]] right_view_type right_view() const {
        return std::views::reverse(std::span(ptr<const right_type>(buf_ + right_), right_size()));
    }

    void push_left(const left_type& x) {
        if ((left_ + sizeof(left_type)) > right_) {
            realloc();
        }
        new (buf_ + left_) left_type(x);
        left_ += sizeof(left_type);
    }

    void push_right(const right_type& x) {
        if ((left_ + sizeof(right_type)) > right_) {
            realloc();
        }
        right_ -= sizeof(right_type);
        new (right()) right_type(x);
    }
    void pop_left() {
        assert(left_size() != 0);
        left_ -= sizeof(left_type);
    }
    void pop_right() {
        assert(right_size() != 0);
        right_ += sizeof(right_type);
    }

    void erase_left(left_iterator it) {
        if (it != left_end()) {
            left_iterator x = it++;
            std::memmove(x, it, static_cast<std::size_t>(left_end() - it) * sizeof(left_type));
            left_ -= sizeof(left_type);
        }
    }
    void erase_left_unordered(left_iterator it) {
        if (auto ep = left_end(); it != ep) {
            *it = *--ep;
            pop_left();
        }
    }
    void erase_right(right_iterator it) {
        if (it != right_end()) {
            right_type* r = (++it).base();
            auto*       b = ptr<right_type>(right());
            assert(r >= b);
            std::memmove(b + 1, b, static_cast<std::size_t>(r - b) * sizeof(right_type));
            right_ += sizeof(right_type);
        }
    }
    void erase_right_unordered(right_iterator it) {
        if (it != right_end()) {
            *it     = *ptr<right_type>(right());
            right_ += sizeof(right_type);
        }
    }
    void shrink_left(left_iterator it) { left_ = static_cast<size_type>(it - left_begin()) * sizeof(left_type); }
    void shrink_right(right_iterator it) {
        auto* x = ptr<buf_type>(it.base());
        right_  = static_cast<size_type>(x - begin());
    }

protected:
    template <typename X, typename B>
    static X* ptr(B* p) {
        return reinterpret_cast<X*>(p);
    }

    using buf_type = unsigned char;
    void init_buffer(buf_type* b, size_type c, bool own) {
        buf_   = b;
        cap_   = c;
        free_  = own;
        left_  = 0;
        right_ = cap_;
    }
    ~left_right_rep() { release(); }

    void assign(const left_right_rep& other) {
        if (auto os = other.raw_size(); os > cap_) {
            auto  c = ((os + (block_size - 1)) / block_size) * block_size;
            auto* b = static_cast<buf_type*>(::operator new(c * sizeof(buf_type)));
            release();
            init_buffer(b, c, true);
        }
        left_  = other.left_;
        right_ = this->cap_ - (other.right_size() * sizeof(right_type));
        if (other.buf_) {
            std::memcpy(begin(), other.begin(), other.left_size() * sizeof(left_type));
            std::memcpy(right(), const_cast<left_right_rep&>(other).right(), other.right_size() * sizeof(right_type));
        }
    }
    void move(left_right_rep&& other) {
        init_buffer(other.buf_, other.cap_, other.free_);
        left_  = other.left_;
        right_ = other.right_;
    }

    buf_type*                     begin() { return buf_; }
    [[nodiscard]] const buf_type* begin() const { return buf_; }
    buf_type*                     end() { return buf_ + cap_; }
    [[nodiscard]] const buf_type* end() const { return buf_ + cap_; }
    buf_type*                     right() { return buf_ + right_; }
    [[nodiscard]] size_type       capacity() const { return cap_ / block_size; }
    [[nodiscard]] size_type       raw_size() const { return left_ + (cap_ - right_); }
    void                          release() {
        if (free_ != 0) {
            ::operator delete(buf_);
            free_ = 0;
        }
    }
    void      realloc();
    buf_type* buf_;
    size_type cap_  : 31;
    size_type free_ : 1;
    size_type left_;
    size_type right_;
};

template <typename L, typename R>
void left_right_rep<L, R>::realloc() {
    size_type new_cap = ((capacity() * 3) >> 1) * block_size;
    size_type min_cap = 4 * block_size;
    if (new_cap < min_cap) {
        new_cap = min_cap;
    }
    auto*     temp = static_cast<buf_type*>(::operator new(new_cap * sizeof(buf_type)));
    size_type r    = cap_ - right_;
    if (this->buf_) {
        // copy left
        std::memcpy(temp, begin(), left_size() * sizeof(L));
        // copy right
        std::memcpy(temp + (new_cap - r), right(), right_size() * sizeof(R));
    }
    // swap
    release();
    buf_   = temp;
    cap_   = new_cap;
    free_  = 1;
    right_ = new_cap - r;
}

template <typename L, typename R, unsigned Cap>
struct left_right_buffer; // NOLINT

// always store sequence in heap-allocated buffer
template <typename L, typename R>
struct left_right_buffer<L, R, 0> : public left_right_rep<L, R> {
    static constexpr unsigned inline_raw_cap = 0;
    void                      init() { this->init_buffer(nullptr, 0u, false); }
};

// store small sequences directly inside of object
template <typename L, typename R, unsigned Cap>
struct left_right_buffer : public left_right_rep<L, R> { // NOLINT
    static constexpr unsigned inline_raw_cap = Cap;
    using buf_type                           = typename left_right_rep<L, R>::buf_type;
    using align_type                         = typename left_right_rep<L, R>::align_type;

    void init() { this->init_buffer(mem, Cap, false); }

    void try_shrink() {
        if (this->raw_size() <= Cap && this->buf_ != mem) {
            left_right_buffer t;
            t.move(static_cast<left_right_rep<L, R>&&>(*this));
            this->init();
            this->assign(t);
        }
    }

    alignas(align_type) buf_type mem[Cap];
};

// compute inline capacity for left_right_sequence based on parameter i
template <typename L, typename R, unsigned I>
static consteval unsigned compute_raw_cap() {
    constexpr auto bs = left_right_rep<L, R>::block_size;
    constexpr auto ms = sizeof(left_right_buffer<L, R, bs>);
    if constexpr (ms > I) {
        return 0;
    }
    else {
        constexpr auto c = (((I - ms) / bs) + 1) * bs;
        static_assert(sizeof(left_right_buffer<L, R, c>) <= I || c >= bs * 2);
        return sizeof(left_right_buffer<L, R, c>) <= I ? c : c - bs;
    }
}
template <typename L, typename R, unsigned I>
using left_right_buffer_t = left_right_buffer<L, R, compute_raw_cap<L, R, I>()>;

} // namespace detail

//! Stores two sequences in one contiguous memory block
/*!
 * The left sequence grows from left to right, while the
 * right sequence grows from right to left. On overlap, the
 * memory block is automatically extended.
 *
 * \param L value type of left sequence
 * \param R value type of right sequence
 * \param I max size on stack
 * \pre L and R can be copied with memcpy (i.e. have trivial copy constructor and trivial destructor)
 */
template <typename L, typename R, unsigned I>
class left_right_sequence : public bk_lib::detail::left_right_buffer_t<L, R, I> { // NOLINT
public:
    using base_type            = bk_lib::detail::left_right_buffer_t<L, R, I>;
    using left_type            = typename base_type::left_type;
    using right_type           = typename base_type::right_type;
    using size_type            = typename base_type::size_type;
    using align_type           = typename base_type::align_type;
    using max_type             = typename base_type::max_type;
    using buf_type             = typename base_type::buf_type;
    using left_iterator        = typename base_type::left_iterator;
    using const_left_iterator  = typename base_type::const_left_iterator;
    using right_iterator       = typename base_type::right_iterator;
    using const_right_iterator = typename base_type::const_right_iterator;

    left_right_sequence() { base_type::init(); }
    left_right_sequence(const left_right_sequence& other) {
        base_type::init();
        base_type::assign(other);
    }
    left_right_sequence(left_right_sequence&& other) noexcept { this->move_or_copy(std::move(other)); }
    left_right_sequence& operator=(const left_right_sequence& other) {
        if (this != &other) {
            base_type::assign(other);
        }
        return *this;
    }
    left_right_sequence& operator=(left_right_sequence&& other) noexcept {
        if (this != &other) {
            base_type::release();
            this->move_or_copy(std::move(other));
        }
        return *this;
    }
    ~left_right_sequence() = default;

    void clear() {
        this->left_  = 0;
        this->right_ = this->cap_;
    }

    void reset() {
        base_type::release();
        base_type::init();
    }

private:
    void move_or_copy(left_right_sequence&& other) noexcept {
        if (other.raw_size() > base_type::inline_raw_cap) {
            base_type::move(std::move(other));
        }
        else {
            this->init();
            this->assign(other);
            other.release();
        }
        other.init();
    }
};

} // namespace bk_lib

#ifdef _MSC_VER
#pragma warning(pop)
#endif
#if defined(__GNUC__) && __GNUC__ >= 8
#pragma GCC diagnostic pop
#endif
