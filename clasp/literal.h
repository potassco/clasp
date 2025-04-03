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

#include <clasp/pod_vector.h>

#include <potassco/enum.h>

#include <utility> // std::swap

/*!
 * \file
 * \brief Types and functions related to literals and variables.
 */
namespace Clasp {
/*!
 * \addtogroup constraint
 */
//@{

//! A variable is an integer in the range [0;var_max).
using Var_t = uint32_t;

//! var_max is not a valid variable, i.e. currently Clasp supports at most 2^30 variables.
constexpr auto var_max = static_cast<Var_t>(1) << 30;

//! The variable 0 has a special meaning in the solver.
constexpr auto sent_var = static_cast<Var_t>(0);

//! Possible types of a variable.
enum class VarType : uint32_t { atom = 1u, body = 2u, hybrid = atom | body };
POTASSCO_ENABLE_CMP_OPS(VarType);

//! A literal is a variable or its negation.
/*!
 * \par Implementation:
 * A literal's state is stored in a single 32-bit integer as follows:
 *  - 30-bits   : variable id
 *  - 1-bit     : sign, 1 if negative, 0 if positive
 *  - 1-bit     : general purpose flag for marking a literal instance
 */
class Literal {
public:
    //! The default constructor creates the positive literal of the special sentinel var.
    constexpr Literal() : rep_(sent_var) {}
    //! Creates a literal of the variable var with sign s.
    /*!
     * \param var  The literal's variable.
     * \param sign true if new literal should be negative.
     * \pre var < var_max
     */
    constexpr Literal(Var_t var, bool sign) : rep_((var << sign_mask) + (static_cast<uint32_t>(sign) << flag_mask)) {
        assert(var < var_max);
    }

    //! Returns the variable of the literal.
    [[nodiscard]] constexpr Var_t var() const noexcept { return rep_ >> sign_mask; }

    //! Returns the sign of the literal.
    /*!
     * \return true if the literal is negative. Otherwise, false.
     */
    [[nodiscard]] constexpr bool sign() const noexcept { return (rep_ & sign_mask) != 0; }

    //! Returns var and sign encoded in a unique id.
    /*!
     * \note The watch-flag is ignored and thus the id of a literal can be stored in 31-bits.
     */
    [[nodiscard]] constexpr uint32_t id() const noexcept { return rep_ >> flag_mask; }

    //! Returns the stored representation of this literal.
    constexpr uint32_t&              rep() noexcept { return rep_; }
    [[nodiscard]] constexpr uint32_t rep() const noexcept { return rep_; }

    //! Creates a literal from an id.
    static constexpr Literal fromId(uint32_t id) {
        assert(id <= id_max);
        return Literal{id << flag_mask};
    }
    //! Creates a literal from an unsigned integer.
    static constexpr Literal fromRep(uint32_t rep) { return Literal{rep}; }

    constexpr void swap(Literal& other) noexcept { std::swap(rep_, other.rep_); }

    //! Sets the watched-flag of this literal.
    constexpr Literal& flag() {
        rep_ |= flag_mask;
        return *this;
    }

    //! Clears the watched-flag of this literal.
    constexpr Literal& unflag() {
        rep_ &= ~flag_mask;
        return *this;
    }

    //! Returns true if the watched-flag of this literal is set.
    [[nodiscard]] constexpr bool flagged() const noexcept { return (rep_ & flag_mask) != 0; }

    //! Returns the complimentary literal of this literal.
    /*!
     *  The complementary Literal of a Literal is a Literal referring to the
     *  same variable but with inverted sign.
     */
    constexpr Literal operator~() const noexcept { return Literal{(rep_ & ~flag_mask) ^ sign_mask}; }

    friend constexpr auto operator==(Literal lhs, Literal rhs) { return lhs.id() == rhs.id(); }
    friend constexpr auto operator<=>(Literal lhs, Literal rhs) { return lhs.id() <=> rhs.id(); }

private:
    static constexpr uint32_t sign_mask = 2u;
    static constexpr uint32_t flag_mask = 1u;
    static constexpr uint32_t id_max    = (1u << 31) - 1;
    constexpr explicit Literal(uint32_t rep) : rep_(rep) {}
    uint32_t rep_;
};
constexpr Literal operator^(Literal lhs, bool sign) { return Literal::fromId(lhs.id() ^ static_cast<uint32_t>(sign)); }
constexpr Literal operator^(bool sign, Literal rhs) { return rhs ^ sign; }
constexpr void    swap(Literal& l, Literal& r) noexcept { l.swap(r); }
//! Creates the negative literal of variable v.
constexpr Literal negLit(Var_t v) { return {v, true}; }
//! Creates the positive literal of variable v.
constexpr Literal posLit(Var_t v) { return {v, false}; }
//! Returns negLit(abs(p)) if p < 0 and posLit(p) otherwise.
constexpr Literal toLit(int32_t p) { return p < 0 ? negLit(static_cast<Var_t>(-p)) : posLit(static_cast<Var_t>(p)); }
//! Converts the given (non-sentinel) literal to a signed integer s.th. p == toLit(toInt(p)).
constexpr int32_t toInt(Literal p) { return p.sign() ? -static_cast<int32_t>(p.var()) : static_cast<int32_t>(p.var()); }
//! Always-true literal.
constexpr auto lit_true = posLit(sent_var);
//! Always-false literal.
constexpr auto lit_false = negLit(sent_var);
static_assert(lit_true == ~lit_false);
static_assert(lit_true != lit_false);
static_assert(lit_true < lit_false);
static_assert(lit_false > lit_true);
static_assert(posLit(1) < negLit(1));
static_assert(negLit(1) < posLit(2));
static_assert((lit_true ^ true) == lit_false);
static_assert((lit_true ^ false) == lit_true);
static_assert(not(~Literal{12, false}.flag()).flagged());
//! Returns true if p represents the special variable 0
constexpr bool isSentinel(Literal p) { return p.var() == sent_var; }
static_assert(isSentinel(lit_true) && isSentinel(lit_false));
// Low-level conversion between Literals and int literals.
// We cannot use toInt() here because it is not defined for the
// sentinel literals lit_true and lit_false.
constexpr int32_t encodeLit(Literal x) {
    return not x.sign() ? static_cast<int32_t>(x.var() + 1) : -static_cast<int32_t>(x.var() + 1);
}
constexpr Var_t   decodeVar(int32_t x) { return static_cast<Var_t>(x >= 0 ? x : -x) - 1; }
constexpr Literal decodeLit(int32_t x) { return {decodeVar(x), x < 0}; }
static_assert(decodeLit(encodeLit(lit_true)) == lit_true);
static_assert(decodeLit(encodeLit(negLit(2))) == negLit(2));
constexpr unsigned hashId(unsigned key) {
    key  = ~key + (key << 15);
    key ^= (key >> 11);
    key += (key << 3);
    key ^= (key >> 5);
    key += (key << 10);
    key ^= (key >> 16);
    return key;
}
constexpr uint32_t hashLit(Literal p) { return hashId(p.id()); }
static_assert(hashLit(lit_true) != hashLit(lit_false));

//! A signed integer type used to represent weights.
using Weight_t = int32_t;
//! A signed integer type used to represent sums of weights.
using Wsum_t = int64_t;

constexpr Weight_t weight_min     = INT32_MIN;
constexpr Weight_t weight_max     = INT32_MAX;
constexpr Wsum_t   weight_sum_min = INT64_MIN;
constexpr Wsum_t   weight_sum_max = INT64_MAX;

//!< A literal associated with a weight.
struct WeightLiteral {
    Literal  lit;
    Weight_t weight = 1;

    friend constexpr bool operator==(WeightLiteral lhs, WeightLiteral rhs)  = default;
    friend constexpr auto operator<=>(WeightLiteral lhs, WeightLiteral rhs) = default;
};
static_assert(std::is_trivially_copyable_v<WeightLiteral>);
template <typename T>
using SpanView      = std::span<const T>;
using VarVec        = PodVector_t<Var_t>;         //!< A vector of variables.
using VarView       = SpanView<Var_t>;            //!< A read-only view of variables.
using LitVec        = PodVector_t<Literal>;       //!< A vector of literals.
using LitView       = SpanView<Literal>;          //!< A read-only view of literals.
using WeightVec     = PodVector_t<Weight_t>;      //!< A vector of weights.
using WeightView    = SpanView<Weight_t>;         //!< A read-only view of weights.
using SumVec        = PodVector_t<Wsum_t>;        //!< A vector of sums of weights.
using SumView       = SpanView<Wsum_t>;           //!< A read-only view of sums of weights.
using WeightLitVec  = PodVector_t<WeightLiteral>; //!< A vector of weight-literals.
using WeightLitView = SpanView<WeightLiteral>;    //!< A read-only view of weight-literals.
///////////////////////////////////////////////////////////////////////////////
// Truth values
///////////////////////////////////////////////////////////////////////////////
using Val_t                 = uint8_t; //!< Type of the three value-literals.
using ValueVec              = PodVector_t<Val_t>;
using ValueView             = SpanView<Val_t>;
constexpr Val_t value_free  = 0; //!< Value used for variables that are unassigned.
constexpr Val_t value_true  = 1; //!< Value used for variables that are true.
constexpr Val_t value_false = 2; //!< Value used for variables that are false.

//! Returns the value that makes the literal `lit` true.
/*!
 * \param lit The literal for which the true-value should be determined.
 * \return
 *   - value_true  iff lit is a positive literal, or
 *   - value_false iff lit is a negative literal.
 *   .
 */
constexpr Val_t trueValue(Literal lit) { return 1u + lit.sign(); }
static_assert(trueValue(lit_true) == value_true);
static_assert(trueValue(lit_false) == value_false);

//! Returns the value that makes the literal `lit` false.
/*!
 * \param lit The literal for which the false-value should be determined.
 * \return
 *   - value_false iff lit is a positive literal, or
 *   - value_true  iff lit is a negative literal.
 *   .
 */
constexpr Val_t falseValue(Literal lit) { return 2u - lit.sign(); }
static_assert(falseValue(lit_true) == value_false);
static_assert(falseValue(lit_false) == value_true);

//! Returns the sign that matches the value.
/*!
 * \return
 *   - false iff v == value_true
 *   - true  otherwise
 */
constexpr bool valSign(Val_t v) { return v != value_true; }

template <typename Os>
constexpr Os& operator<<(Os& os, Literal lit) {
    return os << toInt(lit);
}
template <typename Os>
constexpr Os& operator<<(Os& os, WeightLiteral lit) {
    return os << "(" << lit.lit << ", " << lit.weight << ")";
}

//@}
} // namespace Clasp
