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

#include <clasp/constraint.h>

namespace Clasp {

//! Primitive representation of weight constraint literals in normal form.
struct WeightLitsRep {
    //! Transforms the given literals to the normal form expected by WeightConstraint.
    /*!
     * The function simplifies lits and bound by removing assigned and
     * merging duplicate/complementary literals. Furthermore, negative weights and
     * their literals are inverted, bound is updated accordingly, and literals
     * are sorted by decreasing weight.
     */
    static WeightLitsRep create(Solver& s, WeightLitVec& lits, Weight_t bound);
    //! Propagates the constraint con == *this.
    /*!
     * If *this is always satisfied (bound <= 0) or unsatisfied (bound > reach),
     * the function forward propagates con. Otherwise, if con is not free, it assigns
     * (and removes) literals from *this that must hold.
     */
    bool               propagate(Solver& s, Literal con);
    [[nodiscard]] bool sat() const { return bound <= 0; }
    [[nodiscard]] bool unsat() const { return reach < bound; }
    [[nodiscard]] bool open() const { return bound > 0 && bound <= reach; }
    [[nodiscard]] bool hasWeights() const { return size && lits[0].weight > 1; }
    [[nodiscard]] auto literals() const -> WeightLitView { return std::span{lits, size}; }
    WeightLiteral*     lits;  /*!< Literals sorted by decreasing weight. */
    uint32_t           size;  /*!< Number of literals in lits.  */
    Weight_t           bound; /*!< Rhs of linear constraint.    */
    Weight_t           reach; /*!< Sum of weights of lits.      */
};

//! Class implementing smodels-like cardinality- and weight constraints.
/*!
 * \ingroup constraint
 * This class represents a constraint of type W == w1*x1 ... wn*xn >= B,
 * where W and each xi are literals and B and each wi are strictly positive integers.
 *
 * The class is used to represent smodels-like weight constraint, i.e.
 * the body of a basic weight rule. In this case W is the literal associated with the body.
 * A cardinality constraint is handled like a weight constraint where all weights are equal to 1.
 *
 * Given a WeightConstraint with bound @c B and set of literals @c L,
 * - let @c sumTrue be the sum of the weights of all literals @c l in @c L that are currently true,
 * - @c sumReach be the sum of the weights of all literals @c l in @c L that are currently not false, and
 * - @c U be the set of literals @c l in @c L that are currently unassigned
 * .
 * the class implements the following <b>four inference rules</b>:
 * - @c FTB: If @c sumTrue >= @c B: assign @c W to true.
 * - @c BFB: If @c W is false: set false all literals @c l in @c U for which @c sumTrue + @c weight(l) >= @c B.
 * - @c FFB: If @c sumReach < @c B: assign @c W to false.
 * - @c BTB: If @c W is true: set true all literals @c l in @c U for which @c sumReach - @c weight(l) < @c B.
 *
 */
class WeightConstraint : public Constraint {
public:
    //! Flags controlling weight constraint creation.
    enum CreateFlag : uint32_t {
        create_explicit  = 1u,   //!< Force creation of explicit constraint even if size/bound is small.
        create_no_add    = 2u,   //!< Do not add constraint to solver db (implies create_explicit).
        create_sat       = 4u,   //!< Force creation even if constraint is always satisfied.
        create_no_freeze = 8u,   //!< Do not freeze variables in constraint.
        create_no_share  = 16u,  //!< Do not allow sharing of literals between threads.
        create_eq_bound  = 32u,  //!< Create equality instead of greater-or-equal constraint.
        create_only_btb  = 64u,  //!< Only create ffb_btb constraint.
        create_only_bfb  = 128u, //!< Only create ftb_bfb constraint.
    };
    POTASSCO_ENABLE_BIT_OPS(CreateFlag, friend);
    //! Type used to communicate result of create().
    class CPair {
    public:
        constexpr CPair() = default;
        [[nodiscard]] bool ok() const {
            return con_[0] != reinterpret_cast<WeightConstraint*>(0x1) &&
                   con_[1] != reinterpret_cast<WeightConstraint*>(0x1);
        }
        [[nodiscard]] WeightConstraint* first() const { return con_[0]; }
        [[nodiscard]] WeightConstraint* second() const { return con_[1]; }

    private:
        friend class WeightConstraint;
        WeightConstraint* con_[2] = {nullptr, nullptr};
    };
    //! Creates a new weight constraint from the given weight literals.
    /*!
     * If the right hand side of the weight constraint is initially true/false (FTB/FFB),
     * W is assigned appropriately but no constraint is created. Otherwise,
     * the new weight constraint is added to s unless creationFlags contains create_no_add.
     *
     * \param s Solver in which the new constraint is to be used.
     * \param con The literal that is associated with the constraint.
     * \param lits The literals of the weight constraint.
     * \param bound The lower bound of the weight constraint.
     * \param creationFlags Set of creation flags to apply.
     * \note Cardinality constraint are represented as weight constraints with all weights equal to 1.
     * \note If creationFlags contains @c create_eq_bound, a constraint W == (lits == bound) is created that is
     *       represented by up to two weight constraints.
     */
    static CPair create(Solver& s, Literal con, WeightLitVec& lits, Weight_t bound, CreateFlag creationFlags = {});

    //! Low level creation function.
    /*!
     * \note flag @c create_eq_bound is ignored by this function, that is, this function always creates
     *       a single >= constraint.
     */
    static CPair create(Solver& s, Literal con, WeightLitsRep& rep, CreateFlag flags);
    // constraint interface
    Constraint*            cloneAttach(Solver&) override;
    bool                   simplify(Solver& s, bool = false) override;
    void                   destroy(Solver*, bool) override;
    PropResult             propagate(Solver& s, Literal p, uint32_t& data) override;
    void                   reason(Solver&, Literal p, LitVec& lits) override;
    bool                   minimize(Solver& s, Literal p, CCMinRecursive* r) override;
    void                   undoLevel(Solver& s) override;
    [[nodiscard]] uint32_t estimateComplexity(const Solver& s) const override;
    /*!
     * Logically, we distinguish two constraints:
     * - ffb_btb for handling forward false body and backward true body and
     * - ftb_bfb for handling forward true body and backward false body.
     * .
     * Physically, we store the literals in one array: ~W=1, l0=w0,...,ln-1=wn-1.
     */
    enum ActiveConstraint : uint32_t {
        ffb_btb = 0, //!< (@c SumW - @c B)+1 [~W=1, l0=w0,..., ln-1=wn-1]
        ftb_bfb = 1, //!< @c B [ W=1,~l0=w0,...,~ln-1=wn-1]
    };
    /*!
     * Returns the i-th literal of constraint c, i.e.
     * - li, iff c == ffb_btb
     * - ~li, iff c == ftb_bfb.
     */
    [[nodiscard]] Literal lit(uint32_t i, ActiveConstraint c) const { return Literal::fromId(lits_->lit(i).id() ^ c); }
    //! Returns the weight of the i-th literal or 1 if constraint is a cardinality constraint.
    [[nodiscard]] Weight_t weight(uint32_t i) const { return lits_->weight(i); }
    //! Returns the number of literals in this constraint (including W).
    [[nodiscard]] uint32_t size() const { return lits_->size(); }
    //! Returns false if constraint is a cardinality constraint.
    [[nodiscard]] bool isWeight() const { return lits_->weights(); }
    // Returns the index of next literal to look at during backward propagation.
    [[nodiscard]] uint32_t getBpIndex() const { return not isWeight() ? 1 : undo_[0].data >> 1; }

private:
    static WeightConstraint* doCreate(Solver& s, Literal con, WeightLitsRep& rep, CreateFlag flags);
    bool                     integrateRoot(Solver& s);
    struct WL {
        WL(uint32_t s, bool shared, bool w);
        [[nodiscard]] bool     shareable() const { return rc != 0; }
        [[nodiscard]] bool     unique() const { return rc == 0 || refCount() == 1; }
        [[nodiscard]] bool     weights() const { return w != 0; }
        [[nodiscard]] uint32_t size() const { return sz; }
        [[nodiscard]] Literal  lit(uint32_t i) const { return lits[(i << w)]; }
        [[nodiscard]] Var_t    var(uint32_t i) const { return lits[(i << w)].var(); }
        [[nodiscard]] Weight_t weight(uint32_t i) const {
            return not weights() ? 1 : static_cast<Weight_t>(lits[(i << 1) + 1].rep());
        }
        [[nodiscard]] uint32_t refCount() const;
        WL*                    clone();
        void                   release();
        uint8_t*               address();
        uint32_t               sz : 30; // number of literals
        uint32_t               rc : 1;  // ref counted?
        uint32_t               w  : 1;  // has weights?
        POTASSCO_WARNING_BEGIN_RELAXED
        Literal lits[0]; // Literals of constraint: ~B [Bw], l1 [w1], ..., ln-1 [Wn-1]
        POTASSCO_WARNING_END_RELAXED
    };
    WeightConstraint(Solver& s, SharedContext* ctx, Literal con, const WeightLitsRep&, WL* out, uint32_t act = 3u);
    WeightConstraint(Solver& s, const WeightConstraint& other);

    static constexpr uint32_t not_active = 3u;

    // Represents a literal on the undo stack.
    // idx()        returns the index of the literal.
    // constraint() returns the constraint that added the literal to the undo stack.
    // Note: Only 31-bits are used for undo info.
    // The remaining bit is used as a flag for marking processed literals.
    struct UndoInfo {
        explicit UndoInfo(uint32_t d = 0) : data(d) {}
        [[nodiscard]] uint32_t         idx() const { return data >> 2; }
        [[nodiscard]] ActiveConstraint constraint() const { return static_cast<ActiveConstraint>((data & 2) != 0); }
        uint32_t                       data;
    };
    // Is literal idx contained as reason lit in the undo stack?
    [[nodiscard]] bool litSeen(uint32_t idx) const { return (undo_[idx].data & 1) != 0; }
    // Mark/unmark literal idx.
    void toggleLitSeen(uint32_t idx) { undo_[idx].data ^= 1; }
    // Add watch for idx-th literal of c to the solver.
    void addWatch(Solver& s, uint32_t idx, ActiveConstraint c);
    // Updates bound_[c] and adds an undo watch to the solver if necessary.
    // Then adds the literal at position idx to the reason set (and the undo stack).
    void updateConstraint(Solver& s, uint32_t level, uint32_t idx, ActiveConstraint c);
    // Returns the starting index of the undo stack.
    [[nodiscard]] uint32_t undoStart() const { return isWeight(); }
    [[nodiscard]] UndoInfo undoTop() const {
        assert(up_ != undoStart());
        return undo_[up_ - 1];
    }
    // Returns the decision level of the last assigned literal
    // or 0 if no literal was assigned yet.
    [[nodiscard]] uint32_t highestUndoLevel(const Solver&) const;
    void                   setBpIndex(uint32_t n);

    WL*      lits_;         // literals of constraint
    uint32_t up_      : 27; // undo position; [undoStart(), up_) is the undo stack
    uint32_t ownsLit_ : 1;  // owns lits_?
    uint32_t active_  : 2;  // which of the two sub-constraints is currently unit?
    uint32_t watched_ : 2;  // which constraint is watched (3 both, 2 ignore, ftb_bfb, ffb_btb)
    Weight_t bound_[2]{};   // ffb_btb: (sumW-bound)+1 / ftb_bfb: bound
    POTASSCO_WARNING_BEGIN_RELAXED
    UndoInfo undo_[0]; // undo stack + seen flag for each literal
    POTASSCO_WARNING_END_RELAXED
};
} // namespace Clasp
