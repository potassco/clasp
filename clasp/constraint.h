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

#include <clasp/literal.h>
#include <clasp/util/misc_types.h> // bits stuff

#include <potassco/basic_types.h>

#include <cassert>

/*!
 * \file
 * \brief Defines the base classes for boolean constraints.
 */
namespace Clasp {

class SharedContext;
class Solver;
class ClauseHead;
struct CCMinRecursive;

/**
 * \defgroup constraint Constraints
 * \brief Boolean Constraints, post propagators, and related types.
 * @{ */

//! Constraint types distinguished by a Solver.
enum class ConstraintType : uint32_t {
    static_  = 0, //!< An unremovable constraint (e.g. a problem constraint).
    conflict = 1, //!< A removable constraint derived from conflict analysis.
    loop     = 2, //!< A removable constraint derived from unfounded set checking.
    other    = 3, //!< A removable constraint learnt by some other means.
};
POTASSCO_SET_DEFAULT_ENUM_MAX(ConstraintType::other);
POTASSCO_ENABLE_CMP_OPS(ConstraintType);
using TypeSet = Potassco::Bitset<uint32_t, ConstraintType>;

struct ConstraintScore;
class ConstraintInfo;

//! Base class for (boolean) constraints to be used in a Solver.
/*!
 * Base class for (boolean) constraints like e.g. clauses. Concrete constraint classes define
 * representations for constraints over boolean variables.
 * Each constraint class must define a method for inference (derive information from an assignment),
 * it must be able to detect conflicts (i.e. detect when the current assignment makes the constraint unsatisfiable)
 * and to return a reason for inferred literals as well as conflicts (as a set of literals).
 */
class Constraint {
public:
    //! Type used as return type for Constraint::propagate.
    struct PropResult {
        constexpr explicit PropResult(bool a_ok = true, bool a_keepWatch = true) : ok(a_ok), keepWatch(a_keepWatch) {}
        bool ok;        //!< true if propagation completes without conflict.
        bool keepWatch; //!< true if constraint wants to keep the current watch.
    };
    Constraint();
    Constraint(const Constraint&)            = delete;
    Constraint& operator=(const Constraint&) = delete;

    /*!
     * \name Mandatory functions.
     * Functions that must be implemented by all constraints.
     * @{ */

    /*!
     * Propagate is called for each constraint that watches p. It shall enqueue
     * all consequences of p becoming true.
     * \pre p is true in s
     * \param s The solver in which p became true.
     * \param p A literal watched by this constraint that recently became true.
     * \param data The data-blob that this constraint passed when the watch for p was registered.
     */
    virtual PropResult propagate(Solver& s, Literal p, uint32_t& data) = 0;

    /*!
     * \pre This constraint is the reason for p being true in s.
     * \post The literals implying p were added to lits.
     */
    virtual void reason(Solver& s, Literal p, LitVec& lits) = 0;

    //! Returns a clone of this and adds necessary watches to the given solver.
    /*!
     * The function shall create and return a copy of this constraint
     * to be used in the given solver. Furthermore, it shall add
     * necessary watches to the given solver.
     * \note Return 0 to indicate that cloning is not supported.
     */
    virtual Constraint* cloneAttach(Solver& other) = 0;
    //@}

    /*!
     * \name Additional functions.
     * Functions that can be implemented by constraints.
     * @{ */
    //! Called when the given solver removes a decision level watched by this constraint.
    virtual void undoLevel(Solver& s);

    /*!
     * \brief Simplify this constraint.
     *
     * \pre s.decisionLevel() == 0 and the current assignment is fully propagated.
     * \return
     *  true if this constraint can be ignored (e.g. is satisfied),
     *  false otherwise.
     * \post
     * If simplify returned true, this constraint has previously removed all its watches
     * from the solver.
     *
     * \note The default implementation simply returns false.
     */
    virtual bool simplify(Solver& s, bool reinit = false);

    /*!
     * \brief Delete this constraint.
     * \note The default implementation simply calls delete this.
     * \param s The solver in which this constraint is used (can be 0).
     * \param detach Whether the constraint shall detach itself from the given solver.
     */
    virtual void destroy(Solver* s = nullptr, bool detach = false);

    //! Shall return whether the constraint is valid (i.e. not conflicting) w.r.t the current assignment in s.
    /*!
     * \pre The assignment in s is not conflicting and fully propagated.
     * \post A changed assignment if the assignment was not valid.
     * \note The default implementation always returns true and assumes
     *       that conflicts are detected by Constraint::propagate().
     */
    virtual bool valid(Solver& s);

    //! Called during minimization of learnt clauses if this is the reason for p being true in s.
    /*!
     * \return true if p can be removed from the current learnt clause, false otherwise.
     * \note The default implementation uses the following inefficient algorithm
     * \code
     *   LitVec temp;
     *   reason(s, p, temp);
     *   for each x in temp
     *     if (!s.ccMinimize(p, rec)) return false;
     *   return true;
     * \endcode
     */
    virtual bool minimize(Solver& s, Literal p, CCMinRecursive* rec);

    //! Returns an estimate of the constraint's complexity relative to a clause (complexity = 1).
    [[nodiscard]] virtual uint32_t estimateComplexity(const Solver& s) const;

    //! Shall return this if constraint is a clause, otherwise 0.
    /*!
     * The default implementation returns 0.
     */
    virtual ClauseHead* clause();
    //@}

    /*!
     * \name Functions for learnt constraints.
     *
     * Learnt constraints can be created and deleted dynamically during the search-process and
     * are subject to nogood-deletion.
     * A learnt constraint shall at least define the methods type() and locked().
     * @{ */

    using Type      = ConstraintType;
    using ScoreType = ConstraintScore;
    using InfoType  = ConstraintInfo;

    //! Returns the type of this (learnt) constraint.
    [[nodiscard]] virtual Type type() const;

    /*!
     * Shall return true if this constraint can't be deleted because it
     * currently implies one or more literals and false otherwise.
     * The default implementation returns true.
     */
    [[nodiscard]] virtual bool locked(const Solver& s) const;

    //! Returns the activity of the constraint.
    /*!
     * \note A solver uses the activity-value in order to establish an ordering
     * of learnt constraints. Whenever a solver needs to delete some learnt constraints it
     * selects from the unlocked ones those with a low activity-value.
     * \note The default-implementation always returns the minimal activity.
     */
    [[nodiscard]] virtual ScoreType activity() const;
    //! Asks the constraint to decrease its activity.
    virtual void decreaseActivity();
    //! Asks the constraint to reset its activity.
    virtual void resetActivity();
    //! Shall return 0 if either !t.inSet(type()) or this constraint is satisfied w.r.t the current assignment.
    /*!
     * If this constraint is currently not satisfied and t.inSet(type()), shall return type()
     * and freeLits shall contain all currently unassigned literals of this constraint.
     *
     * The default implementation always returns 0.
     */
    virtual uint32_t isOpen(const Solver& s, const TypeSet& t, LitVec& freeLits);
    //@}
protected:
    virtual ~Constraint();
};
//@}

/**
 * \defgroup propagator Propagators
 * \brief Post propagators and related types.
 * \ingroup constraint
 * @{
 */

//! Base class for post propagators.
/*!
 * Post propagators are called after unit propagation on each decision level and
 * once after a total assignment is found.
 *
 * They extend a solver's unit-propagation with more elaborate propagation mechanisms.
 * The typical asp example is an unfounded set check.
 *
 * \note Currently, the solver distinguishes \b two classes of post propagators:
 *       - class_simple: deterministic post propagators that only extend
 *         the current decision level. That is, these post propagators shall neither
 *         backtrack below the current decision level nor permanently add new decision levels.
 *         Deterministic post propagators are called in priority order. For this,
 *         the function PostPropagator::priority() is used and shall return a priority in the range:
 * <tt>[priority_class_simple, priority_class_general)</tt>
 *       - class_general: post propagators that are non-deterministic or those that are not limited to extending
 *         the current decision level shall have a priority of priority_class_general. They are called in FIFO order
 *         after \b all simple post propagators have reached a fixpoint.
 *
 * \note There are currently three reserved priority values, namely
 *  - priority_reserved_msg for message and termination handler (if any),
 *  - priority_reserved_ufs for the default unfounded set checker (if any),
 *  - and priority_reserved_look for the default lookahead operator (if any).
 *  .
 */
class PostPropagator : public Constraint {
public:
    PostPropagator();
    ~PostPropagator() override;
    PostPropagator(const PostPropagator&)            = delete;
    PostPropagator& operator=(const PostPropagator&) = delete;
    using Constraint::propagate; // Enable overloading!

    PostPropagator* next; // main propagation lists of post propagators
    //! Default priorities for post propagators.
    enum Priority {
        priority_class_simple  = 0,    //!< Starting priority of simple post propagators.
        priority_reserved_msg  = 0,    //!< Reserved priority for message/termination handlers (if any).
        priority_reserved_ufs  = 10,   //!< Reserved priority for the default unfounded set checker (if any).
        priority_reserved_look = 1023, //!< Reserved priority for the default lookahead operator (if any).
        priority_class_general = 1024, //!< Priority of extended post propagators.
    };

    //! Shall return a value representing the priority of this propagator.
    /*!
     * The priority is used to order sequences of post propagators and to
     * classify post propagators w.r.t the classes: class_simple and class_general.
     * \note See class description for an overview of the two priority classes.
     */
    [[nodiscard]] virtual uint32_t priority() const = 0;

    //! Called during initialization of s.
    /*!
     * \note During initialization a post propagator may assign variables,
     *       but it must not yet propagate them.
     */
    virtual bool init(Solver& s);

    //! Shall enqueue and propagate new assignments implied by this propagator.
    /*!
     * This function shall enqueue and propagate all assignments currently implied by
     * this propagator until a fixpoint is reached w.r.t this post propagator or
     * a conflict is detected.
     *
     * \pre   The assignment is fully propagated w.r.t any previous post propagator.
     * \param s    The solver in which this post propagator is used.
     * \param ctx  The post propagator from which this post propagator is called or
     *             0 if no other post propagator is currently active.
     * \post  s.queueSize() == 0 || s.hasConflict()
     * \return false if propagation led to conflict, true otherwise
     *
     * \note
     *   The function shall not call Solver::propagate()
     *   or any other function that would result in a recursive chain
     *   of propagate() calls. On the other hand, it shall call
     *   Solver::propagateUntil(this) after enqueuing any new assignments
     *   to initiate propagation up to this propagator.
     *
     * Typically, propagateFixpoint() should implement a loop like this:
     * \code
     * for (;;) {
     *   if (!assign_newly_implied_literals(s)){ return false; }
     *   if (s.queueSize() == 0)               { return true;  }
     *   if (!s.propagateUntil(this))          { return false; }
     * }
     * \endcode
     */
    virtual bool propagateFixpoint(Solver& s, PostPropagator* ctx) = 0;

    //! Aborts an active propagation operation.
    /*!
     * The function reset() is called whenever propagation on the
     * current decision level is stopped before a fixpoint is reached.
     * In particular, a solver calls reset() when a conflict is detected
     * during propagation.
     *
     * \note The default implementation is a noop.
     */
    virtual void reset();

    //! Is the current total assignment a model?
    /*!
     * \pre The assignment is total and not conflicting.
     * \return
     *  - true if the assignment is a model w.r.t this post propagator
     *  - false otherwise
     * \post If the function returned true:  s.numFreeVars() == 0 && !s.hasConflict().
     *       If the function returned false: s.numFreeVars() > 0 || s.hasConflict().
     * \note The default implementation returns Constraint::valid(s);
     */
    virtual bool isModel(Solver& s);

protected:
    //! Calls reset on post propagators following this.
    void cancelPropagation();

    //! PostPropagators are not cloneable by default.
    Constraint* cloneAttach(Solver&) override { return nullptr; }
    // Constraint interface - noops
    PropResult propagate(Solver&, Literal, uint32_t&) override;
    void       reason(Solver&, Literal, LitVec&) override;
};

//! A special post propagator used to handle messages and signals.
class MessageHandler : public PostPropagator {
public:
    MessageHandler();
    virtual bool           handleMessages() = 0;
    [[nodiscard]] uint32_t priority() const override { return priority_reserved_msg; }
    bool                   propagateFixpoint(Solver&, PostPropagator*) override { return handleMessages(); }
};

//! An intrusive list of post propagators ordered by priority.
/*!
 * Propagators in the list are owned by the list.
 */
class PropagatorList {
public:
    PropagatorList();
    ~PropagatorList();
    PropagatorList(PropagatorList&&) = delete;
    void add(PostPropagator* p);
    void remove(PostPropagator* p);
    void clear();
    template <typename Pred>
    requires(std::is_invocable_r_v<bool, Pred, PostPropagator*>)
    [[nodiscard]] auto find(const Pred& p, uint32_t prio = UINT32_MAX) const -> PostPropagator* {
        return prio == UINT32_MAX ? findImpl([&](PostPropagator* x) { return p(x) <=> true; })
                                  : findImpl([&](PostPropagator* x) {
                                        auto cmp = x->priority() <=> prio;
                                        return cmp != std::strong_ordering::equal ? cmp : p(x) <=> true;
                                    });
    }
    [[nodiscard]] auto find(uint32_t prio) const -> PostPropagator* {
        return findImpl([&](const PostPropagator* p) { return p->priority() <=> prio; });
    }
    [[nodiscard]] auto head() const -> PostPropagator* const* { return &head_; }
    PostPropagator**   head() { return &head_; }

    // Operations applied on all elements.
    bool init(Solver& s);
    bool simplify(Solver& s, bool reinit = false);
    bool isModel(Solver& s);

private:
    template <typename P>
    [[nodiscard]] auto findImpl(const P& pred) const -> PostPropagator* {
        for (auto* x = head_; x; x = x->next) {
            if (auto cmp = pred(x); cmp == std::strong_ordering::equal) {
                return x;
            }
            else if (cmp == std::strong_ordering::greater) {
                break;
            }
        }
        return nullptr;
    }
    PostPropagator* head_; // head of pp-list
};
//@}

/**
 * \addtogroup constraint
 * @{ */

//! Stores a reference to the constraint that implied a literal.
/*!
 * Stores a reference to the constraint that implied a certain literal or
 * null if the literal has no antecedent (i.e. is a decision literal or a top-level fact).
 *
 * \note
 * The constraint that implied a literal can have three different representations:
 * - it can be a single literal (binary clause constraint)
 * - it can be two literals (ternary clause constraint)
 * - it can be a pointer to a constraint (generic constraint)
 * .
 *
 * \par Implementation:
 *
 * The class stores all three representations in one tagged 64-bit integer, i.e.
 * from the 64-bits the 2 LSBs encode the type stored:
 *  - 00: Pointer to constraint
 *  - 01: ternary constraint (i.e. two literals stored in the remaining 62 bits).
 *  - 10: binary constraint (i.e. one literal stored in the highest 31 bits)
 *  .
 */
class Antecedent {
public:
    enum Type { generic = 0, ternary = 1, binary = 2 };
    //! Creates a null Antecedent.
    /*!
     * \post: isNull() == true && type == Generic
     */
    constexpr Antecedent() : data_(0) {}

    //! Creates an Antecedent from the literal p.
    /*!
     * \post: type() == Binary && firstLiteral() == p
     */
    constexpr Antecedent(const Literal& p) {
        // first lit is stored in high dword
        data_ = (static_cast<uint64_t>(p.id()) << 33) + binary;
        assert(type() == binary && firstLiteral() == p);
    }

    //! Creates an Antecedent from the literals p and q.
    /*!
     * \post type() == Ternary && firstLiteral() == p && secondLiteral() == q
     */
    constexpr Antecedent(const Literal& p, const Literal& q) {
        // first lit is stored in high dword
        // second lit is stored in low dword
        data_ = (static_cast<uint64_t>(p.id()) << 33) + (static_cast<uint64_t>(q.id()) << 2) + ternary;
        assert(type() == ternary && firstLiteral() == p && secondLiteral() == q);
    }

    //! Creates an Antecedent from the Constraint con.
    /*!
     * \post type() == Generic && constraint() == con
     */
    Antecedent(Constraint* con) : data_(reinterpret_cast<uintptr_t>(con)) {
        static_assert(sizeof(Constraint*) <= sizeof(uint64_t), "unsupported pointer size");
        assert(type() == generic && constraint() == con);
    }

    //! Returns true if this antecedent does not refer to any constraint.
    [[nodiscard]] constexpr bool isNull() const { return data_ == 0; }
    //! Returns the antecedent's type.
    [[nodiscard]] constexpr Type type() const { return static_cast<Type>(data_ & 3); }
    //! Returns true if the antecedent is a learnt nogood.
    [[nodiscard]] constexpr bool learnt() const {
        return Potassco::right_most_bit(data_) > binary && constraint()->type() != ConstraintType::static_;
    }

    //! Extracts the constraint-pointer stored in this object.
    /*!
     * \pre type() == Generic
     */
    [[nodiscard]] Constraint* constraint() const {
        assert(type() == generic);
        return reinterpret_cast<Constraint*>(static_cast<uintptr_t>(data_));
    }

    //! Extracts the first literal stored in this object.
    /*!
     * \pre type() != Generic
     */
    [[nodiscard]] constexpr Literal firstLiteral() const {
        assert(type() != generic);
        return Literal::fromId(static_cast<uint32_t>(data_ >> 33));
    }

    //! Extracts the second literal stored in this object.
    /*!
     * \pre type() == Ternary
     */
    [[nodiscard]] constexpr Literal secondLiteral() const {
        assert(type() == ternary);
        return Literal::fromId(static_cast<uint32_t>(data_ >> 1) >> 1);
    }

    //! Returns the reason for p.
    /*!
     * \pre !isNull()
     */
    void reason(Solver& s, Literal p, LitVec& lits) const {
        assert(not isNull());
        Type t = type();
        if (t == generic) {
            constraint()->reason(s, p, lits);
            return;
        }
        lits.push_back(firstLiteral());
        if (t == ternary) {
            lits.push_back(secondLiteral());
        }
    }
    template <class S>
    bool minimize(S& s, Literal p, CCMinRecursive* rec) const {
        assert(not isNull());
        Type t = type();
        if (t == generic) {
            return constraint()->minimize(s, p, rec);
        }
        return s.ccMinimize(firstLiteral(), rec) && (t != ternary || s.ccMinimize(secondLiteral(), rec));
    }

    //! Returns true iff the antecedent refers to the constraint con.
    bool operator==(const Constraint* con) const {
        return static_cast<uintptr_t>(data_) == reinterpret_cast<uintptr_t>(con);
    }
    [[nodiscard]] constexpr uint64_t asUint() const { return data_; }
    constexpr uint64_t&              asUint() { return data_; }

private:
    uint64_t data_;
};

constexpr uint32_t lbd_max = 127u;           //!< highest possible lbd value.
constexpr uint32_t act_max = (1u << 20) - 1; //!< highest possible activity value.
//! Type storing a constraint's activity.
struct ConstraintScore {
    using Score                          = ConstraintScore;
    static constexpr uint32_t bits_used  = 28u;
    static constexpr uint32_t bumped_bit = 27;
    static constexpr uint32_t lbd_shift  = 20u;
    static constexpr uint32_t lbd_mask   = lbd_max << lbd_shift;
    static constexpr uint32_t score_mask = Potassco::bit_max<uint32_t>(bits_used);

    explicit constexpr ConstraintScore(uint32_t act = 0, uint32_t lbd = 0)
        : rep(std::min(lbd, lbd_max) << lbd_shift | std::min(act, act_max)) {}

    constexpr void                   reset(uint32_t act = 0, uint32_t lbd = 0) { assign(ConstraintScore(act, lbd)); }
    [[nodiscard]] constexpr uint32_t activity() const { return rep & act_max; }
    [[nodiscard]] constexpr uint32_t lbd() const { return hasLbd() ? (rep & lbd_mask) >> lbd_shift : lbd_max; }
    [[nodiscard]] constexpr bool     hasLbd() const { return Potassco::test_any(rep, lbd_mask); }
    [[nodiscard]] constexpr bool     bumped() const { return Potassco::test_bit(rep, bumped_bit); }
    constexpr void                   bumpActivity() { rep += (activity() < act_max); }
    constexpr void                   bumpLbd(uint32_t x) {
        if (x < lbd()) {
            Potassco::store_clear_mask(rep, lbd_mask);
            Potassco::store_set_mask(rep, (x << lbd_shift) | Potassco::nth_bit<uint32_t>(bumped_bit));
        }
    }
    constexpr void clearBumped() { Potassco::store_clear_bit(rep, bumped_bit); }
    constexpr void reduce() {
        clearBumped();
        if (uint32_t a = activity()) {
            Potassco::store_clear_mask(rep, act_max);
            Potassco::store_set_mask(rep, a >> 1);
        }
    }
    constexpr void assign(Score o) {
        Potassco::store_clear_mask(rep, score_mask);
        Potassco::store_set_mask(rep, o.rep & score_mask);
    }

    friend constexpr bool operator==(ConstraintScore lhs, ConstraintScore rhs) noexcept {
        return (lhs.rep & score_mask) == (rhs.rep & score_mask);
    }

    uint32_t rep;
};

//! Type storing meta information about a constraint.
class ConstraintInfo : private ConstraintScore {
public:
    using Info  = ConstraintInfo;
    using Score = ConstraintScore;
    constexpr ConstraintInfo(ConstraintType t = ConstraintType::static_) {
        static_assert(ConstraintScore::bits_used <= 28, "invalid score");
        rep = static_cast<uint32_t>(t) << type_shift;
    }
    using ConstraintScore::activity;
    using ConstraintScore::lbd;
    [[nodiscard]] constexpr ConstraintType type() const {
        return static_cast<ConstraintType>((rep & type_mask) >> type_shift);
    }
    [[nodiscard]] constexpr bool         tagged() const { return Potassco::test_bit(rep, tag_bit); }
    [[nodiscard]] constexpr bool         aux() const { return tagged() || Potassco::test_bit(rep, aux_bit); }
    [[nodiscard]] constexpr bool         learnt() const { return type() != ConstraintType::static_; }
    [[nodiscard]] constexpr const Score& score() const { return *this; }
    constexpr Score&                     score() { return *this; }

    constexpr Info& setType(ConstraintType t) {
        Potassco::store_clear_mask(rep, type_mask);
        Potassco::store_set_mask(rep, (static_cast<uint32_t>(t) << type_shift));
        return *this;
    }
    constexpr Info& setScore(Score sc) {
        assign(sc);
        return *this;
    }
    constexpr Info& setActivity(uint32_t a) {
        assign(ConstraintScore(a, lbd()));
        return *this;
    }
    constexpr Info& setLbd(uint32_t lbd) {
        assign(ConstraintScore(activity(), lbd));
        return *this;
    }
    constexpr Info& setTagged(bool b) {
        tagged() == b || Potassco::store_toggle_bit(rep, tag_bit);
        return *this;
    }
    constexpr Info& setAux(bool b) {
        aux() == b || Potassco::store_toggle_bit(rep, aux_bit);
        return *this;
    }

private:
    static constexpr uint32_t tag_bit    = 31u;
    static constexpr uint32_t aux_bit    = 30u;
    static constexpr uint32_t type_shift = 28u;
    static constexpr uint32_t type_mask  = 3u << type_shift;
};
//@}

/**
 * \defgroup shared_con Shared
 * \brief %Constraint data that can safely be shared between solvers.
 * \ingroup constraint
 */

} // namespace Clasp
