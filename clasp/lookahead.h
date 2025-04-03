//
// Copyright (c) 2009-present Benjamin Kaufmann
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

/*!
 * \file
 * \brief Defines lookahead related types.
 *
 * Lookahead can be used as a post propagator (e.g. failed-literal detection) and
 * optionally as a heuristic.
 */

#include <clasp/constraint.h>
#include <clasp/solver.h>
namespace Clasp {
/*!
 * \addtogroup propagator
 */
//@{

//! Type used to store lookahead-information for one variable.
struct VarScore {
    constexpr VarScore() = default;
    //! Is literal p dependent?
    [[nodiscard]] constexpr bool seen(Literal p) const { return (seen_ & mask(p)) != 0; }
    //! Is this var dependent?
    [[nodiscard]] constexpr bool seen() const { return seen_ != 0; }
    //! Mark literal p as tested during lookahead.
    constexpr void setTested(Literal p) { tested_ |= mask(p); }
    //! Was literal p tested during lookahead?
    [[nodiscard]] constexpr bool tested(Literal p) const { return (tested_ & mask(p)) != 0; }
    //! Was some literal of this var tested?
    [[nodiscard]] constexpr bool tested() const { return tested_ != 0; }
    //! Were both literals of this var tested?
    [[nodiscard]] constexpr bool testedBoth() const { return tested_ == 3u; }

    //! Sets the score for literal p to value and marks p as tested.
    constexpr void setScore(Literal p, uint32_t value) {
        setScoreImpl(p, value);
        setTested(p);
    }
    //! Sets the score of a dependent literal p to min(sc, current score) and mark p as seen.
    constexpr void setDepScore(Literal p, uint32_t sc) {
        if (not seen(p) || score(p) > sc) {
            setScoreImpl(p, sc);
            seen_ |= mask(p);
        }
    }
    //! Returns the score for literal p.
    [[nodiscard]] constexpr uint32_t score(Literal p) const { return p.sign() ? nVal_ : pVal_; }
    //! Returns the scores of the two literals of a variable.
    /*!
     * \param[out] mx The maximum score.
     * \param[out] mn The minimum score.
     */
    void score(uint32_t& mx, uint32_t& mn) const {
        if (nVal_ > pVal_) {
            mx = nVal_;
            mn = pVal_;
        }
        else {
            mx = pVal_;
            mn = nVal_;
        }
    }
    //! Returns the sign of the literal that has the higher score.
    [[nodiscard]] constexpr bool prefSign() const { return nVal_ > pVal_; }

    [[nodiscard]] constexpr uint32_t nVal() const { return nVal_; }
    [[nodiscard]] constexpr uint32_t pVal() const { return pVal_; }

private:
    static constexpr auto     max_score = (1u << 14) - 1;
    static constexpr uint32_t mask(Literal p) { return static_cast<uint32_t>(p.sign()) + 1u; }

    constexpr void setScoreImpl(Literal p, uint32_t value) {
        if (value > max_score) {
            value = max_score;
        }
        if (p.sign()) {
            nVal_ = value;
        }
        else {
            pVal_ = value;
        }
    }

    uint32_t pVal_   : 14 = 0;
    uint32_t nVal_   : 14 = 0;
    uint32_t seen_   : 2  = 0;
    uint32_t tested_ : 2  = 0;
};

//! A small helper class used to score the result of a lookahead operation.
struct ScoreLook {
    enum Mode { score_max, score_max_min };
    using VarScores = PodVector_t<VarScore>; /**< A vector of variable-scores */
    [[nodiscard]] bool validVar(Var_t v) const { return v < score.size(); }
    void               scoreLits(const Solver& s, LitView lits);
    void               clearDeps();
    static uint32_t    countNant(const Solver& s, LitView lits);
    [[nodiscard]] bool greater(Var_t lhs, Var_t rhs) const;
    [[nodiscard]] bool greaterMax(Var_t x, uint32_t max) const {
        return score[x].nVal() > max || score[x].pVal() > max;
    }
    [[nodiscard]] bool greaterMaxMin(Var_t lhs, uint32_t max, uint32_t min) const {
        uint32_t lhsMin, lhsMax;
        score[lhs].score(lhsMax, lhsMin);
        return lhsMin > min || (lhsMin == min && lhsMax > max);
    }
    VarScores score;                //!< score[v] stores lookahead score of v
    VarVec    deps;                 //!< Tested vars and those that follow from them.
    VarType   types{VarType::atom}; //!< Var types to consider.
    Var_t     best{0};              //!< Var with best score among those in deps.
    uint32_t  limit{UINT32_MAX};    //!< Stop after this number of tests
    Mode      mode{score_max};      //!< Score mode to apply.
    bool      addDeps{true};        //!< Add/score dependent vars?
    bool      nant{false};          //!< Score only atoms in NegAnte(P)?
};

class UnitHeuristic;

//! Lookahead extends propagation with failed-literal detection.
/*!
 * The class provides different kinds of one-step lookahead.
 * Atom- and body-lookahead are uniform lookahead types, where
 * either only atoms or bodies are tested. Hybrid-lookahead tests
 * both types of vars but each only in a single phase. I.e. atoms
 * are only tested negatively while bodies are tested positively.
 */
class Lookahead : public PostPropagator {
public:
    static constexpr auto prio = priority_reserved_look;
    //! Set of parameters to configure lookahead.
    struct Params {
        Params(VarType t = VarType::atom) : type(t) {} // NOLINT
        Params& lookahead(VarType t) {
            type = t;
            return *this;
        }
        Params& addImps(bool b) {
            topLevelImps = b;
            return *this;
        }
        Params& nant(bool b) {
            restrictNant = b;
            return *this;
        }
        Params& limit(uint32_t x) {
            lim = x;
            return *this;
        }
        VarType  type;
        uint32_t lim{0};
        bool     topLevelImps{true};
        bool     restrictNant{false};
    };
    static bool isType(uint32_t t) { return t != 0 && t <= VarType::hybrid; }
    /*!
     * \param p Lookahead parameters to use.
     */
    explicit Lookahead(const Params& p);
    ~Lookahead() override;

    bool init(Solver& s) override;
    //! Clears the lookahead list.
    void clear();
    //! Returns true if lookahead list is empty.
    [[nodiscard]] bool empty() const { return head()->next == head_id; }
    //! Adds literal p to the lookahead list.
    void append(Literal p, bool testBoth);
    //! Executes a single-step lookahead on all vars in the lookahead list.
    bool propagateFixpoint(Solver& s, PostPropagator*) override;
    //! Returns PostPropagator::priority_reserved_look.
    [[nodiscard]] uint32_t priority() const override;
    void                   destroy(Solver* s, bool detach) override;
    ScoreLook              score; //!< State of last lookahead operation.
    //! Returns "best" literal w.r.t scoring of last lookahead or lit_true() if no such literal exists.
    Literal            heuristic(Solver& s);
    void               detach(Solver& s);
    [[nodiscard]] bool hasLimit() const { return limit_ != 0; }

protected:
    bool propagateLevel(Solver& s); // called by propagate
    void undoLevel(Solver& s) override;
    bool test(Solver& s, Literal p);

private:
    using NodeId                  = uint32_t;
    static constexpr auto head_id = static_cast<NodeId>(0);
    static constexpr auto undo_id = static_cast<NodeId>(1);
    struct LitNode {
        explicit LitNode(Literal x) : lit(x) {}
        Literal lit;
        NodeId  next{UINT32_MAX};
    };
    using UndoStack = PodVector_t<NodeId>;
    using LookList  = PodVector_t<LitNode>;
    void                         splice(NodeId n);
    LitNode*                     node(NodeId n) { return &nodes_[n]; }
    LitNode*                     head() { return &nodes_[head_id]; } // head of circular candidate list
    LitNode*                     undo() { return &nodes_[undo_id]; } // head of undo list
    bool                         checkImps(Solver& s, Literal p);
    [[nodiscard]] const LitNode* head() const { return &nodes_[head_id]; }
    LookList                     nodes_; // list of literals to test
    UndoStack                    saved_; // stack of undo lists
    LitVec                       imps_;  // additional top-level implications
    NodeId                       last_;  // last candidate in list; invariant: node(last_)->next == head_id;
    NodeId                       pos_;   // current lookahead start position
    uint32_t                     top_;   // size of top-level
    uint32_t                     limit_; // stop lookahead after this number of applications
};
//@}

//! Heuristic that uses the results of lookahead.
/*!
 * \ingroup heuristic
 * The heuristic uses a Lookahead post propagator to select a literal with the highest score,
 * where the score is determined by counting assignments made during
 * failed-literal detection. For hybrid_lookahead, the heuristic selects the literal that
 * derived the most literals. On the other hand, for uniform_lookahead the heuristic is similar to
 * the smodels lookahead heuristic and selects the literal that maximizes the minimum.
 * \see Patrik Simons: "Extending and Implementing the Stable Model Semantics" for a
 * detailed description of the lookahead heuristic.
 *
 * \note The heuristic might itself apply some lookahead but only on variables that
 *       did not fail in a previous call to Lookahead::propagateFixpoint(). I.e. if
 *       priorities are correct for all post propagators in s, the lookahead operations can't fail.
 *
 * \note If no Lookahead post propagator exists in the solver, the heuristic selects the first free variable!
 */
class UnitHeuristic : public SelectFirst {
public:
    UnitHeuristic();
    //! Decorates the heuristic given in other with temporary lookahead.
    static UnitHeuristic* restricted(DecisionHeuristic* other);
    void                  endInit(Solver& /* s */) override;
    Literal               doSelect(Solver& s) override;

private:
    static Lookahead* getLookahead(const Solver&);

    class Restricted;
};

} // namespace Clasp
