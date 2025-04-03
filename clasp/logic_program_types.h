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

/*!
 * \file
 * \brief Basic types for working with a logic program.
 */
#include <clasp/claspfwd.h>
#include <clasp/literal.h>

#include <potassco/error.h>
#include <potassco/rule_utils.h>

#include <algorithm>

namespace Potassco {
using LitVec  = Clasp::PodVector_t<Lit_t>;
using WLitVec = Clasp::PodVector_t<WeightLit>;
} // namespace Potassco
namespace Clasp {
class ClauseCreator;
using Potassco::id_max;
namespace Asp {
using AtomList = PodVector_t<PrgAtom*>;
using BodyList = PodVector_t<PrgBody*>;
using DisjList = PodVector_t<PrgDisj*>;
using Potassco::Atom_t;
using Potassco::Id_t;
constexpr auto value_weak_true = static_cast<Val_t>(3); /**< true but no proof */
/*!
 * \addtogroup asp
 */
//@{
//! A node of a program-dependency graph.
/*!
 * A node represents a relevant part in a logic program. Each node
 * has at least a literal and a value.
 */
class PrgNode {
public:
    //! Supported node types.
    enum Type : uint32_t { atom = 0u, body = 1u, disj = 2u };
    static constexpr uint32_t no_scc  = (1u << 27) - 1;
    static constexpr uint32_t no_node = (1u << 28) - 1;
    static constexpr uint32_t no_lit  = 1;
    //! Creates a new node that corresponds to a literal that is false.
    constexpr explicit PrgNode(uint32_t id, bool checkScc = true)
        : litId_(no_lit)
        , noScc_(not checkScc)
        , id_(id)
        , val_(value_free)
        , eq_(0)
        , seen_(0) {
        static_assert(sizeof(PrgNode) == sizeof(uint64_t), "Unsupported Alignment");
        POTASSCO_CHECK(id < no_node, EOVERFLOW, "Id out of range");
    }
    PrgNode(const PrgNode&)            = delete;
    PrgNode& operator=(const PrgNode&) = delete;
    //! Is the node still relevant or removed() resp. eq()?
    [[nodiscard]] constexpr bool relevant() const { return eq_ == 0; }
    //! Was the node removed?
    [[nodiscard]] constexpr bool removed() const { return eq_ != 0 && id_ == no_node; }
    //! Ignore the node during scc checking?
    [[nodiscard]] constexpr bool ignoreScc() const { return noScc_ != 0; }
    //! Returns true if this node is equivalent to some other node.
    /*!
     * If eq() is true, the node is no longer relevant and must not be used any further.
     * The only sensible operation is to call id() in order to get the id of the node
     * that is equivalent to this node.
     */
    [[nodiscard]] constexpr bool eq() const { return eq_ != 0 && id_ != no_node; }
    [[nodiscard]] constexpr bool seen() const { return seen_ != 0; }
    //! Returns true if node has an associated variable in a solver.
    [[nodiscard]] constexpr bool hasVar() const { return litId_ != no_lit; }
    //! Returns the variable associated with this node or sent_var if no var is associated with this node.
    [[nodiscard]] constexpr Var_t var() const { return litId_ >> 1; }
    //! Returns the literal associated with this node or a sentinel literal if no var is associated with this node.
    [[nodiscard]] constexpr Literal literal() const { return Literal::fromId(litId_); }
    //! Returns the value currently assigned to this node.
    [[nodiscard]] constexpr Val_t value() const { return val_; }
    //! Returns the current id of this node.
    [[nodiscard]] constexpr uint32_t id() const { return id_; }
    //! Returns the literal that must be true in order to fulfill the truth-value of this node.
    [[nodiscard]] constexpr Literal trueLit() const {
        return value() == value_free ? lit_true : literal() ^ (value() == value_false);
    }

    /*!
     * \name implementation functions
     * Low-level implementation functions. Use with care and only if you
     * know what you are doing!
     */
    //@{
    constexpr void setLiteral(Literal x) { litId_ = x.id(); }
    constexpr void clearLiteral(bool clVal) {
        litId_ = no_lit;
        if (clVal) {
            val_ = value_free;
        }
    }
    constexpr void setValue(Val_t v) { val_ = v; }
    constexpr void setEq(uint32_t eqId) {
        id_   = eqId;
        eq_   = 1;
        seen_ = 1;
    }
    constexpr void setIgnoreScc(bool b) { noScc_ = static_cast<uint32_t>(b); }
    constexpr void markRemoved() {
        if (not eq()) {
            setEq(no_node);
        }
    }
    constexpr void setSeen(bool b) { seen_ = static_cast<uint32_t>(b); }
    constexpr void resetId(uint32_t id, bool seen) {
        id_   = id;
        eq_   = 0;
        seen_ = static_cast<uint32_t>(seen);
    }
    constexpr bool assignValueImpl(Val_t v, bool noWeak) {
        if (v == value_weak_true && noWeak) {
            v = value_true;
        }
        if (value() == value_free || v == value() || (value() == value_weak_true && v == value_true)) {
            setValue(v);
            return true;
        }
        return v == value_weak_true && value() == value_true;
    }
    //@}
protected:
    uint32_t litId_ : 31; // literal-id in solver
    uint32_t noScc_ : 1;  // ignore during scc checks?
    uint32_t id_    : 28; // own id/eq-id/root-id/ufs-id
    uint32_t val_   : 2;  // assigned value
    uint32_t eq_    : 1;  // removed or eq to some other node?
    uint32_t seen_  : 1;  // marked as seen?
};
using NodeType = PrgNode::Type;
//! An edge of a program-dependency graph.
/*!
 * Currently, clasp distinguishes four types of edges:
 *  - a Normal edge stipulates an implication between body and head,
 *    i.e. tableau-rules FTA and BFA for atoms.
 *  - a Choice edge only stipulates a support.
 *  - a Gamma edge is like a Normal edge that is only considered during
 *    nogood creation but ignored in the dependency graph.
 *  - a GammaChoice edge is like a Gamma edge but only stipulates a support.
 * The head of a rule is either an atom or a disjunction.
 */
struct PrgEdge {
    //! Type of edge.
    enum Type : uint32_t { normal = 0, gamma = 1, choice = 2, gamma_choice = 3 };
    static constexpr PrgEdge noEdge() { return {UINT32_MAX}; }

    template <typename NodeT>
    static constexpr PrgEdge newEdge(const NodeT& n, Type eType) {
        // 28-bit node id, 2-bit node type, 2-bit edge type
        return {(n.id() << 4) | (static_cast<uint32_t>(n.nodeType()) << 2) | eType};
    }
    //! Returns the id of the adjacent node.
    [[nodiscard]] constexpr uint32_t node() const { return rep >> 4; }
    //! Returns the type of this edge.
    [[nodiscard]] constexpr Type type() const { return static_cast<Type>(rep & 3u); }
    //! Returns the type of adjacent node.
    [[nodiscard]] constexpr NodeType nodeType() const { return static_cast<NodeType>((rep >> 2) & 3u); }
    //! Returns true if edge has normal semantic (normal edge or gamma edge).
    [[nodiscard]] constexpr bool isNormal() const { return (rep & 2u) == 0; }
    //! Returns true if edge has choice semantic.
    [[nodiscard]] constexpr bool isChoice() const { return (rep & 2u) != 0; }
    //! Returns true if the edge is a gamma (aux normal) edge.
    [[nodiscard]] constexpr bool isGamma() const { return (rep & 1u) != 0; }
    //! Returns true if the adjacent node is a body.
    [[nodiscard]] constexpr bool isBody() const { return nodeType() == PrgNode::body; }
    //! Returns true if the adjacent node is an atom.
    [[nodiscard]] constexpr bool isAtom() const { return nodeType() == PrgNode::atom; }
    //! Returns true if the adjacent node is a disjunction.
    [[nodiscard]] constexpr bool isDisj() const { return nodeType() == PrgNode::disj; }
    //! Returns true if edge is valid, i.e. is not the special "no edge".
    explicit       operator bool() const noexcept { return rep != UINT32_MAX; }
    constexpr bool operator==(const PrgEdge& rhs) const = default;
    constexpr auto operator<=>(const PrgEdge&) const    = default;

    uint32_t rep;
};

using EdgeType = PrgEdge::Type;
using EdgeVec  = bk_lib::pod_vector<PrgEdge>;
using EdgeSpan = SpanView<PrgEdge>;
constexpr bool isChoice(EdgeType t) { return t >= PrgEdge::choice; }

using Potassco::BodyType;
using Potassco::HeadType;
using Potassco::Rule;
using Potassco::WeightLitSpan;
//! A class for translating extended rules to normal rules.
class RuleTransform {
public:
    //! Interface that must be implemented to get the result of a transformation.
    struct ProgramAdapter {
        virtual Atom_t newAtom()              = 0;
        virtual void   addRule(const Rule& r) = 0;

    protected:
        ~ProgramAdapter() = default;
    };
    //! Supported transformation strategies.
    enum Strategy { strategy_default, strategy_no_aux, strategy_allow_aux };
    explicit RuleTransform(ProgramAdapter& prg);
    explicit RuleTransform(LogicProgram& prg);
    ~RuleTransform();
    RuleTransform(RuleTransform&&) = delete;
    //! Transforms the given (extended) rule to a set of normal rules.
    uint32_t transform(const Rule& r, Strategy s = strategy_default);

private:
    struct Impl;
    std::unique_ptr<Impl> impl_;
};

//! A set of flags used during rule simplification.
class AtomState {
public:
    static constexpr uint8_t pos_flag    = 0x1u;  //!< In positive body of active rule
    static constexpr uint8_t neg_flag    = 0x2u;  //!< In negative body of active rule
    static constexpr uint8_t head_flag   = 0x4u;  //!< In normal head of active rule
    static constexpr uint8_t choice_flag = 0x8u;  //!< In choice head of active rule
    static constexpr uint8_t disj_flag   = 0x10u; //!< In disjunctive head of active rule
    static constexpr uint8_t rule_mask   = 0x1Fu; //!< In active rule
    static constexpr uint8_t fact_flag   = 0x20u; //!< Atom is a fact (sticky)
    static constexpr uint8_t false_flag  = 0x40u; //!< Atom is false  (sticky)
    static constexpr uint8_t simp_mask   = 0x7fu; //!< In active rule or assigned
    static constexpr uint8_t dom_flag    = 0x80u; //!< Var of atom is a dom var (sticky)
    AtomState()                          = default;
    void swap(AtomState& o) noexcept { state_.swap(o.state_); }
    //! Does t.node() appear in the head of the active rule?
    [[nodiscard]] bool inHead(PrgEdge t) const { return isSet(t.node(), headFlag(t)); }
    [[nodiscard]] bool inHead(Atom_t atom) const { return isSet(atom, head_flag); }
    //! Does p appear in the body of the active rule?
    [[nodiscard]] bool inBody(Literal p) const { return isSet(p.var(), pos_flag + p.sign()); }
    [[nodiscard]] bool isSet(Var_t v, uint8_t f) const { return v < state_.size() && (state_[v] & f) != 0; }
    [[nodiscard]] bool isFact(Var_t v) const { return isSet(v, fact_flag); }
    //! Mark v as a head of the active rule.
    void addToHead(Atom_t v) { set(v, head_flag); }
    void addToHead(PrgEdge t) { set(t.node(), headFlag(t)); }
    //! Mark p as a literal contained in the active rule.
    void addToBody(Literal p) { set(p.var(), pos_flag + p.sign()); }

    void addToBody(LitView body) {
        for (auto p : body) { addToBody(p); }
    }

    void set(Var_t v, uint8_t f) {
        grow(v);
        state_[v] |= f;
    }
    void clear(Var_t v, uint8_t f) {
        if (v < state_.size()) {
            state_[v] &= ~f;
        }
    }
    void clearRule(Var_t v) { clear(v, rule_mask); }
    void clearHead(PrgEdge t) { clear(t.node(), headFlag(t)); }
    void clearBody(Literal p) { clear(p.var(), pos_flag + p.sign()); }
    void resize(uint32_t sz) { state_.resize(sz); }

    template <std::ranges::range R, typename P>
    void clearRule(const R& r, const P& p) {
        for (const auto& x : r) { this->clearRule(p(x)); }
    }
    template <std::ranges::range R>
    void clearRule(const R& r) {
        clearRule(r, [](auto x) { return Potassco::atom(x); });
    }
    void clearBody(LitView body) {
        for (auto p : body) { clearBody(p); }
    }

    [[nodiscard]] constexpr bool allMarked(VarView atoms, uint8_t f) const {
        return std::ranges::all_of(atoms, [&](Var_t v) { return isSet(v, f); });
    }
    [[nodiscard]] constexpr bool inBody(LitView lits) const {
        return std::ranges::all_of(lits, [this](Literal x) { return inBody(x); });
    }

private:
    using StateVec = PodVector_t<uint8_t>;
    void grow(Var_t v) {
        if (v >= state_.size()) {
            state_.resize(v + 1);
        }
    }
    [[nodiscard]] static uint8_t headFlag(PrgEdge t) {
        return t.isAtom() ? (head_flag << static_cast<uint8_t>(t.isChoice())) : disj_flag;
    }
    StateVec state_;
};

//! A head node of a program-dependency graph.
/*!
 * A head node is either an atom or a disjunction
 * and stores its possible supports.
 */
class PrgHead : public PrgNode {
public:
    enum Simplify { no_simplify = 0, force_simplify = 1 };

    //! Is the head part of the (simplified) program?
    [[nodiscard]] bool inUpper() const { return relevant() && upper_ != 0; }
    //! Is this head an atom?
    [[nodiscard]] bool isAtom() const { return isAtom_ != 0; }
    //! Number of supports (rules) for this head.
    [[nodiscard]] uint32_t numSupports() const { return size32(supports_); }
    //! First support for this head or noEdge() if head has no support.
    [[nodiscard]] PrgEdge support() const { return not supports_.empty() ? supports_[0] : PrgEdge::noEdge(); }
    //! Possible supports for this head.
    [[nodiscard]] EdgeSpan supports() const { return supports_; }
    //! External atom (or defined in a later incremental step)?
    [[nodiscard]] bool frozen() const { return freeze_ != static_cast<uint32_t>(freeze_no); }
    //! If frozen(), value to assume during solving.
    [[nodiscard]] Val_t freezeValue() const {
        return static_cast<Val_t>(freeze_ - static_cast<uint32_t>(freeze_ != 0));
    }
    //! If frozen(), literal to assume during solving.
    [[nodiscard]] Literal assumption() const {
        return freeze_ > static_cast<uint32_t>(freeze_free) ? literal() ^ (freeze_ == freeze_false) : lit_true;
    }
    //! Adds r as support edge for this node.
    void addSupport(PrgEdge r) { addSupport(r, force_simplify); }
    void addSupport(PrgEdge r, Simplify s);
    //! Removes r from the head's list of supports.
    void removeSupport(PrgEdge r);
    void clearSupports();
    void clearSupports(EdgeVec& to) {
        to.swap(supports_);
        clearSupports();
    }
    //! Removes any superfluous/irrelevant supports.
    bool simplifySupports(LogicProgram& prg, bool strong, uint32_t* numDiffSupps = nullptr);
    //! Assigns the value v to this head.
    bool assignValue(Val_t v) { return assignValueImpl(v, ignoreScc() && not frozen()); }
    /*!
     * \name implementation functions
     * Low-level implementation functions. Use with care and only if you
     * know what you are doing!
     */
    //@{
    void                   setInUpper(bool b) { upper_ = static_cast<uint32_t>(b); }
    void                   markDirty() { dirty_ = 1; }
    void                   assignVar(LogicProgram& prg, PrgEdge it, bool allowEq = true);
    [[nodiscard]] NodeType nodeType() const { return isAtom() ? PrgNode::atom : PrgNode::disj; }
    //@}
protected:
    enum FreezeState { freeze_no = 0u, freeze_free = 1u, freeze_true = 2u, freeze_false = 3u };
    //! Creates a new node that corresponds to a literal that is false.
    explicit PrgHead(uint32_t id, NodeType t, uint32_t data = 0, bool checkScc = true);
    bool     backpropagate(LogicProgram& prg, Val_t val, bool bpFull);
    EdgeVec  supports_;    // possible supports (body or disjunction)
    uint32_t data_   : 27; // number of atoms in disjunction or scc of atom
    uint32_t upper_  : 1;  // in (simplified) program?
    uint32_t dirty_  : 1;  // is list of supports dirty?
    uint32_t freeze_ : 2;  // incremental freeze state
    uint32_t isAtom_ : 1;  // is this head an atom?
};

//! An atom in a logic program.
/*!
 * An atom stores the list of bodies depending on it.
 * Furthermore, once strongly-connected components are identified,
 * atoms store their SCC-number. All trivial SCCs are represented
 * with the special SCC-number PrgNode::noScc.
 */
class PrgAtom : public PrgHead {
public:
    enum Dependency { dep_pos = 0, dep_neg = 1, dep_all = 2 };
    using DepSpan = LitView;

    explicit PrgAtom(uint32_t id, bool checkScc = true);
    [[nodiscard]] static constexpr NodeType nodeType() { return PrgNode::atom; }
    //! Strongly connected component of this node.
    [[nodiscard]] uint32_t scc() const { return data_; }
    //! If eq(), stores the literal that is eq to this atom.
    [[nodiscard]] Literal eqGoal(bool sign) const;
    //! Returns true if atom belongs to a disjunctive head.
    [[nodiscard]] bool inDisj() const;
    /*!
     * \name forward dependencies (bodies containing this atom)
     */
    //@{
    [[nodiscard]] DepSpan deps() const { return deps_; }
    [[nodiscard]] bool    hasDep(Dependency d) const;
    void                  addDep(Id_t bodyId, bool pos);
    void                  removeDep(Id_t bodyId, bool pos);
    void                  clearDeps(Dependency d);
    //@}

    /*!
     * \name implementation functions
     * Low-level implementation functions. Use with care and only if you
     * know what you are doing!
     */
    //@{
    void setEqGoal(Literal x);
    bool propagateValue(LogicProgram& prg, bool backprop);
    bool addConstraints(const LogicProgram& prg, ClauseCreator& c);
    void setScc(uint32_t scc) { data_ = scc; }
    void markFrozen(Val_t v) { freeze_ = v + freeze_free; }
    void clearFrozen() {
        freeze_ = freeze_no;
        markDirty();
    }
    //@}
private:
    LitVec deps_; // bodies depending on this atom
};

//! A (rule) body in a logic program.
class PrgBody : public PrgNode {
public:
    using GoalSpan = LitView;

    //! Creates a new body node and (optionally) connects it to its predecessors (i.e. atoms).
    /*!
     * \param prg     The program in which the new body is used.
     * \param id      The id for the new body node.
     * \param rule    The rule for which a body node is to be created.
     * \param pos     Positive body size.
     * \param addDeps If true, add an edge between each atom subgoal and the new node.
     */
    static PrgBody* create(const LogicProgram& prg, uint32_t id, const Rule& rule, uint32_t pos, bool addDeps);
    //! Destroys a body node created via create().
    void                   destroy();
    [[nodiscard]] BodyType type() const { return static_cast<BodyType>(type_); }
    //! Returns the number of atoms in the body.
    [[nodiscard]] uint32_t size() const { return size_; }
    [[nodiscard]] bool     noScc() const { return size() == 0 || goal(0).sign(); }
    //! Returns the bound of this body, or size() if the body is a normal body.
    [[nodiscard]] Weight_t bound() const {
        if (type() == BodyType::normal) {
            return static_cast<Weight_t>(size());
        }
        return hasWeights() ? sumData()->bound : aggData().bound;
    }
    //! Returns the sum of the subgoals weights, or size() if the body is not a sum with weights.
    [[nodiscard]] Weight_t sumW() const { return not hasWeights() ? static_cast<Weight_t>(size()) : sumData()->sumW; }
    //! Returns the idx-th subgoal as a literal.
    [[nodiscard]] Literal goal(uint32_t idx) const {
        assert(idx < size());
        return *(lits() + idx);
    }
    //! Returns the weight of the idx-th subgoal.
    [[nodiscard]] Weight_t weight(uint32_t idx) const {
        assert(idx < size());
        return not hasWeights() ? 1 : sumData()->weights[idx];
    }
    //! Returns true if the body node is supported.
    /*!
     * A normal body is supported, iff all of its positive subgoals are supported.
     * A count/sum body is supported if the sum of the weights of the supported positive +
     * the sum of the negative weights is >= lowerBound().
     */
    [[nodiscard]] bool isSupported() const { return unsupp_ <= 0; }
    //! Returns true if this body defines any head.
    [[nodiscard]] bool hasHeads() const { return isSmallHead() ? head_ != 0 : not largeHead()->empty(); }
    [[nodiscard]] bool inRule() const { return hasHeads() || freeze_; }

    [[nodiscard]] EdgeSpan heads() const { return isSmallHead() ? EdgeSpan{smallHead(), head_} : *largeHead(); }
    [[nodiscard]] GoalSpan goals() const { return {lits(), size()}; }
    //! Adds a rule edge between this body and the given head.
    /*!
     * \note
     *   The function also adds a corresponding back edge to the head.
     * \note
     *   Adding a head invalidates the set property for the heads of this body.
     *   To restore it, call simplifyHeads()
     */
    void addHead(PrgHead* h, EdgeType t);
    //! Simplifies the heads of this body and establishes set property.
    /*!
     * Removes superfluous heads and sets the body to false if for some atom 'a'
     * in the head of this body 'B', Ta -> FB. In that case, all heads atoms are removed, because
     * a false body can't define any atom.
     * If strong is true, removes head atoms that are not associated with a variable.
     * \return
     *    setValue(value_false) if setting a head of this body to true would
     *    make the body false (i.e. the body is a selfblocker). Otherwise, true.
     */
    bool simplifyHeads(LogicProgram& prg, bool strong);
    bool mergeHeads(LogicProgram& prg, PrgBody& heads, bool strong, bool simplify = true);
    void removeHead(PrgHead* h, EdgeType t);
    bool hasHead(const PrgHead* h, EdgeType t) const;
    //! Simplifies the body, i.e. its predecessors-lists.
    /*!
     * - removes true/false atoms from B+/B- resp.
     * - removes/merges duplicate subgoals
     * - checks whether body must be false (e.g. contains false/true atoms in B+/B- resp. or contains p and ~p)
     *
     * \pre prg.getBody(id()) == this
     *
     * \param[in] prg    The program containing this body.
     * \param[in] strong If true, treats atoms that have no variable associated as false.
     * \param[out] eqId  The id of a body in prg that is equivalent to this body.
     *
     * \return
     *  - true if simplification was successful
     *  - false if simplification detected a conflict
     */
    bool simplifyBody(LogicProgram& prg, bool strong, uint32_t* eqId = nullptr);
    //! Calls simplifyBody() and/or simplifyHeads() if necessary.
    bool simplify(LogicProgram& prg, bool strong, uint32_t* eqId = nullptr) {
        return simplifyBody(prg, strong, eqId) && simplifyHeads(prg, strong);
    }
    bool toData(const LogicProgram& prg, Potassco::RuleBuilder& out) const;
    //! Notifies the body node about the fact that its positive subgoal v is supported.
    /*!
     * \return true if the body is now also supported, false otherwise.
     */
    bool propagateSupported(Var_t /* v */);
    //! Propagates the assignment of subgoal p.
    bool propagateAssigned(LogicProgram& prg, Literal p, Val_t v);
    //! Propagates the assignment of a head.
    bool propagateAssigned(LogicProgram& prg, const PrgHead* h, EdgeType t);
    //! Propagates the value of this body.
    bool                   propagateValue(LogicProgram& prg, bool backprop);
    bool                   propagateValue(LogicProgram& prg);
    bool                   addConstraints(const LogicProgram& prg, ClauseCreator& c);
    void                   markDirty() { sBody_ = 1; }
    void                   markHeadsDirty() { sHead_ = 1; }
    void                   markFrozen() { freeze_ = 1; }
    void                   clearHeads();
    bool                   resetSupported();
    void                   assignVar(LogicProgram& prg);
    bool                   assignValue(Val_t v) { return assignValueImpl(v, noScc()); }
    [[nodiscard]] uint32_t scc(const LogicProgram& prg) const;
    [[nodiscard]] bool     hasWeights() const { return type() == BodyType::sum; }
    void                   clearRule(AtomState& rs) const {
        std::ranges::for_each(heads(), [&rs](PrgEdge e) { rs.clearRule(e.node()); });
        std::ranges::for_each(goals(), [&rs](Literal p) { rs.clearRule(p.var()); });
    }
    [[nodiscard]] static constexpr NodeType nodeType() { return PrgNode::body; }

private:
    static constexpr uint32_t max_size = (1u << 25) - 1;
    POTASSCO_WARNING_BEGIN_RELAXED
    struct SumData {
        static SumData* create(uint32_t size, Weight_t bnd, Weight_t ws);
        void            destroy();
        Weight_t        bound;
        Weight_t        sumW;
        Weight_t        weights[0];
    };
    struct Agg {
        union {
            SumData* sum{};
            Weight_t bound;
        };
        Literal lits[0];
    };
    struct Norm {
        Literal lits[0];
    };
    PrgBody(uint32_t id, const LogicProgram& prg, Potassco::LitSpan lits, uint32_t pos, bool addDeps);
    PrgBody(uint32_t id, const LogicProgram& prg, const Potassco::Sum& sum, bool hasWeights, uint32_t pos,
            bool addDeps);
    PrgBody(uint32_t id, BodyType, uint32_t sz);
    ~PrgBody();
    [[nodiscard]] uint32_t findLit(const LogicProgram& prg, Literal p) const;
    bool normalize(const LogicProgram& prg, Weight_t bound, Weight_t sumW, Weight_t reachW, uint32_t& hashOut);
    void prepareSimplifyHeads(const LogicProgram& prg, AtomState& rs);
    bool simplifyHeadsImpl(const LogicProgram& prg, PrgBody& target, AtomState& rs, bool strong);
    bool superfluousHead(const LogicProgram& prg, const PrgHead* head, PrgEdge it, const AtomState& rs) const;
    [[nodiscard]] bool blockedHead(PrgEdge it, const AtomState& rs) const;
    void               addHead(PrgEdge h);
    bool               eraseHead(PrgEdge h);
    [[nodiscard]] bool isSmallHead() const { return head_ != 3u; }
    template <typename T>
    [[nodiscard]] T* data() const {
        return reinterpret_cast<T*>(const_cast<char*>(data_));
    }
    [[nodiscard]] PrgEdge* smallHead() const { return const_cast<PrgEdge*>(headData_.sm); }
    [[nodiscard]] EdgeVec* largeHead() const { return headData_.ext; }
    [[nodiscard]] SumData* sumData() const { return aggData().sum; }
    [[nodiscard]] Agg&     aggData() const { return *data<Agg>(); }
    [[nodiscard]] Literal* lits() const { return type() == BodyType::normal ? data<Norm>()->lits : data<Agg>()->lits; }

    uint32_t size_   : 25; // |B|
    uint32_t head_   : 2;  // simple or extended head?
    uint32_t type_   : 2;  // body type
    uint32_t sBody_  : 1;  // simplify body?
    uint32_t sHead_  : 1;  // simplify head?
    uint32_t freeze_ : 1;  // keep body even if it does not occur in a rule?
    Weight_t unsupp_;      // <= 0 -> body is supported
    union Head {
        PrgEdge  sm[2];
        EdgeVec* ext;
    } headData_;   // successors of this body
    char data_[0]; // empty or one of Agg|Norm
    POTASSCO_WARNING_END_RELAXED
};
//! The head of a disjunctive rule.
class PrgDisj : public PrgHead {
public:
    using AtomSpan = VarView;
    //! Constructor for disjunctions.
    static PrgDisj* create(uint32_t id, Potassco::AtomSpan head);
    //! Destroys a disjunction created via create().
    void destroy();
    void detach(const LogicProgram& prg, bool full = true);
    //! Number of atoms in disjunction.
    [[nodiscard]] uint32_t size() const { return data_; }
    [[nodiscard]] AtomSpan atoms() const { return {atoms_, size()}; }
    //! Propagates the assignment of an atom in this disjunction.
    bool propagateAssigned(const LogicProgram& prg, PrgHead* at, EdgeType t);

private:
    explicit PrgDisj(uint32_t id, Potassco::AtomSpan head);
    ~PrgDisj();
    POTASSCO_WARNING_BEGIN_RELAXED
    Atom_t atoms_[0]; // atoms in disjunction
    POTASSCO_WARNING_END_RELAXED
};

constexpr Val_t getMergeValue(const PrgNode* lhs, const PrgNode* rhs) {
    return static_cast<Val_t>(std::min(static_cast<Val_t>(lhs->value() - 1), static_cast<Val_t>(rhs->value() - 1)) + 1);
}

template <typename NodeT>
bool mergeValue(NodeT* lhs, NodeT* rhs) {
    auto mv = getMergeValue(lhs, rhs);
    return (lhs->value() == mv || lhs->assignValue(mv)) && (rhs->value() == mv || rhs->assignValue(mv));
}
template <std::derived_from<PrgNode> To, std::derived_from<PrgNode> From>
constexpr auto node_cast(From* node) -> std::conditional_t<std::is_const_v<From>, const To*, To*> {
    using P = std::conditional_t<std::is_const_v<From>, const To*, To*>;
    if constexpr (std::is_same_v<std::decay_t<From>, PrgHead>) {
        static_assert(std::is_same_v<To, PrgAtom> || std::is_same_v<To, PrgDisj>);
        assert(node->isAtom() == (std::is_same_v<To, PrgAtom>) );
    }
    return static_cast<P>(node);
}
template <std::derived_from<PrgNode> To, typename From>
requires(std::is_pointer_v<From> && std::derived_from<std::remove_pointer_t<From>, To>)
constexpr auto node_cast(std::span<From> in) -> std::span<std::conditional_t<std::is_const_v<From>, To* const, To*>> {
    using P = std::add_pointer_t<std::conditional_t<std::is_const_v<From>, To* const, To*>>;
    return {reinterpret_cast<P>(in.data()), in.size()};
}

//! A class for computing strongly connected components of the positive atom-body dependency graph.
class SccChecker {
public:
    SccChecker(LogicProgram& prg, AtomList& sccAtoms, uint32_t startScc);
    [[nodiscard]] uint32_t sccs() const { return sccs_; }

private:
    struct Call {
        uintptr_t node;
        uint32_t  min;
        uint32_t  next;
    };
    using CallStack = PodVector_t<Call>;
    using NodeStack = PodVector_t<uintptr_t>;
    static uintptr_t packNode(PrgNode* n, NodeType t) {
        return reinterpret_cast<uintptr_t>(n) + static_cast<uintptr_t>(t);
    }
    static PrgNode* unpackNode(uintptr_t n) { return reinterpret_cast<PrgNode*>(n & ~static_cast<uintptr_t>(3u)); }
    static bool     isNode(uintptr_t n, NodeType t) { return (n & 3u) == static_cast<uintptr_t>(t); }
    static bool     doVisit(const PrgNode* n, bool seen = true) {
        return not n->ignoreScc() && n->relevant() && n->hasVar() && (not seen || not n->seen());
    }
    void visitDfs(PrgNode* n, NodeType t);
    bool recurse(Call& c);
    bool onNode(PrgNode* n, NodeType t, Call& c, uint32_t data);
    void addCall(PrgNode* n, NodeType t, uint32_t next, uint32_t min = 0) {
        callStack_.push_back({.node = packNode(n, t), .min = min, .next = next});
    }
    CallStack     callStack_;
    NodeStack     nodeStack_;
    LogicProgram* prg_;
    AtomList*     sccAtoms_;
    uint32_t      count_;
    uint32_t      sccs_;
};
//! A set of ids of strongly connected components having at least one head-cycle.
struct NonHcfSet : private PodVector_t<uint32_t> {
    using base_type      = PodVector_t<uint32_t>;     // NOLINT
    using const_iterator = base_type::const_iterator; // NOLINT
    using base_type::begin;
    using base_type::empty;
    using base_type::end;
    using base_type::size;
    NonHcfSet() = default;
    void add(uint32_t scc) {
        if (auto it = std::ranges::lower_bound(*this, scc); it == end() || *it != scc) {
            insert(it, scc);
        }
    }
    [[nodiscard]] bool find(uint32_t scc) const {
        auto it = std::ranges::lower_bound(*this, scc);
        return it != end() && *it == scc;
    }
    [[nodiscard]] auto view(std::size_t offset) const -> SpanView<uint32_t> {
        return drop(static_cast<const base_type&>(*this), offset);
    }
    Configuration* config{nullptr};
};
//@}
} // namespace Asp
} // namespace Clasp
