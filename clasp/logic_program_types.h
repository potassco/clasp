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
    static constexpr uint32_t scc_not_set = (1u << 27u) - 1; //!< Scc not (yet) set/known.
    static constexpr uint32_t scc_triv    = (1u << 27u) - 2; //!< Trivial scc, i.e., not strongly connected.
    static constexpr uint32_t no_node     = (1u << 28u) - 1;
    static constexpr uint32_t no_lit      = 1;
    //! Creates a new node that corresponds to a literal that is false.
    constexpr explicit PrgNode(uint32_t id, Type t) : isAtom_(t == atom), id_(id) {
        static_assert(sizeof(PrgNode) == sizeof(uint64_t), "Unsupported Alignment");
        POTASSCO_CHECK(id < no_node, EOVERFLOW, "Id out of range");
    }
    PrgNode(const PrgNode&)                    = delete;
    auto operator=(const PrgNode&) -> PrgNode& = delete;
    //! Is this an atom node?
    [[nodiscard]] constexpr bool isAtom() const { return isAtom_ != 0; }
    //! Is the node still relevant or removed() resp. eq()?
    [[nodiscard]] constexpr bool relevant() const { return eq_ == 0; }
    //! Was the node removed?
    [[nodiscard]] constexpr bool removed() const { return eq_ != 0 && id_ == no_node; }
    //! Returns true if this node is equivalent to some other node.
    /*!
     * If eq() is true, the node is no longer relevant and must not be used any further.
     * The only sensible operation is to call id() to get the id of the node
     * that is equivalent to this node.
     */
    [[nodiscard]] constexpr bool eq() const { return eq_ != 0 && id_ != no_node; }
    [[nodiscard]] constexpr bool seen() const { return seen_ != 0; }
    //! Returns true if the node has an associated variable in a solver.
    [[nodiscard]] constexpr bool hasVar() const { return litId_ != no_lit; }
    //! Returns the variable associated with this node or sent_var if no var is associated with this node.
    [[nodiscard]] constexpr auto var() const -> Var_t { return litId_ >> 1u; }
    //! Returns the literal associated with this node or a sentinel literal if no var is associated with this node.
    [[nodiscard]] constexpr auto literal() const -> Literal { return Literal::fromId(litId_); }
    //! Returns the value currently assigned to this node.
    [[nodiscard]] constexpr auto value() const -> Val_t { return val_; }
    //! Returns the current id of this node.
    [[nodiscard]] constexpr auto id() const -> uint32_t { return id_; }
    //! Returns the literal that must be true to fulfill the truth-value of this node.
    [[nodiscard]] constexpr auto trueLit() const -> Literal {
        return value() == value_free ? lit_true : literal() ^ (value() == value_false);
    }

    /*!
     * \name Implementation functions
     * Low-level implementation functions.
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
    uint32_t litId_  : 31 {no_lit}; // literal-id in solver
    uint32_t isAtom_ : 1 {0};       // is this an atom node?
    uint32_t id_     : 28;          // own id/eq-id/root-id/ufs-id
    uint32_t val_    : 2 {0};       // assigned value
    uint32_t eq_     : 1 {0};       // removed or eq to some other node?
    uint32_t seen_   : 1 {0};       // marked as seen?
};
using NodeType = PrgNode::Type;
//! Returns whether `scc` represents a (non-trivial) scc.
constexpr bool isScc(uint32_t scc) { return scc < PrgNode::scc_triv; }

//! An edge of a program-dependency graph.
/*!
 * Currently, clasp distinguishes four types of edges:
 *  - a Normal edge stipulates an implication between body and head,
 *    i.e., tableau-rules FTA and BFA for atoms;
 *  - a Choice edge only stipulates a support;
 *  - a Gamma edge is like a Normal edge that is only considered during
 *    nogood creation but ignored in the dependency graph;
 *  - a GammaChoice edge is like a Gamma edge but only stipulates a support.
 * The head of a rule is either an atom or a disjunction.
 */
struct PrgEdge {
    //! Type of edge.
    enum Type : uint32_t { normal = 0, gamma = 1, choice = 2, gamma_choice = 3 };
    static constexpr auto noEdge() -> PrgEdge { return {UINT32_MAX}; }

    static constexpr auto newEdge(NodeType nt, uint32_t id, Type eType) -> PrgEdge {
        // 28-bit node id, 2-bit node type, 2-bit edge type
        return {(id << 4u) | (Potassco::to_underlying(nt) << 2u) | eType};
    }

    template <typename NodeT>
    static constexpr auto newEdge(const NodeT& n, Type eType) -> PrgEdge {
        return newEdge(n.nodeType(), n.id(), eType);
    }
    //! Returns the id of the adjacent node.
    [[nodiscard]] constexpr auto node() const -> uint32_t { return rep >> 4u; }
    //! Returns the type of this edge.
    [[nodiscard]] constexpr Type type() const { return static_cast<Type>(rep & 3u); }
    //! Returns the type of the adjacent node.
    [[nodiscard]] constexpr auto nodeType() const -> NodeType { return static_cast<NodeType>((rep >> 2u) & 3u); }
    //! Returns true if edge has normal semantic (normal edge or gamma edge).
    [[nodiscard]] constexpr bool isNormal() const { return (rep & 2u) == 0; }
    //! Returns true if the edge has choice semantic.
    [[nodiscard]] constexpr bool isChoice() const { return (rep & 2u) != 0; }
    //! Returns true if the edge is a gamma (aux normal) edge.
    [[nodiscard]] constexpr bool isGamma() const { return (rep & 1u) != 0; }
    //! Returns true if the adjacent node is a body.
    [[nodiscard]] constexpr bool isBody() const { return nodeType() == PrgNode::body; }
    //! Returns true if the adjacent node is an atom.
    [[nodiscard]] constexpr bool isAtom() const { return nodeType() == PrgNode::atom; }
    //! Returns true if the adjacent node is a disjunction.
    [[nodiscard]] constexpr bool isDisj() const { return nodeType() == PrgNode::disj; }
    //! Returns true if the edge is valid, i.e., is not the special "no edge".
    explicit       operator bool() const noexcept { return rep != UINT32_MAX; }
    constexpr bool operator==(const PrgEdge& rhs) const = default;
    constexpr auto operator<=>(const PrgEdge&) const    = default;

    uint32_t rep;
};
static_assert(PrgEdge::newEdge(PrgNode::atom, 10u, PrgEdge::choice) <
              PrgEdge::newEdge(PrgNode::disj, 10u, PrgEdge::normal));

using EdgeType = PrgEdge::Type;
using EdgeVec  = PodVector_t<PrgEdge>;
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
        virtual auto newAtom() -> Atom_t    = 0;
        virtual void addRule(const Rule& r) = 0;

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
    auto transform(const Rule& r, Strategy s = strategy_default) -> uint32_t;

private:
    struct Impl;
    std::unique_ptr<Impl> impl_;
};

//! A set of flags associated with an atom.
class AtomState {
public:
    static constexpr uint8_t pos_flag     = 0x1u;  //!< In positive body of active rule
    static constexpr uint8_t neg_flag     = 0x2u;  //!< In negative body of active rule
    static constexpr uint8_t head_flag    = 0x4u;  //!< In normal head of active rule
    static constexpr uint8_t choice_flag  = 0x8u;  //!< In choice head of active rule
    static constexpr uint8_t disj_flag    = 0x10u; //!< In disjunctive head of active rule
    static constexpr uint8_t rule_mask    = 0x1Fu; //!< In active rule
    static constexpr uint8_t shown_flag   = 0x20u; //!< Atom is shown (sticky)
    static constexpr uint8_t project_flag = 0x40u; //!< Atom is projected (sticky)

    AtomState() = default;
    void reset() noexcept { discardVec(state_); }
    //! Does t.node() appear in the head of the active rule?
    [[nodiscard]] bool inHead(PrgEdge t) const { return isSet(t.node(), headFlag(t)); }
    [[nodiscard]] bool inHead(Atom_t atom) const { return isSet(atom, head_flag); }
    //! Does p appear in the body of the active rule?
    [[nodiscard]] bool inBody(Literal p) const { return isSet(p.var(), pos_flag + p.sign()); }
    [[nodiscard]] bool isSet(Var_t v, uint8_t f) const { return v < state_.size() && Potassco::test_any(state_[v], f); }
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
        Potassco::store_set_mask(state_[v], f);
    }
    void clear(Var_t v, uint8_t f) {
        if (v < state_.size()) {
            Potassco::store_clear_mask(state_[v], f);
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
    [[nodiscard]] static auto headFlag(PrgEdge t) -> uint8_t {
        return t.isAtom() ? (head_flag << static_cast<uint8_t>(t.isChoice())) : disj_flag;
    }
    StateVec state_;
};

//! Dynamic PrgEdge-vector with "small buffer optimization".
/*!
 * \note SboEdgeVec can store up to 2 edges in-place without allocation.
 */
class SboEdgeVec {
public:
    //! Creates an empty edge vector.
    constexpr SboEdgeVec() = default;
    //! Destroys this edge vector and frees any allocated memory.
    constexpr ~SboEdgeVec() {
        if (not isSmall()) {
            Block::release(block());
        }
    }
    //! Steals the contents from other.
    SboEdgeVec(SboEdgeVec&& other) noexcept;
    SboEdgeVec(const SboEdgeVec&) = delete;
    //! Steals the contents from other - must only be called in "moved-from" state.
    void restore(SboEdgeVec&& other);
    //! Returns whether this edge vector is empty.
    [[nodiscard]] constexpr bool empty() const noexcept { return size() == 0u; }
    //! Returns the number of edges in this vector.
    [[nodiscard]] constexpr auto size() const noexcept -> uint32_t { return isSmall() ? smallSize() : block()->size; }
    //! Returns a span over the elements of the vector.
    [[nodiscard]] constexpr auto span() const noexcept -> EdgeSpan {
        return isSmall() ? EdgeSpan{data_, smallSize()} : block()->span();
    }
    [[nodiscard]] constexpr auto span() noexcept -> std::span<PrgEdge> {
        return isSmall() ? std::span{data_, smallSize()} : block()->span();
    }
    //! Returns a pointer to the underlying array.
    [[nodiscard]] constexpr auto data() noexcept -> PrgEdge* { return isSmall() ? data_ : block()->data; }
    [[nodiscard]] constexpr auto data() const noexcept -> const PrgEdge* {
        return const_cast<SboEdgeVec&>(*this).data();
    }
    //! Appends the given edge to this vector and returns its new size.
    constexpr auto push_back(PrgEdge e) -> uint32_t {
        assert(not Potassco::test_mask(e.rep, ptr_mask) || not e);
        if (auto* b = isSmall() ? nullptr : block(); not b && data_[1] == no_edge) {
            auto sz   = static_cast<uint32_t>(data_[0] != no_edge);
            data_[sz] = e;
            return sz + 1;
        }
        else {
            if (not b || b->size == b->cap) {
                b = grow(b);
            }
            b->data[b->size++] = e;
            return b->size;
        }
    }
    //! Removes the last `n` edges from the vector.
    /*!
     * \pre n <= size()
     */
    void pop(uint32_t n = 1);
    //! Removes all elements from the vector and releases any allocated memory.
    void clear();

private:
    // NOTE: We distinguish between small and large states by checking the lowest 4-bits of the first edge (data_[0]).
    //  - 1100 (i.e. invalid NodeType 3u and EdgeType normal) marks the "large" state,
    //  - otherwise, we are in small state, where "no_edge" is used to distinguish between "free" and "used" slots.
    //
    // In the large state, storage of the block-ptr depends on the architectures:
    // On 32-bit architectures, the first slot stores the tag, while the block-ptr is stored in the second slot.
    // On 64-bit, we use the alignment bits of a block-ptr as tag and
    //  - on little-endian: memcpy the ptr in to and out of the two edge slots, or
    //  - otherwise       : store the low and high word of the pointer in the first and second slot, respectively.
    // NOTE: All sane compilers turn the memcpy into a single "mov" instruction at the lowest optimization level.
    static_assert(sizeof(void*) <= sizeof(PrgEdge) * 2, "unsupported platform");
    static constexpr auto no_edge   = PrgEdge::newEdge(static_cast<NodeType>(3u), PrgNode::no_node, PrgEdge::choice);
    static constexpr auto ptr_mask  = 0xCu;
    static constexpr auto ptr_shift = sizeof(uintptr_t) > sizeof(uint32_t) ? 32u : 0u;
    static constexpr auto mem_cpy   = std::endian::native == std::endian::little;

    //! Returns whether the vector is in "small" state.
    [[nodiscard]] constexpr auto isSmall() const noexcept -> bool { return (data_[0].rep & 15u) != ptr_mask; }
    //! Computes the current size of the vector in "small" state.
    [[nodiscard]] constexpr auto smallSize() const noexcept -> uint32_t {
        return data_[0] != no_edge ? 1u + (data_[1] != no_edge) : 0u;
    }
    struct Block {
        [[nodiscard]] constexpr auto span() noexcept -> std::span<PrgEdge> { return {data, size}; }
        static void                  release(Block*);
        //
        uint32_t size{0};
        uint32_t cap{0};
        POTASSCO_WARNING_BEGIN_RELAXED
        PrgEdge data[0];
        POTASSCO_WARNING_END_RELAXED
    };
    //! Returns the block-pointer in "large" state.
    POTASSCO_ATTR_INLINE [[nodiscard]] auto block() const noexcept -> Block* { return load(); }
    //! Extracts the block-ptr from the data_ array.
    template <uint32_t Shift = ptr_shift, bool MemCpy = mem_cpy>
    [[nodiscard]] constexpr auto load() const noexcept -> Block* {
        if constexpr (Shift == 0u) {
            return reinterpret_cast<Block*>(data_[1].rep);
        }
        else {
            uintptr_t ret;
            if constexpr (MemCpy) {
                std::memcpy(&ret, data_, sizeof(uintptr_t));
            }
            else {
                ret = (static_cast<uintptr_t>(data_[1].rep) << Shift) | data_[0].rep;
            }
            return reinterpret_cast<Block*>(Potassco::clear_mask(ret, ptr_mask));
        }
    }
    //! Writes the given block pointer to the data_ array.
    template <uint32_t Shift = ptr_shift, bool MemCpy = mem_cpy>
    constexpr void store(Block* block) noexcept {
        if constexpr (Shift == 0u) {
            data_[0].rep = ptr_mask;
            data_[1].rep = reinterpret_cast<uintptr_t>(block);
        }
        else {
            auto p = reinterpret_cast<uintptr_t>(block) | ptr_mask;
            if constexpr (MemCpy) {
                std::memcpy(data_, &p, sizeof(uintptr_t));
            }
            else {
                data_[0].rep = static_cast<uint32_t>(p);
                data_[1].rep = static_cast<uint32_t>(p >> Shift);
            }
        }
    }
    //! Increases the capacity of this vector.
    auto grow(Block*) -> Block*;

    PrgEdge data_[2] = {no_edge, no_edge};
};

//! A head node of a program-dependency graph.
/*!
 * A head node is either an atom or a disjunction and stores its possible supports.
 */
class PrgHead : public PrgNode {
public:
    enum Simplify { no_simplify = 0, force_simplify = 1 };

    [[nodiscard]] auto nodeType() const -> NodeType { return isAtom() ? atom : disj; }
    //! Is the head part of the (simplified) program?
    [[nodiscard]] bool inUpper() const { return relevant() && upper_ != 0; }
    //! Number of supports (rules) for this head.
    [[nodiscard]] auto numSupports() const -> uint32_t { return supports_.size(); }
    //! First support for this head or noEdge() if the head has no support.
    [[nodiscard]] auto support() const -> PrgEdge { return numSupports() ? *supports_.data() : PrgEdge::noEdge(); }
    //! Possible supports for this head.
    [[nodiscard]] auto supports() const -> EdgeSpan { return supports_.span(); }
    //! Adds r as support edge for this node.
    void addSupport(PrgEdge r, Simplify s = force_simplify);
    //! Removes r from the head's list of supports.
    void removeSupport(PrgEdge r);
    void clearSupports();
    //! Removes any superfluous/irrelevant supports.
    bool simplifySupports(LogicProgram& prg, bool strong, uint32_t* numDiffSupps = nullptr);
    /*!
     * \name Implementation functions
     * Low-level implementation functions.
     */
    //@{
    void setInUpper(bool b) { upper_ = static_cast<uint32_t>(b); }
    void markDirty() { dirty_ = 1; }
    void assignVar(LogicProgram& prg, PrgEdge it, bool allowEq = true);
    //@}
protected:
    enum FreezeState { freeze_no = 0u, freeze_free = 1u, freeze_true = 2u, freeze_false = 3u };
    //! Creates a new node that corresponds to a literal that is false.
    explicit PrgHead(uint32_t id, NodeType t, uint32_t data = 0);
    bool backpropagate(LogicProgram& prg, Val_t val, bool bpFull);

    uint32_t   data_   : 27;     // number of atoms in disjunction or scc of atom
    uint32_t   upper_  : 1 {0};  // in (simplified) program?
    uint32_t   dirty_  : 1 {0};  // is the list of supports dirty?
    uint32_t   freeze_ : 2 {0};  // incremental freeze state
    uint32_t   fact_   : 1 {0};  // atom is a fact
    uint32_t   dom_    : 30 {0}; // associated var for domain heuristic
    uint32_t   unused_ : 2 {0};
    SboEdgeVec supports_; // possible supports (body or disjunction)
};

//! An atom in a logic program.
/*!
 * An atom stores the list of bodies depending on it.
 * Furthermore, once strongly connected components are identified,
 * atoms store their SCC-number. All trivial SCCs are represented
 * with the special SCC-number PrgNode::noScc.
 */
class PrgAtom : public PrgHead {
public:
    enum Dependency { dep_pos = 0, dep_neg = 1, dep_all = 2 };
    using DepSpan = LitView;

    explicit PrgAtom(uint32_t id);
    [[nodiscard]] static constexpr auto nodeType() -> NodeType { return atom; }
    //! Strongly connected component of this atom.
    [[nodiscard]] auto scc() const -> uint32_t { return data_; }
    //! Scc assigned?
    [[nodiscard]] bool hasScc() const { return scc() != scc_not_set; }
    //! Is the atom part of a non-trivial scc?
    [[nodiscard]] bool inScc() const { return scc() < scc_triv; }
    //! If eq(), stores the literal that is eq to this atom.
    [[nodiscard]] auto eqGoal(bool sign) const -> Literal;
    //! Returns true if the atom belongs to a disjunctive head.
    [[nodiscard]] bool inDisj() const;
    //! External atom (or defined in a later incremental step)?
    [[nodiscard]] bool frozen() const { return freeze_ != static_cast<uint32_t>(freeze_no); }
    //! If frozen(), value to assume during solving.
    [[nodiscard]] auto freezeValue() const -> Val_t {
        return static_cast<Val_t>(freeze_ - static_cast<uint32_t>(freeze_ != 0));
    }
    //! If frozen(), literal to assume during solving.
    [[nodiscard]] auto assumption() const -> Literal {
        return freeze_ > static_cast<uint32_t>(freeze_free) ? literal() ^ (freeze_ == freeze_false) : lit_true;
    }
    [[nodiscard]] bool isFact() const { return fact_; }
    [[nodiscard]] auto fixed() const -> Val_t { return value() == value_false ? value_false : value_free + fact_; }
    [[nodiscard]] auto domVar() const -> Var_t { return dom_; }

    /*!
     * \name forward dependencies (bodies containing this atom)
     */
    //@{
    [[nodiscard]] auto deps() const -> DepSpan { return deps_; }
    [[nodiscard]] bool hasDep(Dependency d) const;
    void               addDep(Id_t bodyId, bool pos);
    void               removeDep(Id_t bodyId, bool pos);
    void               clearDeps(Dependency d);
    //@}

    /*!
     * \name Implementation functions
     * Low-level implementation functions.
     */
    //@{
    //! Assigns the value v to this atom.
    bool assignValue(Val_t v) { return assignValueImpl(v, scc() == scc_triv && not frozen()); }
    void setEqGoal(Literal x);
    bool propagateValue(LogicProgram& prg, bool backprop);
    bool addConstraints(const LogicProgram& prg, ClauseCreator& c);
    void setScc(uint32_t scc) { data_ = scc; }
    void markFrozen(Val_t v) { freeze_ = v + freeze_free; }
    void clearFrozen() {
        freeze_ = freeze_no;
        markDirty();
    }
    void setFact(bool b) { fact_ = b; }
    void setDomVar(Var_t v) { dom_ = v; }
    //@}
private:
    LitVec deps_; // bodies depending on this atom
};

//! A (rule) body in a logic program.
class PrgBody : public PrgNode {
public:
    using GoalSpan = LitView;

    //! Creates a new body node and (optionally) connects it to its predecessors (i.e., atoms).
    /*!
     * \param prg     The program in which the new body is used.
     * \param id      The id for the new body node.
     * \param rule    The rule for which a body node is to be created.
     * \param pos     Positive body size.
     * \param addDeps If true, add an edge between each atom subgoal and the new node.
     */
    static auto create(const LogicProgram& prg, uint32_t id, const Rule& rule, uint32_t pos, bool addDeps) -> PrgBody*;
    //! Destroys a body node created via create().
    void               destroy();
    [[nodiscard]] auto type() const -> BodyType { return static_cast<BodyType>(type_); }
    //! Returns the number of atoms in the body.
    [[nodiscard]] auto size() const -> uint32_t { return size_; }
    //! Returns the bound of this body, or size() if the body is a normal body.
    [[nodiscard]] auto bound() const -> Weight_t {
        if (type() == BodyType::normal) {
            return static_cast<Weight_t>(size());
        }
        return hasWeights() ? sumData()->bound : aggData().bound;
    }
    //! Returns the sum of the subgoal weights, or size() if the body is not a sum with weights.
    [[nodiscard]] auto sumW() const -> Weight_t {
        return not hasWeights() ? static_cast<Weight_t>(size()) : sumData()->sumW;
    }
    //! Returns the idx-th subgoal as a literal.
    [[nodiscard]] auto goal(uint32_t idx) const -> Literal {
        assert(idx < size());
        return *(lits() + idx);
    }
    //! Returns the weight of the idx-th subgoal.
    [[nodiscard]] auto weight(uint32_t idx) const -> Weight_t {
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
    [[nodiscard]] bool hasHeads() const { return not heads_.empty(); }
    [[nodiscard]] bool inRule() const { return hasHeads() || freeze_; }

    [[nodiscard]] auto heads() const -> EdgeSpan { return heads_.span(); }
    [[nodiscard]] auto goals() const -> GoalSpan { return {lits(), size()}; }
    [[nodiscard]] bool hasWeights() const { return type() == BodyType::sum; }
    [[nodiscard]] auto scc(const LogicProgram& prg) const -> uint32_t;
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
     * in the head of this body 'B', Ta -> FB. In that case, all head atoms are removed because
     * a false body can't define any atom.
     * If strong is true, removes head atoms that are not associated with a variable.
     * \return
     *    setValue(value_false) if setting a head of this body to true would
     *    make the body false (i.e., the body is a selfblocker). Otherwise, true.
     */
    bool simplifyHeads(LogicProgram& prg, bool strong);
    bool mergeHeads(LogicProgram& prg, PrgBody& heads, bool strong, bool simplify = true);
    enum class BackEdge { keep, remove };
    //! Removes h from the heads of this body and calls h->removeSupport() if `x == BackEdge::remove`.
    void removeHead(PrgHead* h, EdgeType t, BackEdge x = BackEdge::remove);
    bool hasHead(const PrgHead* h, EdgeType t) const;
    //! Simplifies the body, i.e., its predecessors-lists.
    /*!
     * - removes true/false atoms from B+/B- resp.
     * - removes/merges duplicate subgoals
     * - checks whether the body must be false (e.g., contains false/true atoms in B+/B- resp. or contains p and ~p)
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
    bool propagateValue(LogicProgram& prg, bool backprop);
    bool propagateValue(LogicProgram& prg);
    bool addConstraints(const LogicProgram& prg, ClauseCreator& c);
    void markDirty() { sBody_ = 1; }
    void markHeadsDirty() { sHead_ = 1; }
    void markFrozen() { freeze_ = 1; }
    void clearHeads();
    bool resetSupported();
    void assignVar(LogicProgram& prg);
    bool assignValue(Val_t v) { return assignValueImpl(v, noWeak()); }
    void clearRule(AtomState& rs) const {
        std::ranges::for_each(heads(), [&rs](PrgEdge e) { rs.clearRule(e.node()); });
        std::ranges::for_each(goals(), [&rs](Literal p) { rs.clearRule(p.var()); });
    }
    [[nodiscard]] static constexpr auto nodeType() -> NodeType { return body; }

private:
    [[nodiscard]] bool        noWeak() const { return size() == 0 || goal(0).sign(); }
    static constexpr uint32_t max_size = (1u << 27u) - 1;
    POTASSCO_WARNING_BEGIN_RELAXED
    struct SumData {
        static auto create(uint32_t size, Weight_t bnd, Weight_t ws) -> SumData*;
        void        destroy();
        Weight_t    bound;
        Weight_t    sumW;
        Weight_t    weights[0];
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
    [[nodiscard]] auto findLit(const LogicProgram& prg, Literal p) const -> uint32_t;
    bool normalize(const LogicProgram& prg, Weight_t bound, Weight_t sumW, Weight_t reachW, uint32_t& hashOut);
    void prepareSimplifyHeads(const LogicProgram& prg, AtomState& rs);
    bool simplifyHeadsImpl(const LogicProgram& prg, PrgBody& target, AtomState& rs, bool strong);
    bool superfluousHead(const LogicProgram& prg, const PrgHead* head, PrgEdge it, const AtomState& rs) const;
    [[nodiscard]] bool blockedHead(PrgEdge it, const AtomState& rs) const;
    template <typename T>
    [[nodiscard]] T* data() const {
        return reinterpret_cast<T*>(const_cast<char*>(data_));
    }
    [[nodiscard]] auto sumData() const -> SumData* { return aggData().sum; }
    [[nodiscard]] Agg& aggData() const { return *data<Agg>(); }
    [[nodiscard]] auto lits() const -> Literal* {
        return type() == BodyType::normal ? data<Norm>()->lits : data<Agg>()->lits;
    }

    uint32_t   size_   : 27; // |B|
    uint32_t   type_   : 2;  // body type
    uint32_t   sBody_  : 1;  // simplify body?
    uint32_t   sHead_  : 1;  // simplify head?
    uint32_t   freeze_ : 1;  // keep the body even if it does not occur in a rule?
    Weight_t   unsupp_;      // <= 0 -> body is supported
    SboEdgeVec heads_;       // successors of this body
    char       data_[0];     // empty or one of Agg|Norm
    POTASSCO_WARNING_END_RELAXED
};
//! The head of a disjunctive rule.
class PrgDisj : public PrgHead {
public:
    using AtomSpan = VarView;
    //! Constructor for disjunctions.
    static auto create(uint32_t id, Potassco::AtomSpan head) -> PrgDisj*;
    //! Destroys a disjunction created via create().
    void destroy();
    //! Remove edges from atoms and bodies but keep state.
    void disconnect(const LogicProgram& prg);
    //! Number of atoms in disjunction.
    [[nodiscard]] auto size() const -> uint32_t { return data_; }
    [[nodiscard]] auto atoms() const -> AtomSpan { return {atoms_, size()}; }
    //! Propagates the assignment of an atom in this disjunction.
    bool propagateAssigned(const LogicProgram& prg, PrgHead* at, EdgeType t);

private:
    explicit PrgDisj(uint32_t id, Potassco::AtomSpan head);
    ~PrgDisj();
    POTASSCO_WARNING_BEGIN_RELAXED
    Atom_t atoms_[0]; // atoms in disjunction
    POTASSCO_WARNING_END_RELAXED
};

constexpr auto getMergeValue(const PrgNode* lhs, const PrgNode* rhs) -> Val_t {
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
    [[nodiscard]] auto sccs() const -> uint32_t { return sccs_; }

private:
    struct Call {
        uintptr_t node;
        uint32_t  min;
        uint32_t  next;
    };
    using CallStack = PodVector_t<Call>;
    using NodeStack = PodVector_t<uintptr_t>;
    static auto packNode(PrgNode* n, NodeType t) -> uintptr_t {
        return reinterpret_cast<uintptr_t>(n) + static_cast<uintptr_t>(t);
    }
    static auto unpackNode(uintptr_t n) -> PrgNode* {
        return reinterpret_cast<PrgNode*>(n & ~static_cast<uintptr_t>(3u));
    }
    static bool isNode(uintptr_t n, NodeType t) { return (n & 3u) == static_cast<uintptr_t>(t); }
    static bool doVisit(const PrgNode* n, bool seen = true) {
        return n->relevant() && n->hasVar() && (not seen || not n->seen());
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
//@}
} // namespace Asp
} // namespace Clasp
