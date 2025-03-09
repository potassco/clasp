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

#include <clasp/constraint.h>
#include <clasp/dependency_graph.h>
#include <clasp/literal.h>
#include <clasp/solver.h>
namespace Clasp {
class LoopFormula;

//! Clasp's default unfounded set checker.
/*!
 * \ingroup propagator
 * Searches for unfounded atoms by checking the positive dependency graph (PDG)
 *
 * Basic Idea:
 *  - For each (non-false) atom 'a', let source(a) be a body B in body(a) that provides an external support for 'a'
 *    - If no such B exists, 'a' must be false
 *  - If source(a) becomes false and 'a' is not false:
 *    - Let Q = {};
 *    - add 'a' to Q
 *    - For each B' s.th B' is not external to Q
 *      - add { a' | source(a') = B } to Q
 *  - Try to find new sources for all atoms 'a' in Q
 */
class DefaultUnfoundedCheck : public PostPropagator {
public:
    using DependencyGraph = Asp::PrgDepGraph;
    using NodeId          = DependencyGraph::NodeId;
    using BodyNode        = DependencyGraph::BodyNode;
    using AtomNode        = DependencyGraph::AtomNode;
    using ConstGraphPtr   = const DependencyGraph*;
    using GraphPtr        = DependencyGraph*;
    //! Defines the supported reasons for explaining assignments.
    enum ReasonStrategy {
        common_reason = 0, /*!< one reason for each unfounded set but one clause for each atom */
        only_reason   = 1, /*!< store only the reason but don't learn a nogood */
        distinct_reason,   /*!< distinct reason and clause for each unfounded atom */
        shared_reason,     /*!< one shared loop formula for each unfounded set */
        no_reason,         /*!< do no compute reasons for unfounded sets (only valid if learning is disabled!) */
    };

    explicit DefaultUnfoundedCheck(DependencyGraph& graph, ReasonStrategy st = common_reason);
    ~DefaultUnfoundedCheck() override;
    DefaultUnfoundedCheck(DefaultUnfoundedCheck&&) = delete;

    [[nodiscard]] ReasonStrategy reasonStrategy() const { return strategy_; }
    void                         setReasonStrategy(ReasonStrategy rs);

    [[nodiscard]] ConstGraphPtr graph() const { return graph_; }
    [[nodiscard]] uint32_t      nodes() const { return size32(atoms_) + size32(bodies_); }

    // base interface
    [[nodiscard]] uint32_t priority() const override { return priority_reserved_ufs; }
    bool                   init(Solver&) override;
    void                   reset() override;
    bool                   propagateFixpoint(Solver& s, PostPropagator* ctx) override;
    bool                   isModel(Solver& s) override;
    bool                   valid(Solver& s) override;
    bool                   simplify(Solver& s, bool) override;
    void                   destroy(Solver* s, bool detach) override;

private:
    enum UfsType { ufs_none, ufs_poly, ufs_non_poly };
    enum WatchType : uint32_t {
        watch_source_false  = 0,
        watch_head_false    = 1,
        watch_head_true     = 2,
        watch_subgoal_false = 3,
    };
    // data for each body
    struct BodyData {
        uint32_t watches : 31 {0}; // how many atoms watch this body as source?
        uint32_t picked  : 1 {0};  // flag used in computeReason()
        uint32_t lowerOrExt{0};    // unsourced preds or index of extended body
    };
    struct BodyPtr {
        constexpr BodyPtr(const BodyNode* n, uint32_t i) : node(n), id(i) {}
        const BodyNode* node;
        uint32_t        id;
    };
    // data for extended bodies
    struct ExtData {
        using SetType = Potassco::Bitset<uint32_t>;
        [[nodiscard]] static constexpr uint32_t word(uint32_t idx) { return idx / 32; }
        [[nodiscard]] static constexpr uint32_t pos(uint32_t idx) { return idx & 31; }
        [[nodiscard]] constexpr bool            inWs(uint32_t idx) const { return flags[word(idx)].contains(pos(idx)); }

        constexpr bool addToWs(uint32_t idx, Weight_t w) {
            auto r = flags[word(idx)].add(pos(idx));
            POTASSCO_DEBUG_ASSERT(r);
            static_cast<void>(r);
            return (lower -= w) <= 0;
        }
        constexpr void removeFromWs(uint32_t idx, Weight_t w) {
            if (flags[word(idx)].remove(pos(idx))) {
                lower += w;
            }
        }
        Weight_t lower{};
        Weight_t slack{};
        POTASSCO_WARNING_BEGIN_RELAXED
        SetType flags[0];
        POTASSCO_WARNING_END_RELAXED
    };
    // data for each atom
    struct AtomData {
        static constexpr uint32_t nil_source = (static_cast<uint32_t>(1) << 29) - 1;
        // returns the body that is currently watched as possible source
        [[nodiscard]] constexpr NodeId watch() const { return source; }
        // returns true if atom has currently a source, i.e. a body that can still define it
        [[nodiscard]] constexpr bool hasSource() const { return validS; }
        // mark source as invalid but keep the watch
        constexpr void markSourceInvalid() { validS = 0; }
        // restore validity of source
        constexpr void resurrectSource() { validS = 1; }
        // sets b as source for this atom
        constexpr void setSource(NodeId b) {
            source = b;
            validS = 1;
        }

        uint32_t source : 29 {nil_source}; // id of body currently watched as source
        uint32_t todo   : 1 {0};           // in todo-queue?
        uint32_t ufs    : 1 {0};           // in ufs-queue?
        uint32_t validS : 1 {0};           // is source valid?
    };
    // Watch-structure used to update extended bodies affected by literal assignments
    struct ExtWatch {
        NodeId   bodyId;
        uint32_t data;
    };
    // Minimality checker for disjunctive logic programs.
    struct MinimalityCheck {
        using FwdCheck = SolveParams::FwdCheck;
        explicit MinimalityCheck(const FwdCheck& fwd);
        bool     partialCheck(uint32_t level);
        void     schedNext(uint32_t level, bool ok);
        FwdCheck fwd;
        uint32_t high;
        uint32_t low;
        uint32_t next;
        uint32_t scc;
    };
    // -------------------------------------------------------------------------------------------
    // constraint interface
    PropResult propagate(Solver&, Literal, uint32_t& data) override {
        uint32_t index = data >> 2;
        uint32_t type  = (data & 3u);
        if (type != watch_source_false || bodies_[index].watches) {
            invalid_.push_back(data);
        }
        return PropResult(true, true);
    }
    void reason(Solver& s, Literal, LitVec&) override;
    // -------------------------------------------------------------------------------------------
    // initialization
    [[nodiscard]] BodyPtr getBody(NodeId bId) const { return {&graph_->getBody(bId), bId}; }
    void                  initBody(const BodyPtr& n);
    void                  initExtBody(const BodyPtr& n);
    void                  initSuccessors(const BodyPtr& n, Weight_t lower);
    void                  addWatch(Literal, uint32_t data, WatchType type);
    void                  addExtWatch(Literal p, const BodyPtr& n, uint32_t data);
    // -------------------------------------------------------------------------------------------
    // propagating source pointers
    void propagateSource();
    void addSource(const AtomNode& atom);
    void removeSource(const AtomNode& atom, bool addTodo);
    void setSource(NodeId atom, const BodyPtr& b);
    void removeSource(NodeId bodyId);
    void forwardSource(const BodyPtr& n);
    void forwardUnsource(const BodyPtr& n, bool add);
    void updateSource(AtomData& atom, const BodyPtr& n);
    // -------------------------------------------------------------------------------------------
    // finding & propagating unfounded sets
    void    updateAssignment(const Solver& s);
    bool    findSource(NodeId atom);
    bool    isValidSource(const BodyPtr&);
    void    addUnsourced(const BodyPtr&);
    bool    falsifyUfs(UfsType t);
    bool    assertAtom(Literal a, UfsType t);
    void    computeReason(UfsType t);
    void    addIfReason(const BodyPtr&, uint32_t uScc);
    bool    isExternal(const BodyPtr&, Weight_t& slack) const;
    void    addDeltaReason(const BodyPtr& body, uint32_t uScc);
    void    addReasonLit(Literal);
    void    createLoopFormula();
    UfsType findUfs(Solver& s, bool checkNonHcf);
    UfsType findNonHcfUfs(Solver& s);
    // -------------------------------------------------------------------------------------------
    bool pushTodo(NodeId at) { return atoms_[at].todo == 0 && (todo_.push(at), atoms_[at].todo = 1, true); }
    bool pushUfs(NodeId at) { return atoms_[at].ufs == 0 && (ufs_.push(at), atoms_[at].ufs = 1, true); }
    void resetTodo() {
        while (not todo_.empty()) { atoms_[todo_.pop_ret()].todo = 0; }
        todo_.clear();
    }
    void resetUfs() {
        while (not ufs_.empty()) { atoms_[ufs_.pop_ret()].ufs = 0; }
        ufs_.clear();
    }
    // -------------------------------------------------------------------------------------------
    using AtomVec   = PodVector_t<AtomData>;
    using BodyVec   = PodVector_t<BodyData>;
    using ExtVec    = PodVector_t<ExtData*>;
    using WatchVec  = PodVector_t<ExtWatch>;
    using IdQueue   = PodQueue<NodeId>;
    using MiniPtr   = std::unique_ptr<MinimalityCheck>;
    using ReasonPtr = std::unique_ptr<LitVec[]>;
    // -------------------------------------------------------------------------------------------
    Solver*        solver_;       // my solver
    GraphPtr       graph_;        // PBADG
    MiniPtr        mini_;         // minimality checker (only for DLPs)
    AtomVec        atoms_;        // data for each atom
    BodyVec        bodies_;       // data for each body
    IdQueue        todo_;         // ids of atoms that recently lost their source
    IdQueue        ufs_;          // ids of atoms that are unfounded wrt the current assignment (limited to one scc)
    IdQueue        sourceQ_;      // source-pointer propagation queue
    VarVec         invalid_;      // ids of invalid elements to be processed
    ExtVec         extended_;     // data for each extended body
    WatchVec       watches_;      // watches for handling choice-, cardinality- and weight rules
    VarVec         pickedExt_;    // extended bodies visited during reason computation
    LitVec         loopAtoms_;    // only used if strategy_ == shared_reason
    LitVec         activeClause_; // activeClause_[0] is the current unfounded atom
    ReasonPtr      reasons_;      // only used if strategy_ == only_reason. reasons_[v] reason why v is unfounded
    ConstraintInfo info_;         // info on active clause
    ReasonStrategy strategy_;     // what kind of reasons to compute?
};
} // namespace Clasp
