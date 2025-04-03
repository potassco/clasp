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

#include <clasp/logic_program.h>
#include <clasp/solver_strategies.h>

namespace Clasp {
class Solver;
class SharedContext;
struct SolverStats;
//! Event type used to signal a (partial) check in disjunctive solving.
struct SolveTestEvent : SolveEvent {
    SolveTestEvent(const Solver& s, uint32_t hcc, bool partial);
    int      result;       //!< -1: before test, 0: unstable, 1: stable
    uint32_t hcc     : 31; //!< hcc under test
    uint32_t partial : 1;  //!< partial test?
    uint64_t confDelta;    //!< conflicts before test
    uint64_t choiceDelta;  //!< choices before test
    double   time;         //!< time for test

    [[nodiscard]] uint64_t conflicts() const;
    [[nodiscard]] uint64_t choices() const;
};

namespace Asp {
//! (Positive) Body-Atom-Dependency Graph.
/*!
 * \ingroup shared_con
 *
 * Represents the PBADG of a logic program. Once initialized, the
 * PBADG is static and read-only and thus can be shared between multiple solvers.
 *
 * \note Initialization is *not* thread-safe, i.e. must be done only once by one thread.
 */
class PrgDepGraph {
public:
    enum NonHcfMapType { map_old = 0, map_new = 1 };
    explicit PrgDepGraph(NonHcfMapType m = map_old);
    ~PrgDepGraph();
    PrgDepGraph(PrgDepGraph&&) = delete;

    using NodeId   = uint32_t;
    using NodeSpan = SpanView<NodeId>;
    //! Type for storing a non head-cycle-free component of a disjunctive program.
    class NonHcfComponent {
    public:
        explicit NonHcfComponent(uint32_t id, const PrgDepGraph& dep, SharedContext& generator, Configuration* c,
                                 uint32_t scc, VarView atoms, VarView bodies);
        ~NonHcfComponent();
        NonHcfComponent(NonHcfComponent&&) = delete;

        [[nodiscard]] uint32_t id() const { return id_; }
        [[nodiscard]] uint32_t scc() const { return scc_; }
        [[nodiscard]] auto     ctx() const -> const SharedContext& { return *prg_; }
        [[nodiscard]] bool     simplify(const Solver& generator) const;

        void assumptionsFromAssignment(const Solver& generator, LitVec& assumptionsOut) const;
        bool test(const Solver& generator, LitView assumptions, VarVec& unfoundedOut) const;
        void update(const SharedContext& generator);

    private:
        friend class PrgDepGraph;
        class ComponentMap;
        const PrgDepGraph*             dep_;
        std::unique_ptr<SharedContext> prg_;
        std::unique_ptr<ComponentMap>  comp_;
        uint32_t                       id_;
        uint32_t                       scc_;
    };
    //! A class for storing statistics on checking of non head-cycle-free components.
    class NonHcfStats {
    public:
        NonHcfStats(PrgDepGraph& g, uint32_t level, bool inc);
        ~NonHcfStats();
        NonHcfStats(NonHcfStats&&) = delete;

        void accept(StatsVisitor& out, bool final) const;
        void startStep(uint32_t statsLevel);
        void endStep();
        void addTo(StatsMap& problem, StatsMap& solving, StatsMap* accu) const;

    private:
        friend class PrgDepGraph;
        void addHcc(const NonHcfComponent&);
        void removeHcc(const NonHcfComponent&);
        struct Data;
        PrgDepGraph*          graph_;
        std::unique_ptr<Data> data_;
    };
    using ComponentVec = PodVector_t<NonHcfComponent*>;
    using NonHcfSpan   = SpanView<NonHcfComponent*>;
    //! Base type for nodes.
    struct Node {
        constexpr explicit Node(Literal l = lit_true, uint32_t sc = PrgNode::no_scc) : lit(l), scc(sc), data(0) {}
        Literal  lit;          // literal of this node
        uint32_t scc  : 28;    // scc of this node
        uint32_t data : 4;     // additional atom/body data
        NodeId*  adj{nullptr}; // list of adjacent nodes
        NodeId*  sep{nullptr}; // separates successor/predecessor nodes
    };

    //! Iterator type for iterating over relevant successor/predecessor nodes.
    template <typename DerivedType, unsigned AdjustInc = 0>
    class SentIter {
    public:
        using value_type      = DerivedType;
        using difference_type = std::ptrdiff_t;
        using SmallInt        = std::conditional_t<sizeof(uint32_t) < sizeof(uintptr_t), uint32_t, uint16_t>;

        constexpr DerivedType& operator++() {
            pos += inc;
            advance();
            return static_cast<DerivedType&>(*this);
        }
        constexpr DerivedType operator++(int) {
            DerivedType t(static_cast<const DerivedType&>(*this));
            ++*this;
            return t;
        }
        //! Returns the id of the current successor/predecessor.
        [[nodiscard]] constexpr NodeId id() const { return *pos; }
        //! Returns whether the current successor/predecessor is from a normal rule.
        [[nodiscard]] constexpr bool normal() const { return inExt < 2u; }

        constexpr const value_type& operator*() const { return static_cast<const DerivedType&>(*this); }
        constexpr friend bool operator==(const DerivedType& it, std::default_sentinel_t) { return *it.pos == id_max; }

        struct View {
            template <typename... Args>
            constexpr explicit View(Args&&... args) : it(std::forward<Args>(args)...) {}
            [[nodiscard]] constexpr DerivedType                    begin() const { return it; }
            [[nodiscard]] static constexpr std::default_sentinel_t end() { return std::default_sentinel; }
            DerivedType                                            it;
        };

        const NodeId* pos;
        SmallInt      inc;
        SmallInt      inExt;

    private:
        friend DerivedType;
        constexpr SentIter(const NodeId* p, SmallInt baseInc, bool hasExt)
            : pos(p)
            , inc(baseInc)
            , inExt(static_cast<uint32_t>(hasExt)) {
            advance();
        }
        constexpr void advance() { // private: check if we have to advance from normal to extended part
            if (*pos == id_max && inExt == 1u) {
                inExt = 2u;
                ++pos;
                inc += AdjustInc;
            }
        }
    };

    //! An atom node.
    /*!
     * The PBADG stores a node of type AtomNode for each non-trivially connected atom.
     * The predecessors of an AtomNode are the bodies that define the atom. Its successors
     * are those bodies from the same SCC that contain the atom positively.
     */
    struct AtomNode : Node {
        enum Property : uint32_t {
            property_in_choice  = 1u,
            property_in_disj    = 2u,
            property_in_ext     = 4u,
            property_in_non_hcf = 8u
        };
        constexpr AtomNode() = default;
        constexpr void set(Property p) { data |= static_cast<uint32_t>(p); }
        constexpr void setProperties(uint32_t f) {
            assert(f < 8);
            data |= f;
        }
        //! Contained in the head of a choice rule?
        [[nodiscard]] constexpr bool inChoice() const { return Potassco::test_mask(data, property_in_choice); }
        //! Contained in the head of a non-hcf disjunctive rule?
        [[nodiscard]] constexpr bool inDisjunctive() const { return Potassco::test_mask(data, property_in_disj); }
        //! Contained in an extended body?
        [[nodiscard]] constexpr bool inExtended() const { return Potassco::test_mask(data, property_in_ext); }
        //! Contained in a non-hcf SCC?
        [[nodiscard]] constexpr bool inNonHcf() const { return Potassco::test_mask(data, property_in_non_hcf); }
        //! Bodies (i.e. predecessors): bodies from other SCCs precede those from same SCC.
        [[nodiscard]] constexpr NodeSpan bodies() const { return {adj, sep}; }
        [[nodiscard]] constexpr NodeId   body(uint32_t i) const { return adj[i]; }

        //! Iterator type for iterating over the list of relevant successors (bodies) of an atom.
        /*!
         * \note The list of successors of an atom looks like this:
         *       [B1, ..., Bj, id_max, Ext1, pos1, ..., Extn, posn, id_max], where
         *       each Bi is a normal body,
         *       each Exti is an extended body,
         *       and posi is the position of the atom in Exti.
         *
         * \note The extended part is optional and only exists if the atom appears in at least one extended body.
         */
        struct SuccIt : SentIter<SuccIt, 1> {
            using SentIter::SentIter;
            //! Returns the position of this atom in the extended body with id().
            /*!
             * \pre normal() == false
             */
            [[nodiscard]] constexpr NodeId position() const { return this->pos[1]; }
        };
        //! Returns the relevant successors of this atom, i.e. bodies containing this atom.
        [[nodiscard]] constexpr auto successors() const { return SuccIt::View{sep, 1u, inExtended()}; }
    };
    static constexpr uint32_t sentinel_atom = 0u;

    //! A body node.
    /*!
     * The PBADG stores a node of type BodyNode for each body that defines a non-trivially connected atom.
     * The predecessors of a BodyNode are the body's subgoals.
     * Its successors are the heads that are defined by the body.
     * \note Normal bodies only store the positive subgoals from the same SCC, while
     * extended rule bodies store all subgoals. In the latter case, the positive subgoals from
     * the same SCC are stored as AtomNodes. All other subgoals are stored as literals.
     */
    struct BodyNode : Node {
        enum : uint32_t { flag_has_bound = 1u, flag_has_weights = 2u, flag_has_delta = 4u, flag_seen = 8u };
        constexpr explicit BodyNode(const PrgBody* b, uint32_t ascc) : Node(b->literal(), ascc) {
            assert(scc == ascc && data == 0);
            if (ascc != PrgNode::no_scc && b->type() != BodyType::normal) {
                data = flag_has_bound | (b->type() == BodyType::sum ? flag_has_weights : 0u);
            }
        }
        [[nodiscard]] constexpr bool seen() const { return Potassco::test_mask(data, flag_seen); }
        constexpr void               seen(bool b) {
            if (seen() != b) {
                data = Potassco::toggle_mask(data, flag_seen);
            }
        }

        //! Heads (i.e. successors): atoms from same SCC precede those from other SCCs.
        /*!
         * \note Disjunctive heads are stored in flattened atom-lists, where the
         *       lists are terminated on both ends with the special sentinel atom 0.
         *       E.g. given
         *        x :- B.
         *        y :- B.
         *       a|b:- B.
         *       a|c:- B.
         *       would result in: [x,y,0,a,b,0,0,a,c,0]
         */
        [[nodiscard]] constexpr NodeSpan heads() const { return {adj, sep - extended()}; }
        //! Any disjunctive heads?
        [[nodiscard]] constexpr bool delta() const { return Potassco::test_mask(data, flag_has_delta); }

        //! Iterator type for iterating over the list of relevant predecessor atoms of this body.
        /*!
         * \note The list of predecessors looks like this:
         *       [a1, [w1], ..., aj, [wj], id_max, l1, [w1], ..., lk, [wk], id_max], where
         *       each 'ai' is an atom from the same SCC (normal and extended bodies),
         *       each 'li' is a literal of a subgoal from other SCCs (extended bodies only),
         *       and each 'wi' is an optional weight (only for weight rules).
         *
         * \note The extended part is optional and only exists if this body is an extended body (extended() is true).
         * \note The extended part stores literal representations (not atom node ids).
         */
        struct PredIt : SentIter<PredIt> {
            using SentIter::SentIter;
            //! Returns the weight of the current subgoal.
            [[nodiscard]] constexpr Weight_t weight() const {
                return this->inc == 1 ? 1 : static_cast<Weight_t>(pos[1]);
            }
            //! Returns the literal associated with the current subgoal.
            [[nodiscard]] constexpr Literal lit(const PrgDepGraph& graph) const {
                return normal() ? graph.getAtomLit(*pos) : Literal::fromRep(*pos);
            }
            //! Returns whether the current subgoal is a literal from another scc (extended bodies only).
            [[nodiscard]] constexpr bool ext() const { return not normal(); }
        };

        //! Returns the relevant predecessors of this body.
        [[nodiscard]] constexpr auto predecessors(bool internalOnly = false) const {
            return PredIt::View{sep, 1u + sum(), not internalOnly && extended()};
        }
        //! Number of predecessors (counting external subgoals).
        [[nodiscard]] constexpr uint32_t countPreds() const {
            return scc == PrgNode::no_scc ? 0u : static_cast<uint32_t>(std::ranges::distance(predecessors()));
        }
        //! Returns idx of atomId in predecessors() or id_max if atom is not found.
        [[nodiscard]] constexpr uint32_t findPred(NodeId atomId) const {
            for (uint32_t idx = 0; const auto& x : predecessors(true)) {
                if (x.id() == atomId) {
                    return idx;
                }
                ++idx;
            }
            return id_max;
        }

        //! Weight of ith subgoal.
        /*!
         * \pre i in [0, countPreds())
         */
        [[nodiscard]] constexpr Weight_t predWeight(uint32_t i, bool ext) const {
            return not sum() ? 1 : static_cast<Weight_t>(sep[(i << 1) + (1u + ext)]);
        }
        //! Is the body an extended body?
        [[nodiscard]] constexpr bool extended() const { return Potassco::test_mask(data, flag_has_bound); }
        //! Is the body a sum body?
        [[nodiscard]] constexpr bool sum() const { return Potassco::test_mask(data, flag_has_weights); }
        //! Bound of extended body.
        [[nodiscard]] constexpr Weight_t extBound() const {
            assert(extended());
            const auto* x = sep - 1;
            return static_cast<Weight_t>(*x);
        }
    };
    //! Adds SCCs to the graph.
    /*!
     * \param prg       The logic program for which the dependency graph is to be created.
     * \param sccAtoms  Atoms of the logic program that are strongly connected.
     * \param nonHcfs   Sorted list of non-hcf sccs
     */
    void addSccs(const LogicProgram& prg, const AtomList& sccAtoms, const NonHcfSet& nonHcfs);

    //! Removes inactive non-hcfs.
    void simplify(const Solver& s);
    //! Number of atoms in graph.
    [[nodiscard]] uint32_t numAtoms() const { return size32(atoms_); }
    //! Number of bodies in graph.
    [[nodiscard]] uint32_t numBodies() const { return size32(bodies_); }
    //! Sum of atoms and bodies.
    [[nodiscard]] uint32_t nodes() const { return numAtoms() + numBodies(); }

    //! Returns AtomNode of atom with given id.
    [[nodiscard]] const AtomNode& getAtom(NodeId atomId) const {
        assert(atomId < atoms_.size());
        return atoms_[atomId];
    }
    [[nodiscard]] Literal getAtomLit(NodeId atomId) const { return getAtom(atomId).lit; }
    [[nodiscard]] NodeId  id(const AtomNode& n) const { return static_cast<uint32_t>(&n - atoms_.data()); }
    //! Returns BodyNode of body with given id.
    [[nodiscard]] const BodyNode& getBody(NodeId bodyId) const {
        assert(bodyId < bodies_.size());
        return bodies_[bodyId];
    }

    [[nodiscard]] NonHcfSpan   nonHcfs() const { return components_; }
    [[nodiscard]] uint32_t     numNonHcfs() const { return size32(components_); }
    [[nodiscard]] NonHcfStats* nonHcfStats() const { return stats_.get(); }
    NonHcfStats*               enableNonHcfStats(uint32_t level, bool incremental);

private:
    using AtomVec  = PodVector_t<AtomNode>;
    using BodyVec  = PodVector_t<BodyNode>;
    using StatsPtr = std::unique_ptr<NonHcfStats>;

    [[nodiscard]] auto nonHcfMapType() const -> NonHcfMapType { return static_cast<NonHcfMapType>(mapType_); }
    NodeId             createBody(const PrgBody* b, uint32_t bScc);
    NodeId             createAtom(Literal lit, uint32_t aScc);
    NodeId             addBody(const LogicProgram& prg, PrgBody*);
    NodeId             addDisj(const LogicProgram& prg, PrgDisj*);
    static uint32_t    addHeads(const LogicProgram& prg, const PrgBody*, VarVec& atoms);
    static uint32_t    getAtoms(const LogicProgram& prg, const PrgDisj*, VarVec& atoms);
    static void        addPreds(const LogicProgram& prg, const PrgBody*, uint32_t bScc, VarVec& preds);
    void               initBody(uint32_t id, VarView preds, VarView atHeads);
    void               initAtom(uint32_t id, uint32_t prop, VarView adj, uint32_t preds);
    void               addNonHcf(uint32_t id, SharedContext& ctx, Configuration* c, uint32_t scc);

    AtomVec      atoms_;
    BodyVec      bodies_;
    ComponentVec components_;
    StatsPtr     stats_;
    uint32_t     seenComponents_ : 31;
    uint32_t     mapType_        : 1;
};
} // namespace Asp

//! External dependency graph.
/*!
 * \ingroup shared_con
 *
 * Represents external dependencies explicitly given by the user.
 * For example, via aspif edge directives or the graph block in extended dimacs format.
 * \note Initialization is *not* thread-safe, i.e. must be done only once by one thread.
 */
class ExtDepGraph {
public:
    struct Arc {
        Literal                  lit;
        uint32_t                 node[2];
        [[nodiscard]] uint32_t   tail() const { return node[0]; }
        [[nodiscard]] uint32_t   head() const { return node[1]; }
        [[nodiscard]] const Arc* next() const { return node[0] == (this + 1)->node[0] ? this + 1 : nullptr; }
        static Arc               create(Literal x, uint32_t nodeX, uint32_t nodeY) {
            Arc a = {x, {nodeX, nodeY}};
            return a;
        }
    };
    struct Inv {
        [[nodiscard]] uint32_t   tail() const { return rep >> 1; }
        [[nodiscard]] const Inv* next() const { return (rep & 1u) != 0u ? this + 1 : nullptr; }
        Literal                  lit;
        uint32_t                 rep{};
    };
    template <unsigned X>
    struct CmpArc {
        bool operator()(const Arc& lhs, uint32_t n) const { return lhs.node[X] < n; }
        bool operator()(uint32_t n, const Arc& rhs) const { return n < rhs.node[X]; }
        bool operator()(const Arc& lhs, const Arc& rhs) const {
            return lhs.node[X] < rhs.node[X] || (lhs.node[X] == rhs.node[X] && lhs.node[1 - X] < rhs.node[1 - X]);
        }
    };
    explicit ExtDepGraph(uint32_t numNodeGuess = 0);
    ~ExtDepGraph();
    ExtDepGraph(ExtDepGraph&&) = delete;
    void               addEdge(Literal lit, uint32_t startNode, uint32_t endNode);
    void               update();
    uint32_t           finalize(SharedContext& ctx);
    [[nodiscard]] bool frozen() const;
    uint64_t           attach(Solver& s, Constraint& p, uint64_t genId);
    void               detach(Solver* s, Constraint& p);

    [[nodiscard]] const Arc& arc(uint32_t id) const { return fwdArcs_[id]; }
    [[nodiscard]] const Arc* fwdBegin(uint32_t n) const {
        uint32_t x = nodes_[n].fwdOff;
        return validOff(x) ? &fwdArcs_[x] : nullptr;
    }
    [[nodiscard]] const Inv* invBegin(uint32_t n) const {
        uint32_t x = nodes_[n].invOff;
        return validOff(x) ? &invArcs_[x] : nullptr;
    }
    [[nodiscard]] uint32_t nodes() const { return maxNode_; }
    [[nodiscard]] uint32_t edges() const { return comEdge_; }
    [[nodiscard]] bool     validNode(uint32_t n) const { return n < maxNode_; }

private:
    [[nodiscard]] static constexpr bool validOff(uint32_t n) { return n != UINT32_MAX; }
    struct Node {
        uint32_t fwdOff;
        uint32_t invOff;
    };
    using ArcVec  = PodVector_t<Arc>;
    using InvVec  = PodVector_t<Inv>;
    using NodeVec = PodVector_t<Node>;
    ArcVec   fwdArcs_; // arcs ordered by node id
    InvVec   invArcs_; // inverse arcs ordered by node id
    NodeVec  nodes_;   // data for the nodes of this graph
    uint32_t maxNode_; // nodes have ids in the range [0, maxNode_)
    uint32_t comEdge_; // number of edges committed
    uint32_t genCnt_;  // generation count (for incremental updates)
};

//! Acyclicity checker that operates on a ExtDepGraph.
/*!
 * \ingroup propagator
 * \see M. Gebser, T. Janhunen, and J. Rintanen: "SAT Modulo Graphs: Acyclicity"
 */
class AcyclicityCheck : public PostPropagator {
public:
    enum Strategy {
        prop_full     = 0, // forward and backward check with clause generation
        prop_full_imp = 1, // forward and backward check without clause generation
        prop_fwd      = 2, // only forward check
    };
    static constexpr uint32_t prio = priority_reserved_ufs + 1;
    using DependencyGraph          = ExtDepGraph;
    explicit AcyclicityCheck(DependencyGraph* graph);
    ~AcyclicityCheck() override;
    AcyclicityCheck(AcyclicityCheck&&) = delete;
    void setStrategy(Strategy p);
    void setStrategy(const SolverParams& opts);
    // base interface
    [[nodiscard]] uint32_t priority() const override { return prio; }
    bool                   init(Solver&) override;
    void                   reset() override;
    bool                   propagateFixpoint(Solver& s, PostPropagator* ctx) override;
    bool                   isModel(Solver& s) override;
    bool                   valid(Solver& s) override;
    void                   destroy(Solver* s, bool detach) override;

private:
    struct Parent {
        Literal  lit;
        uint32_t node{};
    };
    static constexpr uint32_t config_bit = 2u;
    struct ReasonStore;
    using Arc       = DependencyGraph::Arc;
    using Inv       = DependencyGraph::Inv;
    using EdgeQueue = PodQueue<Arc>;
    using TagVec    = PodVector_t<uint32_t>;
    using ParentVec = PodVector_t<Parent>;
    using StorePtr  = std::unique_ptr<ReasonStore>;
    bool dfsForward(Solver& s, const Arc& e);
    bool dfsBackward(Solver& s, const Arc& e);
    void setParent(uint32_t node, const Parent& p) { parent_[node] = p; }
    void pushVisit(uint32_t node, uint32_t tv) {
        nStack_.push_back(node);
        tags_[node] = tv;
    }
    [[nodiscard]] bool visited(uint32_t node, uint32_t tv) const { return tags_[node] == tv; }
    uint32_t           startSearch();
    void               addClauseLit(Solver& s, Literal p);
    void               setReason(Literal p, LitView reason);
    // -------------------------------------------------------------------------------------------
    // constraint interface
    PropResult propagate(Solver&, Literal, uint32_t& eId) override {
        todo_.push(graph_->arc(eId));
        return PropResult(true, true);
    }
    void                   reason(Solver& s, Literal, LitVec&) override;
    [[nodiscard]] Strategy strategy() const { return static_cast<Strategy>(strat_ & 3u); }

    DependencyGraph* graph_;   // my graph
    Solver*          solver_;  // my solver
    StorePtr         nogoods_; // stores at most one reason per literal
    uint32_t         strat_;   // active propagation strategy
    uint32_t         tagCnt_;  // generation counter for searches
    EdgeQueue        todo_;    // edges that recently became enabled
    TagVec           tags_;    // tag for each node
    ParentVec        parent_;  // parents for each node
    VarVec           nStack_;  // node stack for df-search
    LitVec           reason_;  // reason for conflict/implication
    uint64_t         genId_;   // generation identifier
};

} // namespace Clasp
