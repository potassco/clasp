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

#include <clasp/claspfwd.h>
#include <clasp/constraint.h>
#include <clasp/literal.h>
#include <clasp/solver_strategies.h>
#include <clasp/util/left_right_sequence.h>

#include <potassco/basic_types.h>
#include <potassco/utils.h>

/*!
 * \file
 * \brief Contains common types shared between different solvers.
 */
namespace Clasp {
class Assignment;
class SharedLiterals;
struct SolverStats;
class StatisticObject;
using PrgDepGraph = Asp::PrgDepGraph;
using DomModType  = Potassco::DomModifier;
/**
 * \defgroup shared SharedContext
 * \brief %SharedContext and related types.
 */

//! Base class for event handlers.
/*!
 * \ingroup shared
 */
class EventHandler : public ModelHandler {
public:
    //! Creates a handler for events with given verbosity or lower.
    explicit EventHandler(Event::Verbosity verbosity = Event::verbosity_quiet);
    EventHandler(const EventHandler&)                    = delete;
    auto operator=(const EventHandler&) -> EventHandler& = delete;

    //! Sets the verbosity for the given event source.
    /*!
     * Events with higher verbosity are not dispatched to this handler.
     */
    void setVerbosity(Event::Subsystem sys, Event::Verbosity verb);
    //! Sets the active event source to sys and dispatches an `EnterEvent` if sys is not yet active.
    bool               setActive(Event::Subsystem sys);
    [[nodiscard]] auto active() const -> Event::Subsystem;
    [[nodiscard]] auto verbosity(Event::Subsystem sys) const -> uint32_t {
        return (static_cast<uint32_t>(verb_) >> (static_cast<uint32_t>(sys) << verb_shift)) & verb_mask;
    }
    //! Calls onEvent(ev) if ev has acceptable verbosity.
    void dispatch(const Event& ev) {
        if (ev.verb <= verbosity(static_cast<Event::Subsystem>(ev.system))) {
            onEvent(ev);
        }
    }
    virtual void onEvent(const Event& /* ev */) {}
    bool         onModel(const Solver&, const Model&) override { return true; }

private:
    static constexpr auto verb_mask  = 15u;
    static constexpr auto verb_shift = 2u;

    uint16_t verb_;
    uint16_t sys_;
};

//! Event type for log or warning messages.
/*!
 * \ingroup shared
 */
struct LogEvent : Event {
    enum Type { message = 'M', warning = 'W' };
    LogEvent(Subsystem sys, Verbosity v, Type t, const Solver* s, const char* what)
        : Event(this, sys, v)
        , solver(s)
        , msg(what) {
        op = static_cast<uint32_t>(t);
    }
    [[nodiscard]] bool isWarning() const { return op == static_cast<uint32_t>(warning); }
    const Solver*      solver;
    const char*        msg;
};

//! Base class for preprocessors working on clauses only.
/*!
 * \ingroup shared
 */
class SatPreprocessor {
public:
    //! A clause class optimized for preprocessing.
    class Clause {
    public:
        static auto newClause(LitView lits) -> Clause*;
        static auto abstractLit(Literal p) -> uint64_t { return static_cast<uint64_t>(1) << ((p.var() - 1) & 63u); }
        [[nodiscard]] auto size() const -> uint32_t { return size_; }
        auto               operator[](uint32_t x) const -> const Literal& { return lits_[x]; }
        [[nodiscard]] bool inQ() const { return inQ_ != 0; }
        [[nodiscard]] auto abstraction() const -> uint64_t { return data_.abstr; }
        [[nodiscard]] auto next() const -> Clause* { return data_.next; }
        [[nodiscard]] bool marked() const { return marked_ != 0; }
        [[nodiscard]] auto lits() const -> LitView { return {lits_, size_}; }
        auto               operator[](uint32_t x) -> Literal& { return lits_[x]; }
        void               setInQ(bool b) { inQ_ = static_cast<uint32_t>(b); }
        void               setMarked(bool b) { marked_ = static_cast<uint32_t>(b); }
        auto               abstraction() -> uint64_t& { return data_.abstr; }
        auto               linkRemoved(Clause* next) -> Clause* {
            data_.next = next;
            return this;
        }
        void strengthen(Literal p);
        void simplify(Solver& s);
        void destroy();
        bool addTo(Solver& s);

    private:
        Clause(const Literal* lits, uint32_t size);
        union {
            uint64_t abstr{}; // abstraction of literals
            Clause*  next;    // next removed clause
        } data_;
        uint32_t size_   : 30; // size of the clause
        uint32_t inQ_    : 1;  // in todo-queue?
        uint32_t marked_ : 1;  // a marker flag
        Literal  lits_[1];     // literals of the clause: [lits_[0], lits_[size_])
    };

    SatPreprocessor();
    virtual ~SatPreprocessor();
    SatPreprocessor(SatPreprocessor&&) = delete;

    //! Creates a clone of this preprocessor.
    /*!
     * \note The function does not clone any clauses already added to *this.
     */
    virtual auto clone() -> SatPreprocessor* = 0;

    [[nodiscard]] auto numClauses() const -> uint32_t { return size32(clauses_); }
    //! Adds a clause to the preprocessor.
    /*!
     * \pre clause is not a tautology (i.e., does not contain both l and ~l)
     * \pre clause is a set (i.e., does not contain l more than once)
     * \return true if `clause` was added; false if adding the clause makes the problem UNSAT
     */
    bool addClause(LitView clause);
    //! Propagates known consequences of the clauses added so far.
    /*!
     * \return false if the preprocessor has found a conflict.
     */
    [[nodiscard]] bool propagate(SharedContext& ctx);
    //! Runs the preprocessor on all clauses that were previously added.
    /*!
     * \pre A ctx.startAddConstraint() was called and has variables for all added clauses.
     */
    bool preprocess(SharedContext& ctx, SatPreParams& opts);
    bool preprocess(SharedContext& ctx);

    //! Extends the model in m with values for any eliminated variables.
    void extendModel(ValueVec& m, LitVec& open);
    struct Stats {
        uint32_t clRemoved{0};
        uint32_t clAdded{0};
        uint32_t litsRemoved{0};
    } stats;
    //! Event type for providing information on preprocessing progress.
    struct Progress : Event {
        enum class EventOp : uint8_t {};
        static constexpr auto event_enter = static_cast<EventOp>('>');
        static constexpr auto event_exit  = static_cast<EventOp>('<');
        Progress(SatPreprocessor* p, EventOp eventOp, uint32_t i, uint32_t m)
            : Event(this, subsystem_prepare, verbosity_high)
            , self(p)
            , cur(i)
            , max(m) {
            op = static_cast<uint32_t>(eventOp);
        }
        SatPreprocessor* self;
        uint32_t         cur;
        uint32_t         max;
    };
    using Options = SatPreParams;

protected:
    using ClauseVec = Vector_t<Clause*>;
    using OwnedPtr  = std::unique_ptr<Clause, DestroyObject>;

    virtual bool initPreprocess(SatPreParams& opts)                    = 0;
    virtual bool doAttachClauses(Range32 clauseRange, bool propagate)  = 0;
    virtual bool doPreprocess()                                        = 0;
    virtual void doExtendModel(Clause* top, ValueVec& m, LitVec& open) = 0;
    virtual void doCleanUp()                                           = 0;

    [[nodiscard]] auto clause(uint32_t clId) -> Clause* { return clauses_[clId]; }
    [[nodiscard]] auto clause(uint32_t clId) const -> const Clause* { return clauses_[clId]; }
    [[nodiscard]] auto ctx() const -> SharedContext& {
        assert(ctx_);
        return *ctx_;
    }
    void reportProgress(Progress::EventOp, uint32_t curr, uint32_t max);

    void setClause(uint32_t clId, LitView cl) { clauses_[clId] = Clause::newClause(cl); }
    void destroyClause(uint32_t clId) {
        clauses_[clId]->destroy();
        clauses_[clId] = nullptr;
        ++stats.clRemoved;
    }
    void eliminateClause(uint32_t id) {
        elimTop_     = clauses_[id]->linkRemoved(elimTop_);
        clauses_[id] = nullptr;
        ++stats.clRemoved;
    }

private:
    bool addUnits();
    void freezeSeen();
    bool attachClauses(bool propagate);
    void discardClauses(Clause* top);

    SharedContext* ctx_;         // current context
    ClauseVec      clauses_;     // initial non-unit clauses
    LitVec         units_;       // initial unit clauses
    Clause*        elimTop_;     // stack of blocked/eliminated clauses
    Range32        seen_;        // vars seen in a previous step
    uint32_t       attached_{0}; // number of clauses already attached
};

///////////////////////////////////////////////////////////////////////////////
// Problem statistics
///////////////////////////////////////////////////////////////////////////////
/*!
 * \addtogroup shared
 * @{
 */
//! A struct for aggregating basic problem statistics.
struct ProblemStats {
    constexpr ProblemStats() = default;
    struct {
        uint32_t num, eliminated, frozen;
    } vars{};
    struct {
        uint32_t other, binary, ternary;
    } constraints{};
    uint32_t acycEdges{};
    uint32_t complexity{};
    struct Extra {
        // StatisticObject
        static auto        size() -> uint32_t;
        static auto        key(uint32_t i) -> std::string_view;
        [[nodiscard]] auto at(std::string_view k) const -> StatisticObject;

        uint32_t other;   // number of other constraints
        uint32_t clauses; // number of (long) clauses
        uint64_t clLits;  // sum of literals in (long) clauses
        struct {
            [[nodiscard]] constexpr auto avgLength() const noexcept -> double { return ratio(lits, n); }
            [[nodiscard]] constexpr auto avgBound() const noexcept -> double { return ratio(bounds, n); }

            uint64_t lits;   // sum of literals in cardinality/weight constraints
            uint64_t bounds; // sum of bounds
            uint32_t n;      // number of constraints
            uint32_t c;      // sum of complexity
        } weightCons[2];     // cardinality/weight constraints
    } extra{};
    //
    [[nodiscard]] constexpr auto numConstraints() const noexcept -> uint32_t {
        return constraints.other + constraints.binary + constraints.ternary;
    }
    [[nodiscard]] constexpr auto avgLongClauseLength() const noexcept -> double {
        return ratio(extra.clLits, extra.clauses);
    }
    [[nodiscard]] constexpr auto avgClauseLength() const noexcept -> double {
        return ratio(extra.clLits + (constraints.binary * 2) + (constraints.ternary * 3),
                     extra.clauses + constraints.binary + constraints.ternary);
    }
    template <typename T>
    static constexpr void setDiffMinMax(T& lhs, T rhs) {
        lhs = std::max(lhs, rhs) - std::min(lhs, rhs);
    }
    void diff(const ProblemStats& o) {
        setDiffMinMax(vars.num, o.vars.num);
        setDiffMinMax(vars.eliminated, o.vars.eliminated);
        setDiffMinMax(vars.frozen, o.vars.frozen);
        setDiffMinMax(constraints.other, o.constraints.other);
        setDiffMinMax(constraints.binary, o.constraints.binary);
        setDiffMinMax(constraints.ternary, o.constraints.ternary);
        setDiffMinMax(extra.other, o.extra.other);
        setDiffMinMax(extra.clauses, o.extra.clauses);
        setDiffMinMax(extra.clLits, o.extra.clLits);
        for (auto i : irange(extra.weightCons)) {
            setDiffMinMax(extra.weightCons[i].n, o.extra.weightCons[i].n);
            setDiffMinMax(extra.weightCons[i].c, o.extra.weightCons[i].c);
            setDiffMinMax(extra.weightCons[i].lits, o.extra.weightCons[i].lits);
            setDiffMinMax(extra.weightCons[i].bounds, o.extra.weightCons[i].bounds);
        }
        setDiffMinMax(acycEdges, o.acycEdges);
    }
    void accu(const ProblemStats& o) {
        vars.num            += o.vars.num;
        vars.eliminated     += o.vars.eliminated;
        vars.frozen         += o.vars.frozen;
        constraints.other   += o.constraints.other;
        constraints.binary  += o.constraints.binary;
        constraints.ternary += o.constraints.ternary;
        extra.other         += o.extra.other;
        extra.clLits        += o.extra.clLits;
        extra.clauses       += o.extra.clauses;
        for (auto i : irange(extra.weightCons)) {
            extra.weightCons[i].n      += o.extra.weightCons[i].n;
            extra.weightCons[i].c      += o.extra.weightCons[i].c;
            extra.weightCons[i].lits   += o.extra.weightCons[i].lits;
            extra.weightCons[i].bounds += o.extra.weightCons[i].bounds;
        }
        acycEdges += o.acycEdges;
    }
    // StatisticObject
    static auto        size() -> uint32_t;
    static auto        key(uint32_t i) -> std::string_view;
    [[nodiscard]] auto at(std::string_view k) const -> StatisticObject;
};

//! Stores static information about a variable.
struct VarInfo {
    //! Possible flags.
    enum Flag : uint32_t {
        flag_pos    = 0x1u,  //!< Mark for positive literal.
        flag_neg    = 0x2u,  //!< Mark for negative literal.
        flag_input  = 0x4u,  //!< Is this var an input variable?
        flag_body   = 0x8u,  //!< Is this var representing a body?
        flag_eq     = 0x10u, //!< Is this var representing both a body and an atom?
        flag_nant   = 0x20u, //!< Is this var in NAnt(P)?
        flag_frozen = 0x40u, //!< Is the variable frozen?
        flag_output = 0x80u  //!< Is the variable an output variable?
    };
    constexpr explicit VarInfo(uint8_t r = 0) : rep(r) {}
    //! Returns the type of the variable (or VarType::hybrid if variable was created with parameter eq=true).
    [[nodiscard]] constexpr auto type() const -> VarType {
        return has(flag_eq) ? VarType::hybrid : static_cast<VarType>(+VarType::atom + has(flag_body));
    }
    //! Returns whether variable is an atom (or hybrid).
    [[nodiscard]] constexpr bool atom() const { return Potassco::test(type(), VarType::atom); }
    //! Returns whether var is part of negative antecedents (occurs negatively or in the head of a choice rule).
    [[nodiscard]] constexpr bool nant() const { return has(flag_nant); }
    //! Returns true if var is excluded from variable elimination.
    [[nodiscard]] constexpr bool frozen() const { return has(flag_frozen); }
    //! Returns true if var is an input variable.
    [[nodiscard]] constexpr bool input() const { return has(flag_input); }
    //! Returns true if var is marked as output variable.
    [[nodiscard]] constexpr bool output() const { return has(flag_output); }
    //! Returns the preferred sign of this variable w.r.t its type.
    /*!
     * \return false (i.e., no sign) if var originated from body, otherwise true.
     */
    [[nodiscard]] constexpr bool preferredSign() const { return not has(flag_body); }

    [[nodiscard]] constexpr bool has(Flag f) const { return Potassco::test_mask(rep, f); }
    [[nodiscard]] constexpr bool has(uint32_t f) const { return Potassco::test_any(rep, f); }
    [[nodiscard]] constexpr bool hasAll(uint32_t f) const { return Potassco::test_mask(rep, f); }
    constexpr void               set(Flag f) { rep = Potassco::set_mask(rep, f); }
    constexpr void               toggle(Flag f) { rep = Potassco::toggle_mask(rep, f); }
    uint8_t                      rep;
};

//! A class for efficiently storing and propagating binary and ternary clauses.
/*!
 * \ingroup shared_con
 */
class ShortImplicationsGraph {
public:
    ShortImplicationsGraph() = default;
    ~ShortImplicationsGraph();
    ShortImplicationsGraph(ShortImplicationsGraph&&) = delete;

    //! Makes room for `nodes` number of nodes.
    void resize(uint32_t nodes);
    //! Mark the instance as shared/unshared.
    /*!
     * A shared instance adds learnt binary/ternary clauses
     * to specialized shared blocks of memory.
     */
    void markShared(bool b) { shared_ = b; }
    //! Check and avoid duplicates when simplifying ternary clauses
    void setSimpMode(ContextParams::ShortSimpMode x) { simp_ = x; }
    //! Adds the given constraint to the implication graph.
    /*!
     * \return true iff a new implication was added.
     */
    bool add(LitView lits, bool learnt);
    //! Removes the given constraint from the implication graph.
    /*!
     * \pre The object is currently not shared.
     */
    void remove(LitView lits, bool learnt);

    //! Removes p and its implications.
    /*!
     * \pre s.isTrue(p)
     */
    void removeTrue(const Solver& s, Literal p);

    //! Propagates the consequences of p following from binary and ternary clauses.
    /*!
     * \pre s.isTrue(p)
     */
    bool propagate(Solver& s, Literal p) const;
    //! Propagates immediate consequences of p following from binary clauses only.
    bool propagateBin(Assignment& out, Literal p, uint32_t dl) const;
    //! Checks whether there is a reverse arc implying p and if so returns it in out.
    bool reverseArc(const Solver& s, Literal p, uint32_t maxLev, Antecedent& out) const;

    [[nodiscard]] auto numBinary() const -> uint32_t { return bin_[0]; }
    [[nodiscard]] auto numTernary() const -> uint32_t { return tern_[0]; }
    [[nodiscard]] auto numLearnt() const -> uint32_t { return bin_[1] + tern_[1]; }
    [[nodiscard]] auto numEdges(Literal p) const -> uint32_t;
    [[nodiscard]] auto size() const -> uint32_t { return size_; }
    [[nodiscard]] auto simpMode() const -> ContextParams::ShortSimpMode {
        return static_cast<ContextParams::ShortSimpMode>(simp_);
    }
    //! Type used to disambiguate unary and binary implications in forEach().
    static constexpr struct Unary_t {
        constexpr operator Literal() const noexcept { return lit_false; } // NOLINT
    } unary{};
    //! Applies op on all unary- and binary implications following from p.
    /*!
     * `Op` must be a predicate taking three literals.
     * The first argument will always be `p`.
     * For unary implications `[q]` following from `p`, the second argument will be the literal `q`, while the third
     * argument will be of type `Unary_t`, which is implicitly convertible to `lit_false`.
     * For binary implications `[q, r]` following from `p`, the second and third argument will be `q`, and `r`,
     * respectively.
     * In either case, if `op` returns false, `forEach()` stops and returns false.
     *
     * \note To statically distinguish unary- and binary implications, `Op` can either overload operator() or
     *       use an operator() with a templated third parameter.
     * \note For learnt implications, at least one literal has its watch-flag set.
     */
    template <std::predicate<Literal, Literal, Literal> Op>
    bool forEach(Literal p, const Op& op) const {
        const auto& x = graph_[p.id()];
        if (x.empty()) {
            return true;
        }
        for (auto lit : x.bin) {
            if (not op(p, lit, unary)) {
                return false;
            }
        }
        for (const auto& [q, r] : x.tern) {
            if (not op(p, q, r)) {
                return false;
            }
        }
#if CLASP_HAS_THREADS
        return x.forEachLearnt(p, op);
#else
        return true;
#endif
    }

private:
    using Tern    = std::array<Literal, 2>;
    using TernVec = Vector_t<Tern>;
#if CLASP_HAS_THREADS
    class Block {
    public:
        using const_iterator = const Literal*; // NOLINT
        using iterator       = Literal*;       // NOLINT
        explicit Block(Block* n, const Literal* x, uint32_t xs);
        [[nodiscard]] auto begin() const -> const_iterator { return data_; }
        [[nodiscard]] auto end() const -> const_iterator { return data_ + size(); }
        [[nodiscard]] auto size() const -> uint32_t { return sizeLock_.load(std::memory_order_acquire) >> size_shift; }
        [[nodiscard]] auto next() const -> Block* { return next_; }
        bool               tryLock(uint32_t& lockedSize);
        bool               addUnlock(uint32_t lockedSize, const Literal* x, uint32_t xs);

    private:
        static constexpr auto block_cap  = 13u;
        static constexpr auto lock_mask  = 1u;
        static constexpr auto size_shift = 1u;
        using SizeLock                   = std::atomic<uint32_t>;
        Block*   next_;
        SizeLock sizeLock_;
        Literal  data_[block_cap];
    };
    using SharedBlockPtr = std::atomic<Block*>;
#endif
    struct ImplicationList {
        constexpr ImplicationList() = default;
        ~ImplicationList();
        ImplicationList(ImplicationList&&) = delete;
        auto               operator=(ImplicationList&& other) noexcept -> ImplicationList&;
        [[nodiscard]] auto size() const noexcept -> uint32_t { return size32(bin) + size32(tern); }
        [[nodiscard]] bool empty() const noexcept {
            return bin.empty() && tern.empty()
#if CLASP_HAS_THREADS
                   && learnt == static_cast<Block*>(nullptr);
#endif
        }
        void reset();
#if CLASP_HAS_THREADS
        template <typename Op>
        bool forEachLearnt(Literal p, const Op& op) const {
            for (Block* b = learnt; b; b = b->next()) {
                for (auto imp = b->begin(), endOf = b->end(); imp != endOf;) {
                    auto sz = 2u - imp->flagged();
                    if (not(sz == 1 ? op(p, imp[0], unary) : op(p, imp[0], imp[1]))) {
                        return false;
                    }
                    imp += sz;
                }
            }
            return true;
        }
        [[nodiscard]] bool hasLearnt(Literal q, Literal r) const noexcept;
        void               resetLearnt();
        void               addLearnt(Literal q, Literal r);
#endif
        LitVec  bin;
        TernVec tern;
#if CLASP_HAS_THREADS
        SharedBlockPtr learnt;
#endif
    };
    using GraphPtr = std::unique_ptr<ImplicationList[]>;
    auto     getList(Literal p) -> ImplicationList& { return graph_[p.id()]; }
    void     removeTern(const Solver& s, const Tern& t, Literal p);
    void     removeBin(Literal other, Literal sat);
    GraphPtr graph_;         // one implication list for each literal
    uint32_t size_{0};       // number of nodes (implication lists) in graph
    uint32_t cap_{0};        // allocated graph array size
    uint32_t bin_[2]{};      // number of binary constraints (0: problem / 1: learnt)
    uint32_t tern_[2]{};     // number of ternary constraints(0: problem / 1: learnt)
    bool     shared_{false}; // shared between multiple threads?
    uint8_t  simp_{0};       // check duplicates during simplification
};

//! Base class for distributing learnt knowledge between solvers.
class Distributor {
public:
    struct Policy {
        enum Types : uint32_t {
            no       = 0,
            conflict = static_cast<uint32_t>(ConstraintType::conflict),
            loop     = static_cast<uint32_t>(ConstraintType::loop),
            all      = conflict | loop,
            implicit = all + 1
        };
        Policy(uint32_t aSz = 0, uint32_t aLbd = 0, uint32_t aType = 0) : size(aSz), lbd(aLbd), types(aType) {}
        uint32_t size  : 22; /*!< Allow distribution up to this size only. */
        uint32_t lbd   : 7;  /*!< Allow distribution up to this lbd only.  */
        uint32_t types : 3;  /*!< Restrict distribution to these types.    */
    };
    explicit Distributor(const Policy& p);
    virtual ~Distributor();
    Distributor(Distributor&&) = delete;

    [[nodiscard]] bool isCandidate(uint32_t size, uint32_t lbd, uint32_t type) const {
        return size <= policy_.size && lbd <= policy_.lbd && Potassco::test_any(policy_.types, type);
    }
    [[nodiscard]] bool isCandidate(uint32_t size, uint32_t lbd, ConstraintType type) const {
        return isCandidate(size, lbd, +type);
    }
    [[nodiscard]] bool isCandidate(uint32_t size, const ConstraintInfo& extra) const {
        return size <= 3u || isCandidate(size, extra.lbd(), extra.type());
    }
    virtual void publish(const Solver& source, SharedLiterals* lits)                          = 0;
    virtual auto receive(const Solver& in, SharedLiterals** out, uint32_t maxOut) -> uint32_t = 0;

private:
    Policy policy_;
};

//! Output table that contains predicates to be output on a model.
class OutputTable {
public:
    using NameType = Potassco::ConstString;
    struct PredType {
        POTASSCO_TRIVIALLY_RELOCATABLE();
        NameType name;
        Literal  cond;
        uint32_t user;
    };
    enum Type : uint32_t { type_var, type_pred, type_term, type_theory };
    using TypeSet                   = Potassco::Bitset<uint32_t, Type>;
    static constexpr auto all_types = TypeSet{type_var, type_pred, type_term, type_theory};
    //! Interface for additional theory output.
    class Theory {
    public:
        virtual ~Theory();
        //! Called once on new model m. Shall return nullptr to indicate no output.
        virtual auto first(const Model& m) -> const char* = 0;
        //! Shall return nullptr to indicate no output.
        virtual auto next() -> const char* = 0;
        //! Shall return the type of this theory extension.
        [[nodiscard]] virtual Type type() const { return type_theory; }
    };
    using TheoryPtr  = TaggedPtr<Theory>;
    using PredVec    = Vector_t<PredType>;
    using PredSpan   = SpanView<PredType>;
    using TheorySpan = SpanView<TheoryPtr>;

    OutputTable();
    ~OutputTable();
    OutputTable(OutputTable&&) = delete;
    //! Adds an output predicate, i.e., `n` is output if `c` is true.
    void add(const std::string_view& n, Literal c, uint32_t u = 0);
    //! Adds `t` as additional theory output. Ownership remains at the caller.
    void add(Theory& t);
    //! Adds `t` as additional theory output.
    void add(std::unique_ptr<Theory> t);
    //! Removes the give theory previously added via `add(Theory& t)`.
    /*!
     * \note If `t` was added via `add(std::unique_ptr<Theory> t)`, the function releases ownership of `t`.
     */
    bool remove(Theory& t);

    //! Sets a range of output variables.
    void setVarRange(const Range32& r);
    void setProjectMode(ProjectMode m);

    //! Sets the filter character to be used in `filter()`.
    void setFilter(char c);
    //! Removes entries whose condition is known to be false or whose name starts with the previously set filter.
    auto filter(uint32_t startPos = 0) -> uint32_t;
    //! Sets the condition of the nth output predicate to cond.
    void setPredicateCondition(uint32_t n, Literal cond);
    template <typename Comp>
    void sortPredicates(const Comp& comp, uint32_t startPos = 0) {
        std::sort(preds_.begin() + std::min(startPos, size32(preds_)), preds_.end(), comp);
    }

    //! Returns whether n would be filtered out.
    [[nodiscard]] bool filter(const std::string_view& n) const;

    [[nodiscard]] auto pred_range() const -> PredSpan { return preds_; }
    [[nodiscard]] auto vars_range() const { return irange(vars_.lo, vars_.hi); }
    [[nodiscard]] auto theory_range() const -> TheorySpan { return theories_; }

    [[nodiscard]] auto projectMode() const -> ProjectMode {
        return projMode_ != ProjectMode::implicit ? projMode_
               : hasProject()                     ? ProjectMode::project
                                                  : ProjectMode::output;
    }
    [[nodiscard]] bool hasProject() const { return not proj_.empty(); }
    [[nodiscard]] auto proj_range() const -> LitView { return proj_; }
    void               addProject(Literal x);
    void               clearProject();

    //! Returns the number of output elements, counting each element in a var range.
    [[nodiscard]] auto size() const -> uint32_t;
    [[nodiscard]] auto numPreds() const -> uint32_t { return size32(preds_); }
    [[nodiscard]] auto numVars() const -> uint32_t { return vars_.hi - vars_.lo; }

private:
    using TheoryVec = Vector_t<TheoryPtr>;
    PredVec     preds_;
    TheoryVec   theories_;
    LitVec      proj_;
    Range32     vars_;
    ProjectMode projMode_;
    char        hide_;
};
//! A type for storing information to be used in clasp's domain heuristic.
class DomainTable {
public:
    DomainTable();
    //! A type storing a single domain modification for a variable.
    class ValueType {
    public:
        ValueType(Var_t v, DomModType t, int16_t bias, uint16_t prio, Literal cond);
        [[nodiscard]] bool hasCondition() const { return cond_ != 0; }
        [[nodiscard]] auto cond() const -> Literal { return Literal::fromId(cond_); }
        [[nodiscard]] auto var() const -> Var_t { return var_; }
        [[nodiscard]] auto type() const -> DomModType;
        [[nodiscard]] auto bias() const -> int16_t { return bias_; }
        [[nodiscard]] auto prio() const -> uint16_t { return prio_; }
        [[nodiscard]] bool comp() const { return comp_ != 0; }

    private:
        uint32_t cond_ : 31;
        uint32_t comp_ : 1;
        uint32_t var_  : 30;
        uint32_t type_ : 2;
        int16_t  bias_;
        uint16_t prio_;
    };
    using DomVec   = Vector_t<ValueType>;
    using iterator = DomVec::const_iterator; // NOLINT

    void               add(Var_t v, DomModType t, int16_t bias, uint16_t prio, Literal cond);
    auto               simplify() -> uint32_t;
    void               reset();
    [[nodiscard]] bool empty() const;
    [[nodiscard]] auto size() const -> uint32_t;
    [[nodiscard]] auto begin() const -> iterator;
    [[nodiscard]] auto end() const -> iterator;
    [[nodiscard]] auto dropView(uint32_t offset = 0u) const { return drop(entries_, offset); }
    LitVec*            assume;

    using DefaultAction = std::function<void(Literal, HeuParams::DomPref, uint32_t)>;
    static void applyDefault(const SharedContext& ctx, const DefaultAction& action, uint32_t prefSet = 0);

private:
    DomVec   entries_;
    uint32_t seen_; // size of domain table after last simplify
};

//! Aggregates information to be shared between solver objects.
/*!
 * Among other things, SharedContext objects store
 * static information on variables, an output table, as well as the
 * binary and ternary implication graph of the input problem.
 *
 * Furthermore, a SharedContext object always stores a distinguished
 * master solver used to store and simplify problem constraints.
 * Additional solvers can be added via SharedContext::pushSolver().
 * Once initialization is completed, any additional solvers must be attached
 * to this object by calling SharedContext::attach().
 */
class SharedContext {
public:
    using SolverVec   = Vector_t<Solver*>;
    using SccGraph    = std::unique_ptr<PrgDepGraph>;
    using ExtGraph    = std::unique_ptr<ExtDepGraph>;
    using ConfigPtr   = Configuration*;
    using DistrPtr    = std::unique_ptr<Distributor>;
    using StatsCRef   = const ProblemStats&;
    using DomTab      = DomainTable;
    using Output      = OutputTable;
    using ImpGraph    = ShortImplicationsGraph;
    using ImpGraphRef = const ImpGraph&;
    using LogPtr      = EventHandler*;
    using SatPrePtr   = std::unique_ptr<SatPreprocessor>;
    using MinPtr      = SharedMinimizeData*;
    enum ResizeMode { resize_reserve = 0u, resize_push = 1u, resize_pop = 2u, resize_resize = 3u };
    enum PreproMode { prepro_preserve_models = 1u, prepro_preserve_shown = 2u, prepro_preserve_heuristic = 4u };
    enum ReportMode { report_default = 0u, report_conflict = 1u };
    enum SolveMode { solve_once = 0u, solve_multi = 1u };
    static constexpr auto markMask(Literal x) { return VarInfo::flag_pos + x.sign(); }
    /*!
     * \name Configuration
     * \brief Functions for creating and configuring a shared context.
     * @{ */
    //! Creates a new object for sharing variables and the binary and ternary implication graph.
    explicit SharedContext();
    ~SharedContext();
    SharedContext(SharedContext&&) = delete;
    //! Resets this object to the state after default construction.
    void reset();
    //! Enables event reporting via the given event handler.
    void setEventHandler(LogPtr r, ReportMode m = report_default) {
        progress_     = r;
        share_.report = static_cast<uint32_t>(m);
    }
    //! Sets solve mode, which can be used by other objects to query whether multi-shot solving is active.
    void setSolveMode(SolveMode m);
    //! Sets how to handle physical sharing of constraints.
    void setShareMode(ContextParams::ShareMode m);
    //! Sets whether the short implication graph should be used for storing short learnt constraints.
    void setShortMode(ContextParams::ShortMode m, ContextParams::ShortSimpMode x = ContextParams::simp_no);
    //! Sets maximal number of solvers sharing this object.
    void setConcurrency(uint32_t numSolver, ResizeMode m = resize_reserve);
    //! If b is true, sets preprocessing mode to model-preserving operations only.
    void setPreserveModels(bool b = true) { setPreproMode(prepro_preserve_models, b); }
    //! If b is true, excludes all shown variables from variable elimination.
    void setPreserveShown(bool b = true) { setPreproMode(prepro_preserve_shown, b); }
    //! If b is true, excludes all variables with domain heuristic modifications from variable elimination.
    void setPreserveHeuristic(bool b = true) { setPreproMode(prepro_preserve_heuristic, b); }

    //! Adds a solver to this object and returns it.
    auto pushSolver() -> Solver&;
    //! Configures the statistic object of attached solvers.
    /*!
     * The level determines the amount of extra statistics.
     * \see ExtendedStats
     * \see JumpStats
     */
    void enableStats(uint32_t level);
    //! Sets the configuration for this object and its attached solvers.
    /*!
     * \param config Configuration to use or nullptr to set default configuration.
     */
    void setConfiguration(Configuration* config);

    SatPrePtr satPrepro; /*!< Preprocessor for simplifying the problem.              */
    SccGraph  sccGraph;  /*!< Program dependency graph - only used for ASP-problems. */
    ExtGraph  extGraph;  /*!< External dependency graph - given by user.             */

    //! Returns the current configuration used in this object.
    [[nodiscard]] auto configuration() const -> ConfigPtr { return config_; }
    //! Returns the active event handler or nullptr if none was set.
    [[nodiscard]] auto eventHandler() const -> LogPtr { return progress_; }
    //! Returns the active report mode.
    [[nodiscard]] auto reportMode() const -> ReportMode { return static_cast<ReportMode>(share_.report); }
    //! Returns whether this object seeds the RNG of new solvers.
    [[nodiscard]] bool seedSolvers() const { return share_.seed != 0; }
    //! Returns the number of solvers that can share this object.
    [[nodiscard]] auto concurrency() const -> uint32_t { return share_.count; }
    [[nodiscard]] bool preserveModels() const { return (share_.satPreM & prepro_preserve_models) != 0; }
    [[nodiscard]] bool preserveShown() const { return (share_.satPreM & prepro_preserve_shown) != 0; }
    [[nodiscard]] bool preserveHeuristic() const { return (share_.satPreM & prepro_preserve_heuristic) != 0; }
    [[nodiscard]] auto defaultDomPref() const -> uint32_t;
    //! Returns whether physical sharing is enabled for constraints of type t.
    [[nodiscard]] bool physicalShare(ConstraintType t) const {
        return (share_.shareM & (1u + (t != ConstraintType::static_))) != 0;
    }
    //! Returns whether physical sharing of problem constraints is enabled.
    [[nodiscard]] bool physicalShareProblem() const { return (share_.shareM & ContextParams::share_problem) != 0; }
    //! Returns whether short constraints of type t can be stored in the short implication graph.
    [[nodiscard]] bool allowImplicit(ConstraintType t) const {
        return t != ConstraintType::static_ ? share_.shortM != ContextParams::short_explicit : not isShared();
    }
    //! Returns the configured solve mode.
    [[nodiscard]] auto solveMode() const -> SolveMode { return static_cast<SolveMode>(share_.solveM); }
    //@}

    /*!
     * \name Problem introspection
     * \brief Functions for querying information about the problem.
     */
    //@{
    //! Returns true unless the master has an unresolvable top-level conflict.
    [[nodiscard]] bool ok() const;
    //! Returns whether the problem is currently frozen and therefore ready for being solved.
    [[nodiscard]] bool frozen() const { return share_.frozen; }
    //! Returns whether more than one solver is actively working on the problem.
    [[nodiscard]] bool isShared() const { return frozen() && concurrency() > 1; }
    //! Returns whether the problem is more than a simple CNF.
    [[nodiscard]] bool isExtended() const { return stats_.vars.frozen != 0; }
    //! Returns whether this object has a solver associated with the given id.
    [[nodiscard]] bool hasSolver(uint32_t id) const { return id < solvers_.size(); }
    //! Returns the master solver associated with this object.
    [[nodiscard]] auto master() const -> Solver* { return solver(0); }
    //! Returns the solver with the given id.
    [[nodiscard]] auto solver(uint32_t id) const -> Solver* { return solvers_[id]; }

    //! Returns the number of problem variables.
    /*!
     * \note The special sentinel-var 0 is not counted. Hence, numVars() returns
     * the number of problem variables.
     * To iterate over all problem variables, use a loop like:
     * \code
     * for (auto v : vars()) {...}
     * \endcode
     */
    [[nodiscard]] auto numVars() const -> uint32_t { return size32(varInfo_) - 1; }
    //! Returns the problem variables as an iterable view.
    [[nodiscard]] auto vars() const { return irange(1u, numVars() + 1); }
    //! Returns the number of eliminated vars.
    [[nodiscard]] auto numEliminatedVars() const -> uint32_t { return stats_.vars.eliminated; }
    //! Returns true if var represents a valid variable in this problem.
    /*!
     * \note The range of valid variables is [1;numVars()]. The variable 0
     * is a special sentinel variable.
     */
    [[nodiscard]] bool validVar(Var_t var) const { return var < size32(varInfo_); }
    //! Returns information about the given variable.
    [[nodiscard]] auto varInfo(Var_t v) const -> VarInfo {
        assert(validVar(v));
        return varInfo_[v];
    }
    //! Returns true if v is currently eliminated, i.e., no longer part of the problem.
    [[nodiscard]] bool eliminated(Var_t v) const;
    [[nodiscard]] bool marked(Literal p) const { return varInfo(p.var()).has(markMask(p)); }
    //! Returns the number of problem constraints.
    [[nodiscard]] auto numConstraints() const -> uint32_t;
    //! Returns the number of binary constraints.
    [[nodiscard]] auto numBinary() const -> uint32_t { return btig_.numBinary(); }
    //! Returns the number of ternary constraints.
    [[nodiscard]] auto numTernary() const -> uint32_t { return btig_.numTernary(); }
    //! Returns the number of unary constraints.
    [[nodiscard]] auto numUnary() const -> uint32_t { return lastTopLevel_; }
    //! Returns whether the problem contains minimize (weak) constraints.
    [[nodiscard]] bool hasMinimize() const;
    [[nodiscard]] auto stats() const -> StatsCRef { return stats_; }
    //@}

    /*!
     * \name Problem setup
     * \brief Functions for specifying the problem.
     *
     * Problem specification is a four-stage process:
     * -# Add variables to the SharedContext object.
     * -# Call startAddConstraints().
     * -# Add problem constraints.
     * -# Call endInit() to finish the initialization process.
     * .
     * \note After endInit() was called, other solvers can be attached to this object.
     * \note In incremental setting, the process must be repeated for each incremental step.
     *
     * \note Problem specification is *not* thread-safe. Hence, during initialization, no other thread shall
     * access the context.
     *
     * \note !frozen() is a precondition for all functions in this group!
     * @{ */
    //! Unfreezes a frozen program and prepares it for updates.
    /*!
     * The function also triggers forgetting of volatile knowledge and removes
     * any auxiliary variables.
     * \see requestStepVar()
     * \see Solver::popAuxVar()
     */
    bool unfreeze();

    //! Adds a new variable and returns its numerical id.
    /*!
     * \param type  Type of variable.
     * \param flags Additional information associated with the new variable.
     * \note Problem variables are numbered from 1 onward!
     */
    auto addVar(VarType type, uint8_t flags = VarInfo::flag_nant | VarInfo::flag_input) -> Var_t {
        return addVars(1, type, flags);
    }
    auto addVars(uint32_t nVars, VarType type, uint8_t flags = VarInfo::flag_nant | VarInfo::flag_input) -> Var_t;
    //! Removes the n most recently added problem variables.
    /*!
     * \pre The variables either have not yet been committed by a call to `startAddConstraints()`
     *      or they do not occur in any constraint.
     */
    void popVars(uint32_t n = 1);
    //! Freezes/defreezes a variable (a frozen var is exempt from Sat-preprocessing).
    void setFrozen(Var_t v, bool b);
    //! Marks/unmarks v as input variable.
    void setInput(Var_t v, bool b) { set(v, VarInfo::flag_input, b); }
    //! Marks/unmarks v as output variable.
    void setOutput(Var_t v, bool b) { set(v, VarInfo::flag_output, b); }
    //! Marks/unmarks v as part of negative antecedents.
    void setNant(Var_t v, bool b) { set(v, VarInfo::flag_nant, b); }
    void setVarEq(Var_t v, bool b) { set(v, VarInfo::flag_eq, b); }
    void set(Var_t v, VarInfo::Flag f, bool b) {
        if (b != varInfo(v).has(f)) {
            varInfo_[v].toggle(f);
        }
    }
    void mark(Literal p) {
        assert(validVar(p.var()));
        Potassco::store_set_mask(varInfo_[p.var()].rep, markMask(p));
    }
    void unmark(Literal p) {
        assert(validVar(p.var()));
        Potassco::store_clear_mask(varInfo_[p.var()].rep, markMask(p));
    }
    void unmark(Var_t v) {
        assert(validVar(v));
        Potassco::store_clear_mask(varInfo_[v].rep, VarInfo::flag_pos | VarInfo::flag_neg);
    }
    //! Eliminates the variable v from the problem.
    /*!
     * \pre v must not occur in any constraint and frozen(v) == false and value(v) == value_free
     */
    void eliminate(Var_t v);

    //! Prepares the master solver so that constraints can be added.
    /*!
     * Must be called to publish previously added variables to master solver
     * and before constraints over these variables can be added.
     * \return The master solver associated with this object.
     */
    auto startAddConstraints(uint32_t constraintGuess = 100) -> Solver&;

    //! A convenience method for adding facts to the master.
    bool addUnary(Literal x);
    //! A convenience method for adding binary clauses.
    bool addBinary(Literal x, Literal y);
    //! A convenience method for adding ternary clauses.
    bool addTernary(Literal x, Literal y, Literal z);
    //! A convenience method for adding constraints to the master.
    void add(Constraint* c);
    //! Add weak constraint :~ x.first \[x.second\@p\].
    void addMinimize(WeightLiteral x, Weight_t p);
    //! Returns a pointer to an optimized representation of all minimize constraints in this problem.
    auto minimize() -> MinPtr;
    //! List of output predicates and/or variables.
    Output output;
    //! Set of heuristic modifications.
    DomTab heuristic;
    //! Requests a special variable for tagging volatile knowledge in multi-shot solving.
    /*!
     * The step variable is created on the next call to endInit() and removed on the next
     * call to unfreeze().
     * Once the step variable S is set, learnt constraints containing ~S are
     * considered to be "volatile" and removed on the next call to unfreeze().
     * For this to work correctly, S shall be a root assumption during search.
     */
    void requestStepVar();
    //! Similar to `requestStepVar()`, but adds the step variable immediately if necessary.
    /*!
     * \post not isSentinel(stepLiteral())
     * \return stepLiteral()
     */
    auto requireStepVar() -> Literal;
    //! Finishes initialization of the master solver.
    /*!
     * The function must be called once before search is started. After endInit()
     * was called, previously added solvers can be attached to the
     * shared context and learnt constraints may be added to solver.
     * \param attachAll If true, also calls attach() for all solvers that were added to this object.
     * \return If the constraints are initially conflicting, false. Otherwise, true.
     * \note
     * The master solver can't recover from top-level conflicts, i.e., if endInit()
     * returned false, the solver is in an unusable state.
     * \post frozen()
     */
    bool endInit(bool attachAll = false);
    //@}

    /*!
     * \name (Parallel) solving
     * Functions to be called during (parallel) solving.
     *
     * \note If not otherwise noted, the functions in this group can be safely called
     * from multiple threads.
     * @{ */
    //! Returns the active step literal (see requestStepVar()).
    [[nodiscard]] auto stepLiteral() const -> Literal { return step_; }
    //! Attaches the solver with the given id to this object.
    /*!
     * \note It is safe to attach multiple solvers concurrently
     * but the master solver shall not change during the whole operation.
     *
     * \pre hasSolver(id)
     */
    bool attach(uint32_t id) { return attach(*solver(id)); }
    bool attach(Solver& s);

    //! Detaches the solver with the given id from this object.
    /*!
     * The function removes any tentative constraints from s.
     * Shall be called once after search has stopped.
     * \note The function is concurrency-safe w.r.t to different solver objects,
     *       i.e., in a parallel search, different solvers may call detach()
     *       concurrently.
     */
    void detach(uint32_t id, bool reset = false) { return detach(*solver(id), reset); }
    void detach(Solver& s, bool reset = false);

    DistrPtr distributor; /*!< Distributor object to use for distribution of learnt constraints.*/

    [[nodiscard]] auto winner() const -> uint32_t { return share_.winner; }
    void               setWinner(uint32_t sId) { share_.winner = std::min(sId, concurrency()); }

    //! Simplifies the problem constraints w.r.t the master's assignment.
    void simplify(LitView assigned, bool shuffle);
    //! Removes the constraint with the given idx from the master's db.
    void removeConstraint(uint32_t idx, bool detach);
    //! Removes all minimize constraints from this object.
    void removeMinimize();

    //! Adds the given short implication to the short implication graph if possible.
    /*!
     * \return
     *   - > 0 if implication was added.
     *   - < 0 if implication can't be added because allowImplicit() is false for ct.
     *   - = 0 if implication is subsumed by some constraint in the short implication graph.
     */
    int  addImp(LitView lits, ConstraintType ct);
    bool addPost(Solver& s);
    void setHeuristic(Solver& s);
    //! Returns the number of learnt short implications.
    [[nodiscard]] auto numLearntShort() const -> uint32_t { return btig_.numLearnt(); }
    [[nodiscard]] auto shortImplications() const -> ImpGraphRef { return btig_; }
    void               report(const Event& ev) const {
        if (progress_) {
            progress_->dispatch(ev);
        }
    }
    [[nodiscard]] bool report(const Solver& s, const Model& m) const {
        return not progress_ || progress_->onModel(s, m);
    }
    void reportConflict(const Solver& s, LitView cc, const ConstraintInfo& i) const {
        if (progress_ && reportMode() == report_conflict) {
            progress_->dispatch(ConflictEvent(s, cc, i));
        }
    }
    void               report(const char* what, const Solver* s = nullptr) const;
    void               enter(Event::Subsystem sys) const;
    void               warn(const char* what) const;
    void               initStats(Solver& s) const;
    [[nodiscard]] auto solverStats(uint32_t sId) const -> SolverStats&;         // stats of solver i
    auto               accuStats(SolverStats& out) const -> const SolverStats&; // accumulates all solver stats in out
    [[nodiscard]] auto minimizeNoCreate() const -> MinPtr;
    bool               propagate();
    //@}
private:
    bool preprocessShort();
    bool unfreezeStep();
    using VarVec = Vector_t<VarInfo>;
    void setPreproMode(uint32_t m, bool b);
    struct Minimize;
    using MiniPtr = std::unique_ptr<Minimize>;
    ProblemStats stats_;                                   // problem statistics
    VarVec       varInfo_;                                 // varInfo[v] stores info about variable v
    ImpGraph     btig_;                                    // binary-/ternary implication graph
    ConfigPtr    config_;                                  // active configuration
    SolverVec    solvers_;                                 // solvers associated with this context
    MiniPtr      mini_;                                    // pointer to the set of weak constraints
    LogPtr       progress_;                                // event handler or nullptr if none
    Literal      step_;                                    // literal for tagging enumeration/step constraints
    uint32_t     lastTopLevel_;                            // size of master's top-level after last init
    struct Share {                                         // Additional data
        uint32_t count   : 10 = 1;                         //   max number of objects sharing this object
        uint32_t winner  : 10 = 0;                         //   id of solver that terminated the search
        uint32_t shareM  : 3  = ContextParams::share_auto; //   physical sharing mode
        uint32_t shortM  : 1  = 0;                         //   short clause mode
        uint32_t solveM  : 1  = 0;                         //   solve mode
        uint32_t frozen  : 1  = 0;                         //   is adding of problem constraints allowed?
        uint32_t seed    : 1  = 0;                         //   set seed of new solvers
        uint32_t satPreM : 3  = 0;                         //   preprocessing mode
        uint32_t report  : 2  = 0;                         //   report mode
    } share_;
};
//@}
} // namespace Clasp
