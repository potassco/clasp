//
// Copyright (c) 2013-present Benjamin Kaufmann
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

#include <clasp/logic_program_types.h>
#include <clasp/program_builder.h>
#include <clasp/statistics.h>
#include <clasp/util/misc_types.h>

#include <potassco/enum.h>
#include <potassco/error.h>
#include <potassco/theory_data.h>

namespace Clasp::Asp {
/*!
 * \file
 * \defgroup asp Asp
 * \brief Classes and functions for defining logic programs.
 * \ingroup problem
 */
//@{

//! A struct for counting program rules and directives.
struct RuleStats {
    using Ref_t  = uint32_t&;
    using CRef_t = uint32_t const&;
    //! Rules and directives counted by this object.
    enum Key {
        normal = static_cast<int>(HeadType::disjunctive), //!< Normal or disjunctive rules.
        choice = static_cast<int>(HeadType::choice),      //!< Choice rules.
        minimize,                                         //!< Distinct minimize constraints.
        acyc,                                             //!< Edge directives.
        heuristic,                                        //!< Heuristic directives.
        key_num
    };
    //! Returns a string representation of the given key.
    static const char* toStr(unsigned k);
    //! Returns the number of keys distinguished by this type.
    static uint32_t numKeys() { return key_num; }
    //! Updates the number of rules of the given type.
    void up(Key k, int amount) { key[k] += static_cast<uint32_t>(amount); }
    //! Returns the number of rules of the given type.
    Ref_t operator[](unsigned k) { return key[k]; }
    //! @copydoc Ref_t operator[](unsigned k)
    CRef_t operator[](unsigned k) const { return key[k]; }
    //! Returns the sum of all rules.
    [[nodiscard]] uint32_t sum() const;
    uint32_t               key[key_num]; //!< @private
};
//! A struct for counting distinct program bodies.
struct BodyStats {
    using Ref_t  = uint32_t&;
    using CRef_t = uint32_t const&;
    //! Body types distinguished by this object.
    using Key = BodyType;
    //! Returns a string representation of the given key.
    static const char* toStr(unsigned k);
    //! Returns the number of keys distinguished by this type.
    static uint32_t numKeys() { return Potassco::enum_count<BodyType>() + 1; }
    //! Updates the number of bodies of the given type.
    void up(Key k, int amount) { key[static_cast<int>(k)] += static_cast<uint32_t>(amount); }
    //! Returns the number of bodies of the given type.
    Ref_t operator[](unsigned k) { return key[k]; }
    //! @copydoc Ref_t operator[](unsigned k)
    CRef_t operator[](unsigned k) const { return key[k]; }
    //! Returns the sum of all bodies.
    [[nodiscard]] uint32_t sum() const;
    uint32_t               key[Potassco::enum_count<BodyType>() + 1]; //!< @private
};

//! A type for maintaining a set of program statistics.
class LpStats {
public:
    constexpr LpStats() = default;
    //! Returns the sum of all equivalences.
    [[nodiscard]] uint32_t eqs() const { return eqs(VarType::atom) + eqs(VarType::body) + eqs(VarType::hybrid); }
    //! Returns the number of equivalences of the given type.
    [[nodiscard]] uint32_t eqs(VarType t) const { return eqs_[+t - 1]; }
    //! Increments the number of equivalences of the given type.
    void incEqs(VarType t) { ++eqs_[+t - 1]; }
    //! Computes *this += o.
    void accu(const LpStats& o);
    // StatisticObject
    static uint32_t    size();
    static const char* key(uint32_t i);
    StatisticObject    at(const char* k) const;

    RuleStats rules[2]{};        /**< RuleStats (initial, final). */
    BodyStats bodies[2]{};       /**< BodyStats (initial, final). */
    uint32_t  atoms{0};          /**< Number of program atoms.    */
    uint32_t  auxAtoms{0};       /**< Number of aux atoms created. */
    uint32_t  disjunctions[2]{}; /**< Number of disjunctions (initial, non-hcf). */
    uint32_t  sccs{0};           /**< How many strongly connected components? */
    uint32_t  nonHcfs{0};        /**< How many non head-cycle free components?*/
    uint32_t  gammas{0};         /**< How many non-hcf gamma rules. */
    uint32_t  ufsNodes{0};       /**< How many nodes in the positive dependency graph? */

private:
    uint32_t eqs_[3]{};
};

using Potassco::TheoryData;
using DomModType = Potassco::DomModifier;
enum class MapLit { raw = 0, refined = 1 };

//! A class for defining a logic program.
/*!
 * Use this class to specify a logic program. Once the program is completely defined,
 * call endProgram() to load the logic program into a SharedContext object.
 */
class LogicProgram : public ProgramBuilder {
public:
    LogicProgram();
    ~LogicProgram() override;
    //! Defines the possible modes for handling extended rules, i.e. choice, cardinality, and weight rules.
    enum ExtendedRuleMode {
        mode_native            = 0, //!< Handle extended rules natively.
        mode_transform         = 1, //!< Transform extended rules to normal rules.
        mode_transform_choice  = 2, //!< Transform only choice rules to normal rules.
        mode_transform_card    = 3, //!< Transform only cardinality rules to normal rules.
        mode_transform_weight  = 4, //!< Transform cardinality- and weight rules to normal rules.
        mode_transform_scc     = 5, //!< Transform recursive cardinality- and weight rules to normal rules.
        mode_transform_nhcf    = 6, //!< Transform cardinality- and weight rules in non-hcf components to normal rules.
        mode_transform_integ   = 7, //!< Transform cardinality-based integrity constraints.
        mode_transform_dynamic = 8  //!< Heuristically decide whether to transform a particular extended rule.
    };

    //! Options for the Asp-Preprocessor.
    struct AspOptions {
        static constexpr uint32_t max_eq_iters = (1u << 26) - 1;
        using TrMode                           = ExtendedRuleMode;
        constexpr AspOptions()                 = default;
        constexpr AspOptions& iterations(uint32_t it) {
            static_assert(sizeof(*this) == sizeof(TrMode) + sizeof(uint32_t), "unexpected alignment");
            iters = it <= max_eq_iters ? it : max_eq_iters;
            return *this;
        }
        constexpr AspOptions& depthFirst() {
            dfOrder = 1;
            return *this;
        }
        constexpr AspOptions& backpropagate() {
            backprop = 1;
            return *this;
        }
        constexpr AspOptions& noScc() {
            noSCC = 1;
            return *this;
        }
        constexpr AspOptions& noEq() {
            iters = 0;
            return *this;
        }
        constexpr AspOptions& disableGamma() {
            noGamma = 1;
            return *this;
        }
        constexpr AspOptions& ext(ExtendedRuleMode m) {
            erMode = m;
            return *this;
        }
        TrMode   erMode        = mode_native; //!< How to handle extended rules?
        uint32_t iters    : 26 = 5;           //!< Number of iterations in eq-preprocessing or 0 to disable.
        uint32_t noSCC    : 1  = 0;           //!< Disable scc checking?
        uint32_t suppMod  : 1  = 0;           //!< Disable scc checking and compute supported models.
        uint32_t dfOrder  : 1  = 0;           //!< Visit nodes in eq-preprocessing in depth-first order?
        uint32_t backprop : 1  = 0;           //!< Enable backpropagation during preprocessing?
        uint32_t oldMap   : 1  = 0;           //!< Use old and larger mapping for disjunctive programs.
        uint32_t noGamma  : 1  = 0;           //!< Disable creation of (shifted) gamma rules for non-hcf disjunctions?
    };

    /*!
     * \name Step control functions
     */
    //@{

    //! Starts the definition of a logic program.
    LogicProgram& start(SharedContext& ctx, const AspOptions& opts) {
        startProgram(ctx);
        setOptions(opts);
        return *this;
    }
    LogicProgram& start(SharedContext& ctx) { return start(ctx, {}); }
    //! Sets the mode for handling extended rules (default: mode_native).
    void setExtendedRuleMode(ExtendedRuleMode m) { opts_.ext(m); }
    //! Enable distinct true vars for incremental steps.
    void enableDistinctTrue();
    //! Maintain atom output state.
    /*!
     * \see LogicProgram::getOutputState(Atom_t) const;
     */
    void enableOutputState();
    //! Sets preprocessing options.
    void setOptions(const AspOptions& opts);
    //! Sets the configuration to be used for checker solvers in disjunctive LP solving.
    void setNonHcfConfiguration(Configuration* c) { nonHcfs_.config = c; }

    //! Unfreezes a currently frozen program and starts an incremental step.
    /*!
     * If a program is to be defined incrementally, this function must be called
     * exactly once for each step before any new rules or atoms are added.
     * \note Program update only works correctly under the following assumptions:
     *  - Atoms introduced in step 'i' are either:
     *    - solely defined in step i OR,
     *    - marked as frozen in step i and solely defined in step i+k OR,
     *    - forced to false by a compute statement in step 0.
     *
     * \pre The program is either frozen or at step 0.
     * \post The program is no longer frozen and calling program mutating functions is valid again.
     * \throws std::logic_error precondition is violated.
     * \note The function is an alias for ProgramBuilder::updateProgram().
     */
    bool update() { return updateProgram(); }

    //! Finishes the definition of the logic program (or its current increment).
    /*!
     * Applies program mutating operations issued in the current step and transforms
     * the new program into the solver's internal representation.
     *
     * \return false if the program is conflicting, true otherwise.
     *
     * \post
     *  - If true is returned, the program is considered to be "frozen" and calling
     *    program mutating functions is invalid until the next call to update().
     *  - If false is returned, the state of the object is undefined and start()
     *    and dispose() are the only remaining valid operations.
     *  .
     * \note The function is an alias for ProgramBuilder::endProgram().
     */
    bool end() { return endProgram(); }

    //! Visits the current program by notifying `out` on its elements.
    /*!
     * \param out          Program that should receive elements.
     * \param addPreamble  Whether accept() should call step functions on `out`. If true, accept() wraps calls to `out`
     *                     in AbstractProgram::beginStep()/AbstractProgram::endStep() calls. Furthermore, if the program
     *                     is not incremental or currently at the first step, AbstractProgram::initProgram() is called.
     */
    void accept(Potassco::AbstractProgram& out, bool addPreamble);

    //! Disposes parts of the internal representation of the logic program.
    /*!
     * Only the rules of the current step are disposed, while atoms and any incremental control data remain.
     *
     * \note startProgram() can be called to dispose the whole program.
     */
    void dispose();

    //! Clones the program and adds it to the given ctx.
    /*
     * \pre The program is currently frozen.
     */
    bool clone(SharedContext& ctx);

    //@}

    /*!
     * \name Program mutating functions.
     *
     * Functions in this group shall only be called if the program is currently not
     * frozen. That is, only between the call to start() (resp. update() if in
     * incremental setting) and end(). A std::logic_error is raised if this precondition is violated.
     *
     */
    //@{

    //! Adds a new atom to the program and returns the new atom's id.
    Atom_t newAtom();

    //! Sets atomId as the last input atom of the current step.
    /*!
     * All (new or existing) atoms with a larger id than atomId
     * are considered to be auxiliary and automatically removed before
     * a new incremental step is started.
     *
     * \pre atomId >= startAtom()
     * \post startAuxAtom() == atomId + 1
     */
    void setMaxInputAtom(uint32_t atomId);

    //! Adds a new conjunctive condition to the program.
    /*!
     * \param cond A (possibly empty) list of atom literals.
     * \return The id of the new condition, which can be later passed to
     * extractCondition() or getLiteral().
     */
    Id_t newCondition(Potassco::LitSpan cond);

    //! Adds the given string to the problem's output table.
    /*!
     * \param str The string to add.
     * \param cond The condition under which str should be considered part of a model.
     */
    LogicProgram& addOutput(const Potassco::ConstString& str, Potassco::LitSpan cond);
    LogicProgram& addOutput(const Potassco::ConstString& str, Id_t cond);
    LogicProgram& addOutput(std::string_view str, Potassco::LitSpan cond);
    LogicProgram& addOutput(std::string_view str, Id_t cond);

    //! Adds the given atoms to the set of projection variables.
    LogicProgram& addProject(Potassco::AtomSpan atoms);
    //! Removes all previously added projection variables from the program.
    LogicProgram& removeProject();

    //! Protects an otherwise undefined atom from preprocessing.
    /*!
     * If the atom is defined in this or a previous step, the operation has no effect.
     * \note If atomId is not yet known, an atom with the given id is implicitly created.
     * \note The second parameter defines the assumption that shall hold during solving, i.e.
     *       - posLit(atomId), if value is value_true,
     *       - negLit(atomId), if value is value_false, or
     *       - no assumption, if value is value_free.
     *
     * \see ProgramBuilder::getAssumptions(LitVec&) const;
     */
    LogicProgram& freeze(Atom_t atomId, Val_t value = value_false);

    //! Removes any protection from the given atom.
    /*!
     * If the atom is defined in this or a previous step, the operation has no effect.
     * \note
     *   - The effect is logically equivalent to adding a rule atomId :- false.
     *   - A call to unfreeze() always overwrites a call to freeze() even if the
     *     latter comes after the former
     *   .
     */
    LogicProgram& unfreeze(Atom_t atomId);

    //! Adds the given rule (or integrity constraint) to the program.
    /*!
     * \pre The rule does not define an atom from a previous incremental step.
     *
     * Simplifies the given rule and adds it to the program if it
     * is neither tautological (e.g. a :- a) nor contradictory (e.g. a :- b, not b).
     * Atoms in the simplified rule that are not yet known are implicitly created.
     *
     * \throws std::logic_error if the precondition is violated.
     * \note If the head of the simplified rule mentions an atom from a previous step,
     *       that atom shall either be frozen or false. In the former case,
     *       unfreeze() is implicitly called. In the latter case, the rule is interpreted
     *       as an integrity constraint.
     */
    LogicProgram& addRule(const Rule& rule);
    LogicProgram& addRule(HeadType ht, Potassco::AtomSpan head, Potassco::LitSpan body) {
        return addRule(Rule::normal(ht, head, body));
    }
    LogicProgram& addRule(HeadType ht, Potassco::AtomSpan head, Potassco::Weight_t bound, WeightLitSpan lits) {
        return addRule(Rule::sum(ht, head, bound, lits));
    }
    LogicProgram& addRule(Potassco::RuleBuilder& rb);
    //! Adds the given minimize statement.
    /*!
     * \param prio The priority of the minimize statement.
     * \param lits The literals to minimize.
     * \note All minimize statements of the same priority are merged into one.
     */
    LogicProgram& addMinimize(Weight_t prio, WeightLitSpan lits);
    //! Removes all previously added minimize statements from the program.
    LogicProgram& removeMinimize();

    //! Adds an edge to the extended (user-defined) dependency graph.
    LogicProgram& addAcycEdge(uint32_t n1, uint32_t n2, Potassco::LitSpan condition) {
        return addAcycEdge(n1, n2, newCondition(condition));
    }
    LogicProgram& addAcycEdge(uint32_t n1, uint32_t n2, Id_t cond);

    //! Adds a conditional domain heuristic directive to the program.
    LogicProgram& addDomHeuristic(Atom_t atom, DomModType t, int bias, unsigned prio, Potassco::LitSpan condition) {
        return addDomHeuristic(atom, t, bias, prio, newCondition(condition));
    }
    LogicProgram& addDomHeuristic(Atom_t atom, DomModType t, int bias, unsigned prio, Id_t cond);
    //! Adds an unconditional domain heuristic directive to the program.
    LogicProgram& addDomHeuristic(Atom_t atom, DomModType t, int bias, unsigned prio);

    //! Forces the given literals to be true during solving.
    /*!
     * Assumptions are retracted on the next program update.
     */
    LogicProgram& addAssumption(Potassco::LitSpan cube);

    //! Adds or updates the given external atom.
    /*!
     * \see LogicProgram::freeze(Atom_t atomId, TriVal_t value);
     * \see LogicProgram::unfreeze(Atom_t atomId);
     */
    LogicProgram& addExternal(Atom_t atomId, Potassco::TruthValue value);

    //! Returns an object for adding theory data to this program.
    TheoryData& theoryData();
    //@}

    /*!
     * \name Query functions.
     *
     * Functions in this group are useful to query important information
     * once the program is frozen, i.e. after end() was called.
     * They do not throw exceptions.
     */
    //@{
    //! Returns whether the program can be represented in internal smodels format.
    [[nodiscard]] bool supportsSmodels(const char** errorOut = nullptr) const;
    //! Returns whether the program is to be defined incrementally.
    [[nodiscard]] bool isIncremental() const { return incData_ != nullptr; }
    //! Returns whether the program contains any minimize statements.
    [[nodiscard]] bool hasMinimize() const { return not minimize_.empty(); }
    //! Returns the theory data associated with this program.
    [[nodiscard]] auto theoryData() const -> const TheoryData& { return theory_; }
    //! Returns the number of atoms in the logic program.
    [[nodiscard]] uint32_t numAtoms() const { return size32(atoms_) - 1; }
    //! Returns the number of bodies in the current (slice of the) logic program.
    [[nodiscard]] uint32_t numBodies() const { return size32(bodies_); }
    //! Returns the number of disjunctive heads.
    [[nodiscard]] uint32_t numDisjunctions() const { return size32(disjunctions_); }
    //! Returns the id of the first atom of the current step.
    [[nodiscard]] Atom_t startAtom() const { return input_.lo; }
    //! Returns an id one past the last valid atom id in the program.
    [[nodiscard]] Atom_t endAtom() const { return numAtoms() + 1; }
    //! Returns the id of the first atom that is not an input atom or endAtom() if no such atoms exists.
    [[nodiscard]] Atom_t startAuxAtom() const;
    //! Returns whether 'a' is an atom in the (simplified) program.
    [[nodiscard]] bool inProgram(Atom_t a) const;
    //! Returns whether 'a' is an external atom, i.e. is frozen in this step.
    [[nodiscard]] bool isExternal(Atom_t a) const;
    //! Returns whether 'a' occurs in the head of a rule.
    [[nodiscard]] bool isDefined(Atom_t a) const;
    //! Returns whether 'a' is a fact.
    [[nodiscard]] bool isFact(Atom_t a) const;
    //! Returns whether 'a' is an atom added in the current step.
    [[nodiscard]] bool isNew(Atom_t a) const;
    //! Returns whether 'a' is an atom added in a previous step.
    [[nodiscard]] bool isOld(Atom_t a) const;
    //! Returns the solver literal that is associated with the given atom or condition.
    /*!
     * \pre id is the id of a valid atom literal or was previously returned by newCondition().
     * \note Until end() is called, the function returns \c Clasp::lit_false for
     *       all atoms and conditions defined in the current step.
     * \note For an atom literal 'x' with Potassco::atom(x) == 'a',
     *       getLiteral(Potassco::id(x)) returns
     *        - @c getLiteral(a), iff 'x ==  a', or
     *        - @c ~getLiteral(a), iff 'x == -a'.
     *
     * \note If @c mode is @c MapLit::raw, the function simply returns the literal that
     *       was set during preprocessing. Otherwise, it also considers equivalences
     *       induced by domain heuristic directives and/or step-local true vars.
     *
     * \see enableDistinctTrue()
     */
    [[nodiscard]] Literal getLiteral(Id_t id, MapLit mode = MapLit::raw) const;
    //! Returns the atom literals belonging to the given condition.
    /*!
     * \pre cId was previously returned by newCondition() in the current step.
     */
    bool extractCondition(Id_t cId, Potassco::LitVec& cond) const;

    enum OutputState : uint32_t { out_none = 0u, out_shown = 1u, out_projected = 2u, out_all = 3u };
    //! Returns the output state of the given atom or out_none if output state was not enabled.
    /*!
     * \note If @c mode is MapLit::refined, the function also considers equivalences.
     * \return Output state of the given atom, i.e.
     *   - out_none if atom is neither shown nor projected,
     *   - out_shown if atom is a shown atom (has an associated name),
     *   - out_projected if atom occurs in a projection statement,
     *   - out_all if atom is shown and occurs in a projection statement.
     */
    [[nodiscard]] OutputState getOutputState(Atom_t a, MapLit mode = MapLit::raw) const;
    //! Returns whether 'a' is shown (i.e. has an associated name).
    [[nodiscard]] bool isShown(Atom_t a) const { return Potassco::test(getOutputState(a), out_shown); }
    //! Returns whether 'a' occurs in a projection statement.
    [[nodiscard]] bool isProjected(Atom_t a) const { return Potassco::test(getOutputState(a), out_projected); }

    //! Maps the given unsat core of solver literals to original program assumptions.
    /*!
     * \param unsatCore An unsat core found when solving under ProgramBuilder::getAssumptions().
     * \param prgLits The given unsat core expressed in terms of program literals.
     * \return Whether unsatCore was successfully mapped.
     */
    bool translateCore(LitView unsatCore, Potassco::LitVec& prgLits) const;

    LpStats stats; //!< Statistics of the current step.
    //@}

    /*!
     * \name Implementation functions
     * Low-level implementation functions. Use with care and only if you
     * know what you are doing!
     */
    //@{
    using AtomSpan = SpanView<PrgAtom*>;
    using DisjSpan = SpanView<PrgDisj*>;
    using BodySpan = SpanView<PrgBody*>;
    using VarSpan  = VarView;
    struct SRule {
        uint32_t hash{0};      // hash value of the body
        uint32_t pos{0};       // positive size of body
        uint32_t bid{var_max}; // id of existing body or var_max
    };
    [[nodiscard]] auto options() const -> const AspOptions& { return opts_; }
    [[nodiscard]] auto started() const -> bool { return not atoms_.empty(); }
    [[nodiscard]] bool hasConflict() const { return started() && getTrueAtom()->literal() != lit_true; }
    [[nodiscard]] bool ok() const override { return started() && not hasConflict() && ProgramBuilder::ok(); }
    [[nodiscard]] auto getAtom(Id_t atomId) const -> PrgAtom* { return atoms_[atomId]; }
    [[nodiscard]] auto getHead(PrgEdge it) const -> PrgHead* {
        return it.isAtom() ? node_cast<PrgHead>(getAtom(it.node())) : node_cast<PrgHead>(getDisj(it.node()));
    }
    [[nodiscard]] auto getSupp(PrgEdge it) const -> PrgNode* {
        return it.isBody() ? node_cast<PrgNode>(getBody(it.node())) : node_cast<PrgNode>(getDisj(it.node()));
    }
    [[nodiscard]] Id_t getRootId(Id_t atom) const { return getEqNode(atoms_, atom); }
    [[nodiscard]] auto getRootAtom(Id_t a) const -> PrgAtom* { return getAtom(getRootId(a)); }
    [[nodiscard]] auto getBody(Id_t bodyId) const -> PrgBody* { return bodies_[bodyId]; }
    [[nodiscard]] Id_t getEqBody(Id_t b) const { return getEqNode(bodies_, b); }
    [[nodiscard]] auto getDisj(Id_t disjId) const -> PrgDisj* { return disjunctions_[disjId]; }
    [[nodiscard]] auto bodies() const -> BodySpan { return bodies_; }
    [[nodiscard]] auto disjunctions() const -> DisjSpan { return disjunctions_; }
    [[nodiscard]] auto atoms(uint32_t off = 1) const -> AtomSpan { return drop(atoms_, off); }
    [[nodiscard]] auto newAtoms() const -> AtomSpan { return drop(atoms_, startAtom()); }
    [[nodiscard]] auto oldAtoms() const -> AtomSpan { return {atoms_.data() + 1u, startAtom() - 1u}; }
    [[nodiscard]] auto unfreeze() const -> VarSpan { return incData_ ? VarSpan{incData_->unfreeze} : VarSpan{}; }
    [[nodiscard]] bool validAtom(Id_t aId) const { return aId < size32(atoms_); }
    [[nodiscard]] bool validBody(Id_t bId) const { return bId < numBodies(); }
    [[nodiscard]] bool validDisj(Id_t dId) const { return dId < numDisjunctions(); }
    [[nodiscard]] bool isFact(const PrgAtom* a) const;
    [[nodiscard]] auto findName(Atom_t x) const -> const char*;
    bool               simplifyRule(const Rule& r, Potassco::RuleBuilder& out, SRule& meta);
    Atom_t             falseAtom();
    VarVec&            getSupportedBodies(bool sorted);
    uint32_t           update(PrgBody* b, uint32_t oldHash, uint32_t newHash);
    bool               assignValue(PrgAtom* a, Val_t v, PrgEdge reason);
    bool               assignValue(PrgHead* h, Val_t v, PrgEdge reason);
    bool               propagate(bool backprop);
    auto               mergeEqAtoms(PrgAtom* a, Id_t rootAtom) -> PrgAtom*;
    auto               mergeEqBodies(PrgBody* b, Id_t rootBody, bool hashEq, bool atomsAssigned) -> PrgBody*;
    bool               propagate() { return propagate(options().backprop != 0); }
    void               setConflict();
    auto               atomState() -> AtomState& { return atomState_; }
    void               addMinimize();
    void               addOutputState(Atom_t atom, OutputState state);
    // ------------------------------------------------------------------------
    // Statistics
    void incTrAux(uint32_t n) { stats.auxAtoms += n; }
    void incEqs(VarType t) { stats.incEqs(t); }
    void upStat(RuleStats::Key k, int n = 1) { stats.rules[statsId_].up(k, n); }
    void upStat(BodyType k, int n = 1) { stats.bodies[statsId_].up(k, n); }
    void upStat(HeadType k, int n = 1) { stats.rules[statsId_].up(static_cast<RuleStats::Key>(k), n); }
    // ------------------------------------------------------------------------
    //@}
private:
    struct DlpTr;
    struct AcycArc {
        Id_t     cond;
        uint32_t node[2];
    };
    struct DomRule {
        uint32_t atom : 29;
        uint32_t type : 3;
        Id_t     cond;
        int16_t  bias;
        uint16_t prio;
    };
    struct Eq {
        Atom_t  var{};
        Literal lit;
    };
    using RuleBuilder = Potassco::RuleBuilder;
    using ShowPair    = std::pair<Id_t, Potassco::ConstString>;
    using ShowVec     = PodVector_t<ShowPair>;
    using DomRules    = PodVector_t<DomRule>;
    using AcycRules   = PodVector_t<AcycArc>;
    using RuleList    = PodVector_t<RuleBuilder*>;
    using SccMap      = PodVector_t<uint8_t>;
    using EqVec       = PodVector_t<Eq>;
    using LpWLitVec   = Potassco::WLitVec;
    using LpLitVec    = Potassco::LitVec;
    using AtomRange   = Range32;
    struct IndexData;
    struct Aux;
    struct Incremental;
    using IndexPtr = std::unique_ptr<IndexData>;
    using AuxPtr   = std::unique_ptr<Aux>;
    using IncPtr   = std::unique_ptr<Incremental>;
    // ------------------------------------------------------------------------
    // virtual overrides
    bool              doStartProgram() override;
    bool              doUpdateProgram() override;
    bool              doEndProgram() override;
    void              doGetAssumptions(LitVec& out) const override;
    ProgramParser*    doCreateParser() override;
    [[nodiscard]] int doType() const override { return static_cast<int>(ProblemType::asp); }
    // ------------------------------------------------------------------------
    // Program definition
    [[nodiscard]] bool        handleNatively(const Rule& r) const;
    [[nodiscard]] static bool transformNoAux(const Rule& r);
    [[nodiscard]] static bool equalLits(const PrgBody& b, WeightLitSpan lits);
    [[nodiscard]] bool        isNewAtom(Atom_t a) const { return a >= startAtom(); } // True for new/not yet added atoms
    static Val_t              litVal(const PrgAtom* a, bool pos);
    static bool               positiveLoopSafe(const PrgBody* b, const PrgBody* root);

    PrgAtom* resize(Atom_t atomId);
    void     pushFrozen(PrgAtom* atom, Val_t v);
    void     addRule(const Rule& r, const SRule& meta);
    void     addFact(Atom_t atomId);
    void     addIntegrity(const Rule& b, const SRule& meta);
    void     freezeTheory();
    void     transformExtended();
    void     transformIntegrity(uint32_t nAtoms, uint32_t maxAux);
    PrgBody* getBodyFor(const Rule& r, const SRule& m, bool addDeps = true);
    PrgBody* getTrueBody();
    PrgDisj* getDisjFor(Potassco::AtomSpan head, uint32_t headHash);
    PrgBody* assignBodyFor(const Rule& r, const SRule& m, EdgeType x, bool strongSimp);
    bool simplifyNormal(HeadType ht, Potassco::AtomSpan head, Potassco::LitSpan body, RuleBuilder& out, SRule& meta);
    bool simplifySum(HeadType ht, Potassco::AtomSpan head, const Potassco::Sum& body, RuleBuilder& out, SRule& meta);
    bool pushHead(HeadType ht, Potassco::AtomSpan head, Weight_t slack, RuleBuilder& out);
    uint32_t findBody(uint32_t hash, BodyType type, uint32_t size, Weight_t bound, Potassco::WeightLit* wlits) const;
    [[nodiscard]] uint32_t findBody(uint32_t hash, uint32_t size) const {
        return findBody(hash, BodyType::normal, size, static_cast<Weight_t>(size), nullptr);
    }
    [[nodiscard]] uint32_t findBody(uint32_t hash, BodyType type, Weight_t bound,
                                    std::span<Potassco::WeightLit> wLits) const {
        return findBody(hash, type, size32(wLits), bound, wLits.data());
    }
    uint32_t findEqBody(const PrgBody* b, uint32_t hash);
    uint32_t removeBody(const PrgBody* b, uint32_t oldHash);
    Literal  getEqAtomLit(Literal lit, const BodyList& supports, Preprocessor& p, const SccMap& x);
    void     prepareExternals();
    void     updateFrozenAtoms();
    void     mergeOutput(VarVec::iterator& hint, Atom_t atom, OutputState state);
    template <class C>
    [[nodiscard]] Id_t getEqNode(C& vec, Id_t id) const {
        if (not vec[id]->eq()) {
            return id;
        }
        PrgNode* n    = vec[id];
        Id_t     root = n->id();
        for (PrgNode* r = vec[root]; r->eq(); r = vec[root]) {
            // n == r and r == r' -> n == r'
            assert(root != r->id());
            n->setEq(root = r->id());
        }
        return root;
    }
    [[nodiscard]] bool checkBody(const PrgBody& rhs, BodyType type, uint32_t size, Weight_t bound) const {
        return (rhs.relevant() || (rhs.eq() && getBody(getEqBody(rhs.id()))->relevant())) && rhs.type() == type &&
               rhs.size() == size && rhs.bound() == bound;
    }
    // ------------------------------------------------------------------------
    // Nogood creation
    void prepareProgram(bool checkSccs);
    void prepareOutputTable();
    void finalizeDisjunctions(Preprocessor& p, uint32_t numSccs);
    void prepareComponents();
    bool addConstraints();
    void addAcycConstraint();
    void addDomRules();
    void freezeAssumptions();
    // ------------------------------------------------------------------------
    void                   reset();
    void                   deleteAtoms(uint32_t start);
    [[nodiscard]] PrgAtom* getTrueAtom() const { return atoms_[0]; }

    RuleBuilder rule_;         // temporary: active rule
    AtomState   atomState_;    // which atoms appear in the active rule?
    IndexPtr    index_;        // additional indices
    BodyList    bodies_;       // all bodies
    AtomList    atoms_;        // all atoms
    DisjList    disjunctions_; // all (head) disjunctions
    RuleList    minimize_;     // list of minimize rules
    RuleList    extended_;     // extended rules to be translated
    ShowVec     show_;         // shown atoms/conditions
    VarVec      initialSupp_;  // bodies that are (initially) supported
    VarVec      propQ_;        // assigned atoms
    VarVec      frozen_;       // list of frozen atoms
    LpLitVec    assume_;       // set of assumptions
    NonHcfSet   nonHcfs_;      // set of non-hcf sccs
    TheoryData  theory_;       // map of theory data
    AtomRange   input_;        // input atoms of current step
    int         statsId_;      // which stats to update (0 or 1)
    AuxPtr      auxData_;      // additional state for handling extended constructs
    struct Incremental {
        // first: last atom of step, second: true var
        using StepTrue = std::pair<uint32_t, uint32_t>;
        using TrueVec  = PodVector_t<StepTrue>;
        VarVec   unfreeze;     // list of atoms to unfreeze in this step
        VarVec   doms;         // list of atom variables with domain modification
        TrueVec  steps;        // map of steps to true var
        uint32_t startScc = 0; // first valid scc number in this iteration
        bool     first    = true;
    };
    IncPtr     incData_; // additional state for handling incrementally defined programs
    AspOptions opts_;    // preprocessing
};
constexpr Id_t id(Potassco::Lit_t lit) { return static_cast<Id_t>(lit); }
constexpr Id_t id(Potassco::Atom_t a) { return static_cast<Id_t>(a); }
//! Returns the internal solver literal that is associated with the given atom literal.
/*!
 * \pre The prg is frozen and atomLit is a known atom in prg.
 */
inline Literal solverLiteral(const LogicProgram& prg, Potassco::Lit_t atomLit) {
    POTASSCO_CHECK_PRE(prg.frozen() && prg.validAtom(Potassco::atom(atomLit)));
    return prg.getLiteral(id(atomLit));
}
//! Returns whether `atomLit` is a consequence wrt the given model and the current projection mode.
/*!
 * \return `value_true` if `atomLit` is a consequence, `value_false` if it is not a consequence, and
 *         `value_free` if the state is still unknown.
 */
Val_t isConsequence(const LogicProgram& prg, Potassco::Lit_t atomLit, const Model& model);
//! Adapts a LogicProgram object to the Potassco::AbstractProgram interface.
class LogicProgramAdapter final : public Potassco::AbstractProgram {
public:
    struct Options {
        bool removeMinimize = false;
    };
    explicit LogicProgramAdapter(LogicProgram& prg, const Options& opts);
    explicit LogicProgramAdapter(LogicProgram& prg);
    void initProgram(bool inc) override;
    void beginStep() override;
    void endStep() override;
    void rule(HeadType ht, Potassco::AtomSpan head, Potassco::LitSpan body) override;
    void rule(HeadType ht, Potassco::AtomSpan head, Potassco::Weight_t bound, WeightLitSpan body) override;
    void minimize(Potassco::Weight_t prio, WeightLitSpan lits) override;
    void project(Potassco::AtomSpan atoms) override;
    void output(std::string_view str, Potassco::LitSpan cond) override;
    void outputAtom(Atom_t, const Potassco::ConstString& n) override;
    void external(Atom_t a, Potassco::TruthValue v) override;
    void assume(Potassco::LitSpan lits) override;
    void heuristic(Atom_t a, Potassco::DomModifier t, int bias, unsigned prio, Potassco::LitSpan cond) override;
    void acycEdge(int s, int t, Potassco::LitSpan cond) override;
    void theoryTerm(Id_t termId, int number) override;
    void theoryTerm(Id_t termId, std::string_view name) override;
    void theoryTerm(Id_t termId, int cId, Potassco::IdSpan args) override;
    void theoryElement(Id_t elementId, Potassco::IdSpan terms, Potassco::LitSpan cond) override;
    void theoryAtom(Id_t atomOrZero, Id_t termId, Potassco::IdSpan elements) override;
    void theoryAtom(Id_t atomOrZero, Id_t termId, Potassco::IdSpan elements, Id_t op, Id_t rhs) override;

private:
    LogicProgram* lp_;
    Options       opts_;
    bool          inc_;
};
//@}

} // namespace Clasp::Asp
