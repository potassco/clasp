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

#include <clasp/claspfwd.h>
#include <clasp/literal.h>
#include <potassco/basic_types.h>

#include <iosfwd>

namespace Clasp {

/**
 * \file
 * \defgroup problem Input
 * \brief Classes and functions for defining input programs.
 */
//@{

//! Interface for defining an input program.
class ProgramBuilder {
public:
    ProgramBuilder();
    virtual ~ProgramBuilder();
    ProgramBuilder(const ProgramBuilder&)      = delete;
    ProgramBuilder& operator=(ProgramBuilder&) = delete;

    //! Starts the definition of a program.
    /*!
     * This function shall be called exactly once before a new program is defined.
     * It discards any previously added program.
     *
     * \param ctx The context object in which the program should be stored.
     */
    bool startProgram(SharedContext& ctx);
    //! Parses the given stream as a program of type() and adds it to this object.
    bool parseProgram(std::istream& prg);
    //! Unfreezes a currently frozen program.
    bool updateProgram();
    //! Loads the program into the shared context passed to startProgram().
    bool endProgram();
    //! Returns any assumptions that shall hold during solving.
    /*!
     * \pre frozen()
     */
    void getAssumptions(LitVec& out) const;
    //! Returns bounds that shall hold during minimization.
    void getWeakBounds(SumVec& out) const;
    //! Returns the type of program that is created by this builder.
    [[nodiscard]] int type() const { return doType(); }
    //! Returns true if the program is currently frozen.
    [[nodiscard]] bool frozen() const { return frozen_; }
    //! Returns true if the program is not conflicting.
    [[nodiscard]] virtual bool ok() const;
    //! Returns the stored context object.
    [[nodiscard]] SharedContext* ctx() const { return ctx_; }
    //! Returns a parser for this type of program associated with this object.
    ProgramParser& parser();

protected:
    void addMinLit(Weight_t prio, WeightLiteral x);
    void setFrozen(bool frozen) { frozen_ = frozen; }
    void setCtx(SharedContext* x) { ctx_ = x; }
    void markOutputVariables() const;

private:
    virtual bool                   doStartProgram()  = 0;
    virtual bool                   doUpdateProgram() = 0;
    virtual bool                   doEndProgram()    = 0;
    virtual void                   doGetWeakBounds(SumVec& out) const;
    virtual void                   doGetAssumptions(LitVec& out) const = 0;
    [[nodiscard]] virtual int      doType() const                      = 0;
    virtual ProgramParser*         doCreateParser()                    = 0;
    SharedContext*                 ctx_;
    std::unique_ptr<ProgramParser> parser_;
    bool                           frozen_;
};

//! A class for defining a SAT-problem in CNF.
class SatBuilder final : public ProgramBuilder {
public:
    explicit SatBuilder() = default;
    // program definition

    //! Creates necessary variables and prepares the problem.
    /*!
     * \param numVars          Number of variables to create.
     * \param hardClauseWeight Weight identifying hard clauses (0 means no weight).
     *                         Clauses added with a weight != hardClauseWeight are
     *                         considered soft clauses (see addClause()).
     * \param clauseHint       A hint on how many clauses will be added.
     */
    void prepareProblem(uint32_t numVars, Wsum_t hardClauseWeight = 0, uint32_t clauseHint = 100);
    //! Returns the number of variables in the problem.
    [[nodiscard]] Var_t numVars() const { return vars_; }
    //! Adds the given clause to the problem.
    /*!
     * The SatBuilder supports the creation of (weighted) MaxSAT problems
     * via the creation of "soft clauses". For this, clauses
     * added to this object have an associated weight cw. If cw
     * does not equal hardClauseWeight (typically 0), the clause is a
     * soft clause and not satisfying it results in a penalty of cw.
     *
     * \pre v <= numVars(), for all variables v occurring in clause.
     * \pre cw >= 0.
     * \param clause The clause to add.
     * \param cw     The weight associated with the clause.
     */
    bool addClause(LitVec& clause, Wsum_t cw = 0);
    //! Adds the given PB-constraint (sum(lits) >= bound) to the problem.
    bool addConstraint(WeightLitVec& lits, Weight_t bound);
    //! Adds min as an objective function to the problem.
    bool addObjective(WeightLitView min);
    //! Adds v to the set of projection vars.
    void addProject(Var_t v);
    //! Adds x to the set of initial assumptions.
    void addAssumption(Literal x);

private:
    using VarState = PodVector_t<uint8_t>;
    bool              doStartProgram() override;
    ProgramParser*    doCreateParser() override;
    [[nodiscard]] int doType() const override { return static_cast<int>(ProblemType::sat); }
    bool              doUpdateProgram() override { return not frozen(); }
    void              doGetAssumptions(LitVec& a) const override { a.insert(a.end(), assume_.begin(), assume_.end()); }
    bool              doEndProgram() override;
    bool              satisfied(LitVec& clause);
    bool              markAssigned();
    void              markLit(Literal x) { varState_[x.var()] |= trueValue(x); }
    void              markOcc(Literal x) { varState_[x.var()] |= static_cast<uint8_t>(trueValue(x) << 2u); }
    VarState          varState_;
    LitVec            softClauses_;
    LitVec            assume_;
    Wsum_t            hardWeight_ = 0;
    Var_t             vars_       = 0;
    uint32_t          pos_        = 0;
};

//! A class for defining a PB-problem.
class PBBuilder final : public ProgramBuilder {
public:
    PBBuilder();
    ~PBBuilder() override;

    // program definition
    //! Creates necessary variables and prepares the problem.
    /*!
     * \param numVars          Number of problem variables to create.
     * \param maxProduct       Max number of products in the problem.
     * \param maxSoft          Max number of soft constraints in the problem.
     * \param constraintHint   A hint on how many clauses will be added.
     */
    void prepareProblem(uint32_t numVars, uint32_t maxProduct, uint32_t maxSoft, uint32_t constraintHint = 100);
    //! Returns the number of variables in the problem.
    [[nodiscard]] uint32_t numVars() const { return auxVar_ - 1; }
    //! Adds the given PB-constraint to the problem.
    /*!
     * A PB-constraint consists of a list of weighted Boolean literals (lhs),
     * a comparison operator (either >= or =), and an integer bound (rhs).
     *
     * \pre v <= numVars(), for all variables v occurring in lits.
     *
     * \param lits  The lhs of the PB-constraint.
     * \param bound The rhs of the PB-constraint.
     * \param eq    If true, use '=' instead of '>=' as comparison operator.
     * \param cw    If > 0, treat constraint as soft constraint with weight cw.
     */
    bool addConstraint(WeightLitVec& lits, Weight_t bound, bool eq = false, Weight_t cw = 0);
    //! Adds the given product to the problem.
    /*!
     * The function creates the equality x == l1 && ... && ln, where x is a new
     * literal and each li is a literal in lits.
     * \pre The number of products added so far is < maxProduct that was given in prepareProblem().
     */
    Literal addProduct(LitVec& lits);
    //! Adds min as an objective function to the problem.
    bool addObjective(WeightLitView min);
    //! Adds v to the set of projection vars.
    void addProject(Var_t v);
    //! Adds x to the set of initial assumptions.
    void addAssumption(Literal x);
    //! Only allow solutions where the sum of violated soft constraint is less than bound.
    bool setSoftBound(Wsum_t bound);

private:
    struct PKey {
        LitVec      lits;
        std::size_t operator()(const PKey& k) const { return k.lits[0].rep(); }
        bool        operator()(const PKey& lhs, const PKey& rhs) const { return lhs.lits == rhs.lits; }
    };
    struct ProductIndex;
    using ProductIndexPtr = std::unique_ptr<ProductIndex>;

    bool              doStartProgram() override;
    void              doGetWeakBounds(SumVec& out) const override;
    [[nodiscard]] int doType() const override { return static_cast<int>(ProblemType::pb); }
    bool              doUpdateProgram() override { return not frozen(); }
    void              doGetAssumptions(LitVec& a) const override { a.insert(a.end(), assume_.begin(), assume_.end()); }
    ProgramParser*    doCreateParser() override;
    bool              doEndProgram() override;
    bool              productSubsumed(LitVec& lits, PKey& prod);
    void              addProductConstraints(Literal eqLit, LitVec& lits);
    Var_t             nextAuxVar();
    ProductIndexPtr   products_;
    PKey              prod_;
    LitVec            assume_;
    uint32_t          auxVar_{1};
    uint32_t          endVar_{0};
    Wsum_t            soft_{0};
};

//! Adapts a Sat or PB builder to the Potassco::AbstractProgram interface.
class BasicProgramAdapter final : public Potassco::AbstractProgram {
public:
    explicit BasicProgramAdapter(ProgramBuilder& prg);
    void initProgram(bool inc) override;
    void beginStep() override;
    void rule(Potassco::HeadType ht, Potassco::AtomSpan head, Potassco::LitSpan body) override;
    void rule(Potassco::HeadType ht, Potassco::AtomSpan head, Potassco::Weight_t bound,
              Potassco::WeightLitSpan body) override;
    void minimize(Potassco::Weight_t prio, Potassco::WeightLitSpan lits) override;

private:
    template <typename C>
    void withPrg(C&& call) const;

    ProgramBuilder* prg_;
    LitVec          clause_;
    WeightLitVec    constraint_;
    bool            sat_;
    bool            inc_;
};

} // namespace Clasp
