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

#include <clasp/solver_strategies.h>
/*!
 * \file
 * \brief Defines top-level functions for solving problems.
 */
namespace Clasp {

///! \addtogroup enumerator
//@{

//! Type for holding global solve limits.
struct SolveLimits {
    explicit SolveLimits(uint64_t conf = UINT64_MAX, uint64_t r = UINT64_MAX) : conflicts(conf), restarts(r) {}
    [[nodiscard]] bool reached() const { return conflicts == 0 || restarts == 0; }
    [[nodiscard]] bool enabled() const { return conflicts != UINT64_MAX || restarts != UINT64_MAX; }
    uint64_t           conflicts; /*!< Number of conflicts. */
    uint64_t           restarts;  /*!< Number of restarts.  */
};

///////////////////////////////////////////////////////////////////////////////
// Basic solving
///////////////////////////////////////////////////////////////////////////////
//! Basic (sequential) solving using given solving options.
class BasicSolve {
public:
    //! Creates a new object for solving with the given solver using the given solving options.
    /*!
     * If an optional solve limit is given, solving stops once this limit is reached.
     * \pre s is attached to a problem (SharedContext).
     */
    BasicSolve(Solver& s, const SolveParams& p, const SolveLimits& lim = SolveLimits());
    explicit BasicSolve(Solver& s, const SolveLimits& lim = SolveLimits());
    ~BasicSolve();
    BasicSolve(BasicSolve&&) = delete;

    [[nodiscard]] bool hasLimit() const { return limits_.enabled(); }

    //! Enables solving under the given assumptions.
    /*!
     * The use of assumptions allows for incremental solving. Literals contained
     * in assumptions are assumed to be true during search but can be undone thereafter.
     *
     * \param assumptions A list of unit assumptions to be assumed true.
     * \return false if assumptions are conflicting.
     */
    bool assume(LitView assumptions);

    //! Solves the path stored in the given solver using the given solving options.
    /*!
     * \return
     *    - value_true  if search stopped on a model.
     *    - value_false if the search-space was completely examined.
     *    - value_free  if the given solve limit was hit.
     *
     * \note
     *   The function maintains the current solving state (number of restarts, learnt limits, ...)
     *   between calls.
     */
    Val_t solve();
    //! Returns whether the given problem is satisfiable under the given assumptions.
    /*!
     * Calls assume(assumptions) followed by solve() but does not maintain any solving state.
     * \param assumptions Possibly empty set of assumptions to apply before solving.
     * \param init Call InitParams::randomize() before starting search?
     */
    [[nodiscard]] bool satisfiable(LitView assumptions, bool init) const;

    //! Replaces *this with BasicSolve(s, p).
    void reset(Solver& s, const SolveParams& p, const SolveLimits& lim = SolveLimits());
    //! Resets the internal solving state while keeping the solver and the solving options.
    void reset();

    Solver& solver() { return *solver_; }

private:
    struct State;
    using Params   = const SolveParams;
    using Limits   = SolveLimits;
    using StatePtr = std::unique_ptr<State>;
    Solver*  solver_; // active solver
    Params*  params_; // active solving options
    Limits   limits_; // active solving limits
    StatePtr state_;  // internal solving state
};
//! Event type for reporting basic solve events like restarts or deletion.
struct BasicSolveEvent : SolveEvent {
    //! Type of operation that emitted the event.
    enum EventOp { event_none = 0, event_deletion = 'D', event_exit = 'E', event_grow = 'G', event_restart = 'R' };
    BasicSolveEvent(const Solver& s, EventOp a_op, uint64_t cLim, uint32_t lLim)
        : SolveEvent(this, s, verbosity_max)
        , cLimit(cLim)
        , lLimit(lLim) {
        op = a_op;
    }
    uint64_t cLimit; //!< Next conflict limit
    uint32_t lLimit; //!< Next learnt limit
};
///////////////////////////////////////////////////////////////////////////////
// General solve
///////////////////////////////////////////////////////////////////////////////
class Enumerator;
//! Interface for complex solve algorithms.
/*!
 * \ingroup enumerator
 * \relates Solver
 * SolveAlgorithms implement complex algorithms like enumeration or optimization.
 */
class SolveAlgorithm {
public:
    class Path {
    public:
        using trivially_relocatable = std::true_type; // NOLINT
        constexpr Path()            = default;
        static Path acquire(LitView path);
        static Path borrow(LitView path);
        ~Path();
        Path(Path&& other) noexcept;
        Path(const Path&)                  = delete;
        Path& operator=(const Path& other) = delete;
        Path& operator=(Path&& other) noexcept;

        [[nodiscard]] const Literal* begin() const { return lits_.get(); }
        [[nodiscard]] const Literal* end() const { return lits_.get() + size_; }
        [[nodiscard]] operator LitView() const { return {lits_.get(), size_}; }
        [[nodiscard]] bool owner() const { return lits_.test<0>(); }

    private:
        using Ptr = TaggedPtr<const Literal>;
        Path(Ptr p, std::size_t sz) : lits_(p), size_(sz) {}
        Ptr         lits_{};
        std::size_t size_{0};
    };

    /*!
     * \param limit An optional solve limit applied in solve().
     */
    explicit SolveAlgorithm(const SolveLimits& limit = SolveLimits());
    virtual ~SolveAlgorithm();
    SolveAlgorithm(const SolveAlgorithm&)            = delete;
    SolveAlgorithm& operator=(const SolveAlgorithm&) = delete;

    [[nodiscard]] const SolveLimits& limits() const { return limits_; }
    [[nodiscard]] virtual bool       interrupted() const = 0;
    [[nodiscard]] const Model&       model() const;
    [[nodiscard]] LitView            unsatCore() const;

    void setEnumLimit(uint64_t m) { enumLimit_ = m; }
    void setOptLimit(SumView bound);
    void setLimits(const SolveLimits& x) { limits_ = x; }
    //! If set to false, SharedContext::report() is not called for models.
    /*!
     * \note The default is true, i.e. models are reported via SharedContext::report().
     */
    void setReportModels(bool report) { reportM_ = report; }

    //! Runs the solve algorithm.
    /*!
     * \param en      A fully initialized enumerator.
     * \param ctx     A context object containing the problem.
     * \param assume  A list of initial unit-assumptions.
     * \param onModel Optional handler to be called on each model.
     *
     * \return
     *  - true:  if the search stopped before the search-space was exceeded.
     *  - false: if the search-space was completely examined.
     *
     * \note
     * The use of assumptions allows for incremental solving. Literals contained
     * in assumptions are assumed to be true during search but are undone before solve returns.
     *
     * \note
     * Conceptually, solve() behaves as follows:
     * \code
     * start(en, ctx, assume);
     * while (next()) {
     *   if (!report(model()) || enum_limit_reached()) { stop(); }
     * }
     * return more();
     * \endcode
     * where report() notifies all registered model handlers.
     */
    bool solve(Enumerator& en, SharedContext& ctx, LitView assume = {}, ModelHandler* onModel = nullptr);

    //! Prepares the solve algorithm for enumerating models.
    /*!
     * \pre The algorithm is not yet active.
     */
    void start(Enumerator& en, SharedContext& ctx, LitView assume = {}, ModelHandler* onModel = nullptr);
    //! Searches for the next model and returns whether such a model was found.
    /*!
     * \pre start() was called.
     */
    bool next();
    //! Stops the algorithms.
    void stop();
    //! Returns whether the last search completely exhausted the search-space.
    [[nodiscard]] bool more() const;

    //! Resets solving state and sticky messages like terminate.
    /*!
     * \note The function must be called between successive calls to solve().
     */
    virtual void resetSolve() = 0;

    //! Prepares the algorithm for handling (asynchronous) calls to SolveAlgorithm::interrupt().
    virtual void enableInterrupts() = 0;

    //! Tries to terminate the current solve process.
    /*!
     * \note If enableInterrupts() was not called, SolveAlgorithm::interrupt() may return false
     * to signal that (asynchronous) termination is not supported.
     */
    bool interrupt();

protected:
    //! The actual solve algorithm.
    virtual bool doSolve(SharedContext& ctx, LitView assume) = 0;
    //! Shall return true if termination is supported, otherwise false.
    virtual bool doInterrupt() = 0;

    virtual void doStart(SharedContext& ctx, LitView assume);
    virtual auto doNext(Val_t last) -> Val_t;
    virtual void doStop();
    virtual void doDetach() = 0;

    bool                         reportModel(Solver& s) const;
    bool                         reportUnsat(Solver& s) const;
    [[nodiscard]] Enumerator&    enumerator() const { return *enum_; }
    [[nodiscard]] SharedContext& ctx() const { return *ctx_; }
    [[nodiscard]] const Path&    path() const { return path_; }
    [[nodiscard]] uint64_t       maxModels() const { return enumLimit_; }
    [[nodiscard]] bool           moreModels(const Solver& s) const;
    [[nodiscard]] bool           hasLimit(const Model& m) const;

private:
    bool reportModel(Solver& s, bool sym) const;
    bool attach(Enumerator& en, SharedContext& ctx, ModelHandler* onModel);
    void detach();

    SolveLimits    limits_;
    SharedContext* ctx_;
    Enumerator*    enum_;
    ModelHandler*  onModel_;
    Path           path_;
    LitVec         core_;
    uint64_t       enumLimit_;
    SumVec         optLimit_;
    double         time_;
    Val_t          last_;
    bool           reportM_;
};
//! A class that implements clasp's sequential solving algorithm.
class SequentialSolve : public SolveAlgorithm {
public:
    explicit SequentialSolve(const SolveLimits& limit = SolveLimits());
    [[nodiscard]] bool interrupted() const override;
    void               resetSolve() override;
    void               enableInterrupts() override;

protected:
    bool doSolve(SharedContext& ctx, LitView assume) override;
    bool doInterrupt() override;
    void doStart(SharedContext& ctx, LitView assume) override;
    auto doNext(Val_t last) -> Val_t override;
    void doStop() override;
    void doDetach() override;
    bool restart(Solver& s, LitView assume);

private:
    using SolvePtr = std::unique_ptr<BasicSolve>;
    SolvePtr     solve_;
    volatile int term_;
};

//! Options for controlling solving.
struct BasicSolveOptions {
    [[nodiscard]] SolveAlgorithm* createSolveObject() const { return new SequentialSolve(limit); }
    static uint32_t               supportedSolvers() { return 1; }
    static uint32_t               recommendedSolvers() { return 1; }
    [[nodiscard]] uint32_t        numSolver() const { return 1; }
    void                          setSolvers(uint32_t) {}
    [[nodiscard]] bool            defaultPortfolio() const { return false; }

    SolveLimits limit; //!< Solve limit (disabled by default).
};
//@}

} // namespace Clasp
