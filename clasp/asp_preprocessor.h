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
namespace Clasp::Asp {

/**
 * \addtogroup asp
 */
//@{

//! Preprocesses (i.e. simplifies) a logic program.
/*!
 * Preprocesses (i.e. simplifies) a logic program and associates variables with
 * the nodes of the simplified logic program.
 */
class Preprocessor {
public:
    Preprocessor()                               = default;
    Preprocessor(const Preprocessor&)            = delete;
    Preprocessor& operator=(const Preprocessor&) = delete;

    //! Possible eq-preprocessing types.
    enum EqType {
        no_eq,  //!< No eq-preprocessing, associate a new var with each supported atom and body.
        full_eq //!< Check for all kinds of equivalences between atoms and bodies.
    };

    [[nodiscard]] const LogicProgram* program() const { return prg_; }
    LogicProgram*                     program() { return prg_; }

    //! Starts preprocessing of the logic program.
    /*!
     * Computes the maximum consequences of prg and associates a variable
     * with each supported atom and body.
     * \param prg The logic program to preprocess.
     * \param t   Type of eq-preprocessing.
     * \param maxIters If t == full_eq, maximal number of iterations during eq preprocessing.
     * \param dfs If t == full_eq, classify in df-order (true) or bf-order (false).
     */
    bool preprocess(LogicProgram& prg, EqType t, uint32_t maxIters, bool dfs = true) {
        prg_  = &prg;
        dfs_  = dfs;
        type_ = t;
        return t == full_eq ? preprocessEq(maxIters) : preprocessSimple();
    }

    [[nodiscard]] bool  eq() const { return type_ == full_eq; }
    [[nodiscard]] Var_t getRootAtom(Literal p) const {
        return p.id() < litToNode_.size() ? litToNode_[p.id()] : var_max;
    }
    void setRootAtom(Literal p, uint32_t atomId) {
        if (p.id() >= litToNode_.size()) {
            litToNode_.resize(p.id() + 1, var_max);
        }
        litToNode_[p.id()] = atomId;
    }

private:
    bool preprocessEq(uint32_t maxIters);
    bool preprocessSimple();
    // ------------------------------------------------------------------------
    // Eq-Preprocessing
    struct BodyExtra {
        uint32_t known : 30 {0}; // Number of predecessors already classified, only used for bodies
        uint32_t mBody : 1 {0};  // A flag for marking bodies
        uint32_t bSeen : 1 {0};  // First time we see this body?
    };
    bool     classifyProgram();
    Val_t    simplifyClassifiedProgram(bool more);
    PrgBody* addBodyVar(uint32_t bodyId);
    bool     addHeadsToUpper(const PrgBody* body);
    bool     addDisjToUpper(PrgDisj* disj, PrgEdge support);
    bool     addAtomToUpper(PrgAtom* atom, PrgEdge support);
    bool     addToUpper(PrgHead* head, PrgEdge support);
    bool     propagateAtomVar(PrgAtom*, PrgEdge source);
    bool     propagateAtomValue(PrgAtom*, Val_t val, PrgEdge source);
    bool     mergeEqBodies(PrgBody* b, uint32_t rootId, bool equalLits);
    bool     hasRootLiteral(const PrgBody* b) const;
    bool     superfluous(const PrgBody* b) const;
    Val_t    simplifyHead(PrgHead* h, bool reclassify);
    Val_t    simplifyBody(PrgBody* b, bool reclassify, VarVec& supported);
    uint32_t popFollow(uint32_t& idx);
    // ------------------------------------------------------------------------
    using BodyData     = PodVector_t<BodyExtra>;
    LogicProgram* prg_ = nullptr;   // program to preprocess
    VarVec        follow_;          // bodies yet to classify
    BodyData      bodyInfo_;        // information about the program nodes
    VarVec        litToNode_;       // the roots of our equivalence classes
    uint32_t      pass_    = 0;     // current iteration number
    uint32_t      maxPass_ = 0;     // force stop after maxPass_ iterations
    EqType        type_    = no_eq; // type of eq-preprocessing
    bool          dfs_     = true;  // classify bodies in DF or BF order
};
//@}
} // namespace Clasp::Asp
