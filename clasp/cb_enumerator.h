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

#include <clasp/enumerator.h>

namespace Clasp {

//! Enumerator for computing the brave/cautious consequences of a logic program.
/*!
 * \ingroup enumerator
 */
class CBConsequences : public Enumerator {
public:
    enum Type {
        brave    = Model::brave,
        cautious = Model::cautious,
    };
    enum Algo { def, query };
    /*!
     * \param type Type of consequences to compute.
     * \param a Type of algorithm to apply if type is Cautious.
     */
    explicit CBConsequences(Type type, Algo a = def);
    ~CBConsequences() override;
    [[nodiscard]] int  modelType() const override { return type_; }
    [[nodiscard]] bool exhaustive() const override { return true; }
    [[nodiscard]] bool supportsSplitting(const SharedContext& problem) const override;
    [[nodiscard]] int  unsatType() const override;

private:
    class CBFinder;
    class QueryFinder;
    class SharedConstraint;
    using SharedRef = std::unique_ptr<SharedConstraint>;
    ConPtr    doInit(SharedContext& ctx, SharedMinimizeData* m, int numModels) override;
    void      addLit(SharedContext& ctx, Literal p);
    void      addCurrent(const Solver& s, LitVec& con, ValueVec& m, uint32_t rootL = 0);
    LitVec    cons_;
    SharedRef shared_;
    Type      type_;
    Algo      algo_;
};

} // namespace Clasp
