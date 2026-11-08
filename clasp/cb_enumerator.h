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
class SharedLiterals;

//! Enumerator for computing the brave/cautious consequences of a logic program.
/*!
 * \ingroup enumerator
 */
class CBConsequences : public Enumerator {
public:
    using Strategy = EnumOptions::ConsStrategy;
    enum Type {
        brave    = Model::brave,
        cautious = Model::cautious,
    };
    /*!
     * \param type Type of consequences to compute.
     * \param strat Computation strategy to use.
     */
    explicit CBConsequences(Type type, Strategy strat = EnumOptions::cons_model);
    ~CBConsequences() override;
    [[nodiscard]] int  modelType() const override { return type_; }
    [[nodiscard]] bool exhaustive() const override { return true; }
    [[nodiscard]] bool supportsSplitting(const SharedContext& problem) const override;
    [[nodiscard]] int  unsatType() const override;

private:
    class ModelFinder;
    class QueryFinder;
    using SharedConstraint = LockedValue<SharedLiterals*>;
    auto doInit(SharedContext& ctx, SharedMinimizeData* m, int numModels) -> ConPtr override;
    void addLit(SharedContext& ctx, Literal p, bool flag);
    void setShared(SharedLiterals* lits);

    LitVec           candidates_;
    SharedConstraint shared_;
    Type             type_;
    Strategy         strategy_;
};

} // namespace Clasp
