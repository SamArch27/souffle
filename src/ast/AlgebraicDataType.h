/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file AlgebraicDataType.h
 *
 * Defines a node corresponding to an ast declaration of Algebraic Data Type
 *
 ***********************************************************************/

#pragma once

#include "ast/BranchDeclaration.h"
#include "ast/Type.h"
#include "parser/SrcLocation.h"
#include "souffle/utility/tinyformat.h"

namespace souffle {

/**
 * @class AstAlgebraicDataType
 * @brief Combination of types using sums and products.
 *
 * ADT combines a simpler types using product types and sum types.
 *
 * Example:
 * .type Nat = S {n : Nat} | Zero {}
 *
 * The type Nat has two branches, S which takes element of type Nat and Zero which doesn't take any
 * arguments.
 *
 */
class AstAlgebraicDataType : public AstType {
public:
    AstAlgebraicDataType(AstQualifiedName name, VecOwn<AstBranchDeclaration> branches, SrcLocation loc = {})
            : AstType(std::move(name), std::move(loc)), branches(std::move(branches)) {
        assert(!this->branches.empty());
    };

    std::vector<AstBranchDeclaration*> getBranches() const {
        return toPtrVector(branches);
    }

    void print(std::ostream& os) const override {
        os << tfm::format(".type %s = %s", getQualifiedName(), join(branches, " | "));
    }

    AstAlgebraicDataType* clone() const override {
        return new AstAlgebraicDataType(getQualifiedName(), souffle::clone(branches), getSrcLoc());
    }

protected:
    bool equal(const AstNode& node) const override {
        const auto& other = dynamic_cast<const AstAlgebraicDataType&>(node);
        return getQualifiedName() == other.getQualifiedName() && branches == other.branches;
    }

private:
    /** The list of branches for this sum type. */
    VecOwn<AstBranchDeclaration> branches;
};

}  // namespace souffle
