/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file SubsetType.h
 *
 * Defines a type, i.e., disjoint supersets of the universe
 *
 ***********************************************************************/

#pragma once

#include "SrcLocation.h"
#include "ast/Node.h"
#include "ast/QualifiedName.h"
#include "ast/Type.h"
#include <iostream>
#include <string>
#include <utility>

namespace souffle {

/**
 * A subset type. Can be derived from any type except union.
 */
class AstSubsetType : public AstType {
public:
    AstSubsetType(AstQualifiedName name, AstQualifiedName baseTypeName, SrcLocation loc = {})
            : AstType(std::move(name), std::move(loc)), baseType(std::move(baseTypeName)) {}

    AstSubsetType* clone() const override {
        return new AstSubsetType(getQualifiedName(), getBaseType(), getSrcLoc());
    }

    const AstQualifiedName& getBaseType() const {
        return baseType;
    }

protected:
    void print(std::ostream& os) const override {
        os << ".type " << getQualifiedName() << " <: " << getBaseType();
    }

    bool equal(const AstNode& node) const override {
        const auto& other = static_cast<const AstSubsetType&>(node);
        return getQualifiedName() == other.getQualifiedName() && baseType == other.baseType;
    }

private:
    const AstQualifiedName baseType;
};

}  // end of namespace souffle
