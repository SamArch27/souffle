/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file SubsetType.h
 *
 * Defines the subset type class
 *
 ***********************************************************************/

#pragma once

#include "ast/Node.h"
#include "ast/QualifiedName.h"
#include "ast/Type.h"
#include "parser/SrcLocation.h"
#include <iostream>
#include <string>
#include <utility>

namespace souffle::ast {

/**
 * @class SubsetType
 * @brief Defines subset type class
 *
 * Example:
 *    .type A <: B
 */
class SubsetType : public Type {
public:
    SubsetType(QualifiedName name, QualifiedName baseTypeName, SrcLocation loc = {})
            : Type(std::move(name), std::move(loc)), baseType(std::move(baseTypeName)) {}

    SubsetType* clone() const override {
        return new SubsetType(getQualifiedName(), getBaseType(), getSrcLoc());
    }

    /** Return base type */
    const QualifiedName& getBaseType() const {
        return baseType;
    }

protected:
    void print(std::ostream& os) const override {
        os << ".type " << getQualifiedName() << " <: " << getBaseType();
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const SubsetType&>(node);
        return getQualifiedName() == other.getQualifiedName() && baseType == other.baseType;
    }

private:
    /** Base type */
    const QualifiedName baseType;
};

}  // namespace souffle::ast
