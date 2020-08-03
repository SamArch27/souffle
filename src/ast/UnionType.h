/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file UnionType.h
 *
 * Defines a type, i.e., disjoint supersets of the universe
 *
 ***********************************************************************/

#pragma once

#include "SrcLocation.h"
#include "ast/Node.h"
#include "ast/QualifiedName.h"
#include "ast/Type.h"
#include "utility/StreamUtil.h"
#include <algorithm>
#include <cstddef>
#include <iostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * A union type combines multiple types into a new super type.
 * Each of the enumerated types become a sub-type of the new
 * union type.
 */
class AstUnionType : public AstType {
public:
    AstUnionType(AstQualifiedName name, std::vector<AstQualifiedName> types, SrcLocation loc = {})
            : AstType(std::move(name), std::move(loc)), types(std::move(types)) {}

    /** Obtains a reference to the list element types */
    const std::vector<AstQualifiedName>& getTypes() const {
        return types;
    }

    /** Adds another element type */
    void add(AstQualifiedName type) {
        types.push_back(std::move(type));
    }

    /** Set variant type */
    void setVariantType(size_t idx, AstQualifiedName type) {
        types.at(idx) = std::move(type);
    }

    AstUnionType* clone() const override {
        return new AstUnionType(getQualifiedName(), types, getSrcLoc());
    }

protected:
    void print(std::ostream& os) const override {
        os << ".type " << getQualifiedName() << " = " << join(types, " | ");
    }

    bool equal(const AstNode& node) const override {
        const auto& other = static_cast<const AstUnionType&>(node);
        return getQualifiedName() == other.getQualifiedName() && types == other.types;
    }

private:
    /** The list of types aggregated by this union type */
    std::vector<AstQualifiedName> types;
};

}  // end of namespace souffle
