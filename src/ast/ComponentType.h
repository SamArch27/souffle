/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ComponentType.h
 *
 * Defines the component-type class
 *
 ***********************************************************************/

#pragma once

#include "ast/Node.h"
#include "ast/QualifiedName.h"
#include "parser/SrcLocation.h"
#include "souffle/utility/StreamUtil.h"
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class AstComponentType
 * @brief Component type of a component
 *
 * Example:
 *    name < Type1, Type2, ... >
 * where name is the component name and < Type, Type, ... > is a
 * list of component type parameters (either actual or formal).
 */
class AstComponentType : public AstNode {
public:
    AstComponentType(std::string name = "", std::vector<AstQualifiedName> params = {}, SrcLocation loc = {})
            : AstNode(std::move(loc)), name(std::move(name)), typeParams(std::move(params)) {}

    /** Return component name */
    const std::string& getName() const {
        return name;
    }

    /** Set component name */
    void setName(std::string n) {
        name = std::move(n);
    }

    /** Return component type parameters */
    const std::vector<AstQualifiedName>& getTypeParameters() const {
        return typeParams;
    }

    /** Set component type parameters */
    void setTypeParameters(const std::vector<AstQualifiedName>& params) {
        typeParams = params;
    }

    AstComponentType* clone() const override {
        return new AstComponentType(name, typeParams, getSrcLoc());
    }

protected:
    void print(std::ostream& os) const override {
        os << name;
        if (!typeParams.empty()) {
            os << "<" << join(typeParams) << ">";
        }
    }

    bool equal(const AstNode& node) const override {
        const auto& other = static_cast<const AstComponentType&>(node);
        return name == other.name && typeParams == other.typeParams;
    }

private:
    /** Component name */
    std::string name;

    /** Component type parameters */
    std::vector<AstQualifiedName> typeParams;
};

}  // end of namespace souffle
