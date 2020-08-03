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
 * Defines the class utilized to model a component within the input program.
 *
 ***********************************************************************/

#pragma once

#include "SrcLocation.h"
#include "ast/Node.h"
#include "ast/QualifiedName.h"
#include "utility/StreamUtil.h"
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * A component type is
 *
 *                  name < Type1, Type2, ... >
 *
 * where name is the component name and < Type, Type, ... > is a
 * list of component type parameters (either actual or formal).
 */
class AstComponentType : public AstNode {
public:
    AstComponentType(std::string name = "", std::vector<AstQualifiedName> params = {}, SrcLocation loc = {})
            : AstNode(std::move(loc)), name(std::move(name)), typeParams(std::move(params)) {}

    /** get component name */
    const std::string& getName() const {
        return name;
    }

    /** set component name */
    void setName(std::string n) {
        name = std::move(n);
    }

    /** get component type parameters */
    const std::vector<AstQualifiedName>& getTypeParameters() const {
        return typeParams;
    }

    /** set component type parameters */
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
    /** component name */
    std::string name;

    /** component type parameters */
    std::vector<AstQualifiedName> typeParams;
};

}  // end of namespace souffle
