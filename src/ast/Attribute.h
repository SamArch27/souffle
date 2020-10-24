/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Attribute.h
 *
 * Defines the attribute class
 *
 ***********************************************************************/

#pragma once

#include "ast/Node.h"
#include "ast/QualifiedName.h"
#include "parser/SrcLocation.h"
#include <ostream>
#include <string>
#include <utility>

namespace souffle::ast {

/**
 * @class Attribute
 * @brief Attribute class
 *
 * Example:
 *    x: number
 * An attribute consists of a name and its type name.
 */
class Attribute : public Node {
public:
    Attribute(std::string n, QualifiedName t, SrcLocation loc = {})
            : Node(std::move(loc)), name(std::move(n)), typeName(std::move(t)) {}

    /** Return attribute name */
    const std::string& getName() const {
        return name;
    }

    /** Return type name */
    const QualifiedName& getTypeName() const {
        return typeName;
    }

    /** Set type name */
    void setTypeName(QualifiedName name) {
        typeName = std::move(name);
    }

    Attribute* clone() const override {
        return new Attribute(name, typeName, getSrcLoc());
    }

protected:
    void print(std::ostream& os) const override {
        os << name << ":" << typeName;
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const Attribute&>(node);
        return name == other.name && typeName == other.typeName;
    }

private:
    /** Attribute name */
    std::string name;

    /** Type name */
    QualifiedName typeName;
};

}  // namespace souffle::ast
