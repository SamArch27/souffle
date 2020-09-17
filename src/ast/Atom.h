/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Atom.h
 *
 * Defines the atom class
 *
 ***********************************************************************/

#pragma once

#include "ast/Argument.h"
#include "ast/Literal.h"
#include "ast/Node.h"
#include "ast/QualifiedName.h"
#include "ast/utility/NodeMapper.h"
#include "parser/SrcLocation.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <algorithm>
#include <cstddef>
#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace souffle::ast {

/**
 * @class Atom
 * @brief An atom class
 *
 * An atom representing the use of a relation
 * either in the head or in the body of a clause,
 * e.g., parent(x,y), !parent(x,y), ...
 */
class Atom : public Literal {
public:
    Atom(QualifiedName name = {}, VecOwn<Argument> args = {}, SrcLocation loc = {})
            : Literal(std::move(loc)), name(std::move(name)), arguments(std::move(args)) {}

    /** Return qualified name */
    const QualifiedName& getQualifiedName() const {
        return name;
    }

    /** Return arity of the atom */
    size_t getArity() const {
        return arguments.size();
    }

    /** Set qualified name */
    void setQualifiedName(QualifiedName n) {
        name = std::move(n);
    }

    /** Add argument to the atom */
    void addArgument(Own<Argument> arg) {
        arguments.push_back(std::move(arg));
    }

    /** Return arguments */
    std::vector<Argument*> getArguments() const {
        return toPtrVector(arguments);
    }

    Atom* clone() const override {
        return new Atom(name, souffle::clone(arguments), getSrcLoc());
    }

    void apply(const NodeMapper& map) override {
        for (auto& arg : arguments) {
            arg = map(std::move(arg));
        }
    }

    std::vector<const Node*> getChildNodes() const override {
        std::vector<const Node*> res;
        for (auto& cur : arguments) {
            res.push_back(cur.get());
        }
        return res;
    }

protected:
    void print(std::ostream& os) const override {
        os << getQualifiedName() << "(" << join(arguments) << ")";
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const Atom&>(node);
        return name == other.name && equal_targets(arguments, other.arguments);
    }

    /** Name of atom */
    QualifiedName name;

    /** Arguments of atom */
    VecOwn<Argument> arguments;
};

}  // namespace souffle::ast
