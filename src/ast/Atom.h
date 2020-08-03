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
 * Defines a class for atoms.
 *
 ***********************************************************************/

#pragma once

#include "SrcLocation.h"
#include "ast/Argument.h"
#include "ast/Literal.h"
#include "ast/Node.h"
#include "ast/NodeMapper.h"
#include "ast/QualifiedName.h"
#include "utility/ContainerUtil.h"
#include "utility/StreamUtil.h"
#include <algorithm>
#include <cstddef>
#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * Subclass of Literal that represents the use of a relation
 * either in the head or in the body of a Clause, e.g., parent(x,y).
 * The arguments of the atom can be variables or constants.
 */
class AstAtom : public AstLiteral {
public:
    AstAtom(AstQualifiedName name = {}, VecOwn<AstArgument> args = {}, SrcLocation loc = {})
            : AstLiteral(std::move(loc)), name(std::move(name)), arguments(std::move(args)) {}

    /** get qualified name */
    const AstQualifiedName& getQualifiedName() const {
        return name;
    }

    /** get arity of the atom */
    size_t getArity() const {
        return arguments.size();
    }

    /** set qualified name */
    void setQualifiedName(AstQualifiedName n) {
        name = std::move(n);
    }

    /** add argument to the atom */
    void addArgument(Own<AstArgument> arg) {
        arguments.push_back(std::move(arg));
    }

    /** get arguments */
    std::vector<AstArgument*> getArguments() const {
        return toPtrVector(arguments);
    }

    AstAtom* clone() const override {
        return new AstAtom(name, souffle::clone(arguments), getSrcLoc());
    }

    void apply(const AstNodeMapper& map) override {
        for (auto& arg : arguments) {
            arg = map(std::move(arg));
        }
    }

    std::vector<const AstNode*> getChildNodes() const override {
        std::vector<const AstNode*> res;
        for (auto& cur : arguments) {
            res.push_back(cur.get());
        }
        return res;
    }

protected:
    void print(std::ostream& os) const override {
        os << getQualifiedName() << "(" << join(arguments) << ")";
    }

    bool equal(const AstNode& node) const override {
        const auto& other = static_cast<const AstAtom&>(node);
        return name == other.name && equal_targets(arguments, other.arguments);
    }

    /** name */
    AstQualifiedName name;

    /** arguments */
    VecOwn<AstArgument> arguments;
};

}  // end of namespace souffle
