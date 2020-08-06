/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Variable.h
 *
 * Define the variable class
 *
 ***********************************************************************/

#pragma once

#include "Argument.h"
#include "Node.h"
#include "SrcLocation.h"
#include <ostream>
#include <string>
#include <utility>

namespace souffle {

/**
 * @class AstVariable
 * @brief Named variable class
 */
class AstVariable : public AstArgument {
public:
    AstVariable(std::string name, SrcLocation loc = {})
            : AstArgument(std::move(loc)), name(std::move(name)) {}

    /** Set variable name */
    void setName(std::string name) {
        this->name = std::move(name);
    }

    /** Return variable name */
    const std::string& getName() const {
        return name;
    }

    AstVariable* clone() const override {
        return new AstVariable(name, getSrcLoc());
    }

protected:
    void print(std::ostream& os) const override {
        os << name;
    }

    bool equal(const AstNode& node) const override {
        const auto& other = static_cast<const AstVariable&>(node);
        return name == other.name;
    }

    /** Name */
    std::string name;
};

}  // end of namespace souffle
