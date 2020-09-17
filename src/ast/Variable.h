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

#include "ast/Argument.h"
#include "ast/Node.h"
#include "parser/SrcLocation.h"
#include <ostream>
#include <string>
#include <utility>

namespace souffle::ast {

/**
 * @class Variable
 * @brief Named variable class
 */
class Variable : public Argument {
public:
    Variable(std::string name, SrcLocation loc = {}) : Argument(std::move(loc)), name(std::move(name)) {}

    /** Set variable name */
    void setName(std::string name) {
        this->name = std::move(name);
    }

    /** Return variable name */
    const std::string& getName() const {
        return name;
    }

    Variable* clone() const override {
        return new Variable(name, getSrcLoc());
    }

protected:
    void print(std::ostream& os) const override {
        os << name;
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const Variable&>(node);
        return name == other.name;
    }

    /** Name */
    std::string name;
};

}  // namespace souffle::ast
