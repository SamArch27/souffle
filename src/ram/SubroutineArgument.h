/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file SubroutineArgument.h
 *
 * Defines a class for evaluating values in the Relational Algebra Machine
 *
 ************************************************************************/

#pragma once

#include "ram/Expression.h"
#include "ram/Node.h"
#include <cstdlib>
#include <ostream>

namespace souffle::ram {

/**
 * @class SubroutineArgument
 * @brief Access argument of a subroutine
 *
 * Arguments are number from zero 0 to n-1
 * where n is the number of arguments of the
 * subroutine.
 */
class SubroutineArgument : public Expression {
public:
    SubroutineArgument(size_t number) : number(number) {}

    /** @brief Get argument */
    size_t getArgument() const {
        return number;
    }

    SubroutineArgument* clone() const override {
        return new SubroutineArgument(number);
    }

protected:
    void print(std::ostream& os) const override {
        os << "argument(" << number << ")";
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const SubroutineArgument&>(node);
        return number == other.number;
    }

    /** Argument number */
    const size_t number;
};

}  // namespace souffle::ram
