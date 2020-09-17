/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file SubroutineArgument.h
 *
 * Defines the subroutine argument class
 *
 ***********************************************************************/

#pragma once

#include "ast/Argument.h"
#include "ast/Node.h"
#include "parser/SrcLocation.h"
#include <cstddef>
#include <ostream>
#include <string>
#include <utility>

namespace souffle::ast {

/**
 * @class SubroutineArgument
 * @brief Defines the argument class for subrountines
 */
class SubroutineArgument : public Argument {
public:
    SubroutineArgument(size_t index, SrcLocation loc = {}) : Argument(std::move(loc)), index(index) {}

    /** Return argument index */
    size_t getNumber() const {
        return index;
    }

    SubroutineArgument* clone() const override {
        return new SubroutineArgument(index, getSrcLoc());
    }

protected:
    void print(std::ostream& os) const override {
        os << "arg(" << index << ")";
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const SubroutineArgument&>(node);
        return index == other.index;
    }

private:
    /** Index of subroutine argument */
    size_t index;
};

}  // namespace souffle::ast
