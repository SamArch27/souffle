/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
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

#include "Argument.h"
#include "Node.h"
#include "SrcLocation.h"
#include <cstddef>
#include <ostream>
#include <string>
#include <utility>

namespace souffle {

/**
 * @class AstSubroutineArgument
 * @brief Defines the argument class for subrountines
 */
class AstSubroutineArgument : public AstArgument {
public:
    AstSubroutineArgument(size_t index, SrcLocation loc = {}) : AstArgument(std::move(loc)), index(index) {}

    /** Return argument index */
    size_t getNumber() const {
        return index;
    }

    AstSubroutineArgument* clone() const override {
        return new AstSubroutineArgument(index, getSrcLoc());
    }

protected:
    void print(std::ostream& os) const override {
        os << "arg(" << index << ")";
    }

    bool equal(const AstNode& node) const override {
        const auto& other = static_cast<const AstSubroutineArgument&>(node);
        return index == other.index;
    }

private:
    /** Index of subroutine argument */
    size_t index;
};

}  // end of namespace souffle
