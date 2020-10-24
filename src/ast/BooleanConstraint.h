/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file BooleanConstraint.h
 *
 * Defines the boolean constraint class
 *
 ***********************************************************************/

#pragma once

#include "ast/Constraint.h"
#include "ast/Node.h"
#include "parser/SrcLocation.h"
#include "souffle/utility/MiscUtil.h"
#include <cassert>
#include <iostream>
#include <string>
#include <utility>

namespace souffle::ast {

/**
 * @class BooleanConstraint
 * @brief Boolean constraint class
 *
 * Example:
 *       true
 *
 * Boolean constraint representing either the 'true' or the 'false' value
 */
class BooleanConstraint : public Constraint {
public:
    BooleanConstraint(bool truthValue, SrcLocation loc = {})
            : Constraint(std::move(loc)), truthValue(truthValue) {}

    /** Check whether constraint holds */
    bool isTrue() const {
        return truthValue;
    }

    /** Set truth value */
    void set(bool value) {
        truthValue = value;
    }

    BooleanConstraint* clone() const override {
        return new BooleanConstraint(truthValue, getSrcLoc());
    }

protected:
    void print(std::ostream& os) const override {
        os << (truthValue ? "true" : "false");
    }

    bool equal(const Node& node) const override {
        assert(isA<BooleanConstraint>(&node));
        const auto& other = static_cast<const BooleanConstraint&>(node);
        return truthValue == other.truthValue;
    }

    /** Truth value of Boolean constraint */
    bool truthValue;
};

}  // namespace souffle::ast
