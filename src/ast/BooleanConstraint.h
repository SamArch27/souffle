/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
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

#include "Constraint.h"
#include "Node.h"
#include "SrcLocation.h"
#include <cassert>
#include <iostream>
#include <string>
#include <utility>

namespace souffle {

/**
 * @class AstBooleanConstraint
 * @brief Boolean constraint class
 *
 * Example:
 *       true
 *
 * Boolean constraint representing either the 'true' or the 'false' value
 */
class AstBooleanConstraint : public AstConstraint {
public:
    AstBooleanConstraint(bool truthValue, SrcLocation loc = {})
            : AstConstraint(std::move(loc)), truthValue(truthValue) {}

    /** Check whether constraint holds */
    bool isTrue() const {
        return truthValue;
    }

    /** Set truth value */
    void set(bool value) {
        truthValue = value;
    }

    AstBooleanConstraint* clone() const override {
        return new AstBooleanConstraint(truthValue, getSrcLoc());
    }

protected:
    void print(std::ostream& os) const override {
        os << (truthValue ? "true" : "false");
    }

    bool equal(const AstNode& node) const override {
        assert(nullptr != dynamic_cast<const AstBooleanConstraint*>(&node));
        const auto& other = static_cast<const AstBooleanConstraint&>(node);
        return truthValue == other.truthValue;
    }

    /** Truth value of Boolean constraint */
    bool truthValue;
};

}  // end of namespace souffle
