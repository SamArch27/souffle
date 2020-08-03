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
 * Defines a class for boolean constraints.
 *
 ***********************************************************************/

#pragma once

#include "SrcLocation.h"
#include "ast/Constraint.h"
#include "ast/Node.h"
#include <cassert>
#include <iostream>
#include <string>
#include <utility>

namespace souffle {

/**
 * Boolean Constraint
 *
 * Representing either 'true' or 'false' values
 */
class AstBooleanConstraint : public AstConstraint {
public:
    AstBooleanConstraint(bool truthValue, SrcLocation loc = {})
            : AstConstraint(std::move(loc)), truthValue(truthValue) {}

    /** check whether constraint holds */
    bool isTrue() const {
        return truthValue;
    }

    /** set truth value */
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

    /** truth value */
    bool truthValue;
};

}  // end of namespace souffle
