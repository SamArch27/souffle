/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file BinaryConstraint.h
 *
 * Defines a class for binary constraints.
 *
 ***********************************************************************/

#pragma once

#include "BinaryConstraintOps.h"
#include "SrcLocation.h"
#include "ast/Argument.h"
#include "ast/Constraint.h"
#include "ast/Node.h"
#include "ast/NodeMapper.h"
#include "utility/ContainerUtil.h"
#include "utility/MiscUtil.h"
#include <algorithm>
#include <cassert>
#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * Subclass of Constraint that represents a binary constraint
 * e.g., x = y.
 */
class AstBinaryConstraint : public AstConstraint {
public:
    AstBinaryConstraint(BinaryConstraintOp o, Own<AstArgument> ls, Own<AstArgument> rs, SrcLocation loc = {})
            : AstConstraint(std::move(loc)), operation(o), lhs(std::move(ls)), rhs(std::move(rs)) {}

    /** get LHS argument */
    AstArgument* getLHS() const {
        return lhs.get();
    }

    /** get RHS argument */
    AstArgument* getRHS() const {
        return rhs.get();
    }

    /** get binary operator */
    BinaryConstraintOp getOperator() const {
        return operation;
    }

    /** set binary operator */
    void setOperator(BinaryConstraintOp op) {
        operation = op;
    }

    AstBinaryConstraint* clone() const override {
        return new AstBinaryConstraint(operation, souffle::clone(lhs), souffle::clone(rhs), getSrcLoc());
    }

    void apply(const AstNodeMapper& map) override {
        lhs = map(std::move(lhs));
        rhs = map(std::move(rhs));
    }

    std::vector<const AstNode*> getChildNodes() const override {
        return {lhs.get(), rhs.get()};
    }

protected:
    void print(std::ostream& os) const override {
        os << *lhs << " " << operation << " " << *rhs;
    }

    bool equal(const AstNode& node) const override {
        assert(nullptr != dynamic_cast<const AstBinaryConstraint*>(&node));
        const auto& other = static_cast<const AstBinaryConstraint&>(node);
        return operation == other.operation && equal_ptr(lhs, other.lhs) && equal_ptr(rhs, other.rhs);
    }

    /** constraint operator */
    BinaryConstraintOp operation;

    /** left-hand side of binary constraint */
    Own<AstArgument> lhs;

    /** right-hand side of binary constraint */
    Own<AstArgument> rhs;
};

}  // end of namespace souffle
