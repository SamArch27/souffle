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
 * Defines the binary constraint class
 *
 ***********************************************************************/

#pragma once

#include "ast/Argument.h"
#include "ast/Constraint.h"
#include "ast/Node.h"
#include "ast/utility/NodeMapper.h"
#include "parser/SrcLocation.h"
#include "souffle/BinaryConstraintOps.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/MiscUtil.h"
#include <cassert>
#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace souffle::ast {

/**
 * @class BinaryConstraint
 * @brief Binary constraint class
 *
 * Example:
 *      x = y
 *
 * A binary constraint has a constraint operator, a left-hand side
 * expression, and right-hand side expression.
 */
class BinaryConstraint : public Constraint {
public:
    BinaryConstraint(BinaryConstraintOp o, Own<Argument> ls, Own<Argument> rs, SrcLocation loc = {})
            : Constraint(std::move(loc)), operation(o), lhs(std::move(ls)), rhs(std::move(rs)) {}

    /** Return left-hand side argument */
    Argument* getLHS() const {
        return lhs.get();
    }

    /** Return right-hand side argument */
    Argument* getRHS() const {
        return rhs.get();
    }

    /** Return binary operator */
    BinaryConstraintOp getOperator() const {
        return operation;
    }

    /** Set binary operator */
    void setOperator(BinaryConstraintOp op) {
        operation = op;
    }

    BinaryConstraint* clone() const override {
        return new BinaryConstraint(operation, souffle::clone(lhs), souffle::clone(rhs), getSrcLoc());
    }

    void apply(const NodeMapper& map) override {
        lhs = map(std::move(lhs));
        rhs = map(std::move(rhs));
    }

    std::vector<const Node*> getChildNodes() const override {
        return {lhs.get(), rhs.get()};
    }

protected:
    void print(std::ostream& os) const override {
        os << *lhs << " " << operation << " " << *rhs;
    }

    bool equal(const Node& node) const override {
        assert(isA<BinaryConstraint>(&node));
        const auto& other = static_cast<const BinaryConstraint&>(node);
        return operation == other.operation && equal_ptr(lhs, other.lhs) && equal_ptr(rhs, other.rhs);
    }

    /** Constraint operator */
    BinaryConstraintOp operation;

    /** Left-hand side argument of binary constraint */
    Own<Argument> lhs;

    /** Right-hand side argument of binary constraint */
    Own<Argument> rhs;
};

}  // namespace souffle::ast
