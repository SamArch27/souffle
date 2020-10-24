/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file IntrinsicOperator.h
 *
 * Defines a class for evaluating values in the Relational Algebra Machine
 *
 ************************************************************************/

#pragma once

#include "FunctorOps.h"
#include "ram/AbstractOperator.h"
#include "ram/Expression.h"
#include "ram/Node.h"
#include "souffle/utility/StreamUtil.h"
#include "souffle/utility/tinyformat.h"
#include <memory>
#include <sstream>
#include <utility>
#include <vector>

namespace souffle::ram {

/**
 * @class IntrinsicOperator
 * @brief Operator that represents an intrinsic (built-in) functor
 */
class IntrinsicOperator : public AbstractOperator {
public:
    template <typename... Args>
    IntrinsicOperator(FunctorOp op, Args... args) : AbstractOperator({std::move(args)...}), operation(op) {}

    IntrinsicOperator(FunctorOp op, VecOwn<Expression> args)
            : AbstractOperator(std::move(args)), operation(op) {}

    /** @brief Get operator symbol */
    FunctorOp getOperator() const {
        return operation;
    }

    IntrinsicOperator* clone() const override {
        VecOwn<Expression> argsCopy;
        for (auto& arg : arguments) {
            argsCopy.emplace_back(arg->clone());
        }
        return new IntrinsicOperator(operation, std::move(argsCopy));
    }

protected:
    void print(std::ostream& os) const override {
        if (isInfixFunctorOp(operation)) {
            os << "(" << join(arguments, tfm::format("%s", operation)) << ")";
        } else {
            os << operation << "(" << join(arguments) << ")";
        }
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const IntrinsicOperator&>(node);
        return AbstractOperator::equal(node) && operation == other.operation;
    }

    /** Operation symbol */
    const FunctorOp operation;
};

}  // namespace souffle::ram
