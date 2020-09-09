/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file AbstractOperator.h
 *
 * Defines a class for evaluating values in the Relational Algebra Machine
 *
 ************************************************************************/

#pragma once

#include "ram/Expression.h"
#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "souffle/utility/ContainerUtil.h"
#include <cassert>
#include <memory>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class RamAbstractOperator
 * @brief Abstract class for an operator/functor
 */
class RamAbstractOperator : public RamExpression {
public:
    explicit RamAbstractOperator(std::vector<std::unique_ptr<RamExpression>> args)
            : arguments(std::move(args)) {
        for (auto const& arg : arguments) {
            assert(arg != nullptr && "argument is null-pointer");
        }
    }

    /** @brief Get argument values */
    std::vector<RamExpression*> getArguments() const {
        return toPtrVector(arguments);
    }

    std::vector<const RamNode*> getChildNodes() const override {
        std::vector<const RamNode*> res;
        for (const auto& cur : arguments) {
            res.push_back(cur.get());
        }
        return res;
    }

    void apply(const RamNodeMapper& map) override {
        for (auto& arg : arguments) {
            arg = map(std::move(arg));
        }
    }

protected:
    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamAbstractOperator&>(node);
        return equal_targets(arguments, other.arguments);
    }

    /** Arguments of user defined operator */
    std::vector<std::unique_ptr<RamExpression>> arguments;
};

}  // end of namespace souffle
