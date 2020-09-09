/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file AbstractConditional.h
 *
 ***********************************************************************/

#pragma once

#include "ram/Condition.h"
#include "ram/NestedOperation.h"
#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "ram/Operation.h"
#include "souffle/utility/MiscUtil.h"
#include <cassert>
#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class RamAbstractConditional
 * @brief Abstract conditional statement
 */
class RamAbstractConditional : public RamNestedOperation {
public:
    RamAbstractConditional(std::unique_ptr<RamCondition> cond, std::unique_ptr<RamOperation> nested,
            std::string profileText = "")
            : RamNestedOperation(std::move(nested), std::move(profileText)), condition(std::move(cond)) {
        assert(condition != nullptr && "Condition is a null-pointer");
    }

    RamAbstractConditional* clone() const override = 0;

    /** @brief Get condition that must be satisfied */
    const RamCondition& getCondition() const {
        assert(condition != nullptr && "condition of conditional operation is a null-pointer");
        return *condition;
    }

    std::vector<const RamNode*> getChildNodes() const override {
        auto res = RamNestedOperation::getChildNodes();
        res.push_back(condition.get());
        return res;
    }

    void apply(const RamNodeMapper& map) override {
        RamNestedOperation::apply(map);
        condition = map(std::move(condition));
    }

protected:
    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamAbstractConditional&>(node);
        return RamNestedOperation::equal(node) && equal_ptr(condition, other.condition);
    }

    /** Condition */
    std::unique_ptr<RamCondition> condition;
};

}  // namespace souffle
