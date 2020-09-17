/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file AbstractChoice.h
 *
 ***********************************************************************/

#pragma once

#include "ram/Condition.h"
#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "souffle/utility/ContainerUtil.h"
#include <cassert>
#include <memory>
#include <utility>
#include <vector>

namespace souffle::ram {

/**
 * @class AbstractChoice
 * @brief Abstract class for a choice operation
 *
 * Finding a single tuple, if it exists, such that a condition holds.
 */
class AbstractChoice {
public:
    AbstractChoice(Own<Condition> cond) : condition(std::move(cond)) {
        assert(condition != nullptr && "Condition is a null-pointer");
    }

    /** @brief Getter for the condition */
    const Condition& getCondition() const {
        assert(condition != nullptr && "condition of choice is a null-pointer");
        return *condition;
    }

    void apply(const NodeMapper& map) {
        condition = map(std::move(condition));
    }

    std::vector<const Node*> getChildNodes() const {
        return {condition.get()};
    }

protected:
    bool equal(const Node& node) const {
        const auto& other = dynamic_cast<const AbstractChoice&>(node);
        return equal_ptr(condition, other.condition);
    }

    /** Condition for which a tuple in the relation may hold */
    Own<Condition> condition;
};
}  // namespace souffle::ram
