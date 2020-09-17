/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ExecutionPlan.h
 *
 * Defines an execution plan class
 *
 ***********************************************************************/

#pragma once

#include "ast/ExecutionOrder.h"
#include "ast/Node.h"
#include "ast/utility/NodeMapper.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <algorithm>
#include <map>
#include <memory>
#include <ostream>
#include <utility>
#include <vector>

namespace souffle::ast {

/**
 * @brief ExecutionPlan
 * @class Defines a user-defined execution plan for a clause.
 *
 * An user-defined execution plan consists of one or more
 * execution orders. An execution order is a permutation
 * of atoms in a clause.
 *
 * Example:
 *   .plan 0:(1,2,3), 2:(3,2,1)
 *
 */
class ExecutionPlan : public Node {
public:
    /** Set execution order for a given rule version */
    void setOrderFor(int version, Own<ExecutionOrder> plan) {
        plans[version] = std::move(plan);
    }

    /** Get orders */
    std::map<int, const ExecutionOrder*> getOrders() const {
        std::map<int, const ExecutionOrder*> result;
        for (auto& plan : plans) {
            result.insert(std::make_pair(plan.first, plan.second.get()));
        }
        return result;
    }

    ExecutionPlan* clone() const override {
        auto res = new ExecutionPlan();
        res->setSrcLoc(getSrcLoc());
        for (auto& plan : plans) {
            res->setOrderFor(plan.first, Own<ExecutionOrder>(plan.second->clone()));
        }
        return res;
    }

    void apply(const NodeMapper& map) override {
        for (auto& plan : plans) {
            plan.second = map(std::move(plan.second));
        }
    }

    std::vector<const Node*> getChildNodes() const override {
        std::vector<const Node*> childNodes;
        for (auto& plan : plans) {
            childNodes.push_back(plan.second.get());
        }
        return childNodes;
    }

protected:
    void print(std::ostream& out) const override {
        if (!plans.empty()) {
            out << " .plan ";
            out << join(plans, ", ",
                    [](std::ostream& os, const auto& arg) { os << arg.first << ":" << *arg.second; });
        }
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const ExecutionPlan&>(node);
        return equal_targets(plans, other.plans);
    }

private:
    /** Mapping versions of clauses to execution orders */
    std::map<int, Own<ExecutionOrder>> plans;
};

}  // namespace souffle::ast
