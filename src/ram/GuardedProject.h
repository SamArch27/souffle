/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file GuardedProject.h
 *
 ***********************************************************************/

#pragma once

#include "ram/ExistenceCheck.h"
#include "ram/Project.h"
#include "ram/utility/Utils.h"
#include <cassert>
#include <iosfwd>
#include <memory>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle::ram {

/**
 * @class Project
 * @brief Project a result into the target relation.
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * FOR t0 IN A
 *   ...
 *     PROJECT (t0.a, t0.b, t0.c) INTO @new_X IF (c1 /\ c2 /\ ..)
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Where c1, c2 are existenceCheck.
 */

class GuardedProject : public Project {
public:
    GuardedProject(std::string rel, VecOwn<Expression> expressions, Own<Condition> condition = mk<True>())
            : Project(rel, std::move(expressions)), condition(std::move(condition)) {}

    /** @brief Get guarded condition */
    const Condition* getCondition() const {
        return condition.get();
    }

    std::vector<const Node*> getChildNodes() const override {
        std::vector<const Node*> res = Project::getChildNodes();
        res.push_back(condition.get());
        return res;
    }

    Project* clone() const override {
        VecOwn<Expression> newValues;
        for (auto& expr : expressions) {
            newValues.emplace_back(expr->clone());
        }
        Own<Condition> newCondition(condition->clone());
        return new GuardedProject(relation, std::move(newValues), std::move(newCondition));
    }

    void apply(const NodeMapper& map) override {
        for (auto& expr : expressions) {
            expr = map(std::move(expr));
        }
        condition = map(std::move(condition));
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos);
        os << "PROJECT (" << join(expressions, ", ", print_deref<Own<Expression>>()) << ") INTO " << relation;
        if (!isTrue(condition.get())) {
            os << " IF " << *condition << std::endl;
        } else {
            os << std::endl;
        }
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const GuardedProject&>(node);
        return relation == other.relation && equal_targets(expressions, other.expressions) &&
               equal_ptr(condition, other.condition);
    }

    /* Guarded condition */
    Own<Condition> condition;
};

}  // namespace souffle::ram
