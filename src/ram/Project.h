/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Project.h
 *
 ***********************************************************************/

#pragma once

#include "ram/Expression.h"
#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "ram/Operation.h"
#include "ram/Relation.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StreamUtil.h"
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
 *     PROJECT (t0.a, t0.b, t0.c) INTO @new_X
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class Project : public Operation {
public:
    Project(Own<RelationReference> relRef, VecOwn<Expression> expressions)
            : relationRef(std::move(relRef)), expressions(std::move(expressions)) {
        assert(relationRef != nullptr && "Relation reference is a null-pointer");
        for (auto const& expr : expressions) {
            assert(expr != nullptr && "Expression is a null-pointer");
        }
    }

    /** @brief Get relation */
    const Relation& getRelation() const {
        return *relationRef->get();
    }

    /** @brief Get expressions */
    std::vector<Expression*> getValues() const {
        return toPtrVector(expressions);
    }

    std::vector<const Node*> getChildNodes() const override {
        std::vector<const Node*> res;
        res.push_back(relationRef.get());
        for (const auto& expr : expressions) {
            res.push_back(expr.get());
        }
        return res;
    }

    Project* clone() const override {
        VecOwn<Expression> newValues;
        for (auto& expr : expressions) {
            newValues.emplace_back(expr->clone());
        }
        return new Project(souffle::clone(relationRef), std::move(newValues));
    }

    void apply(const NodeMapper& map) override {
        relationRef = map(std::move(relationRef));
        for (auto& expr : expressions) {
            expr = map(std::move(expr));
        }
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos);
        os << "PROJECT (" << join(expressions, ", ", print_deref<Own<Expression>>()) << ") INTO "
           << getRelation().getName() << std::endl;
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const Project&>(node);
        return equal_ptr(relationRef, other.relationRef) && equal_targets(expressions, other.expressions);
    }

    /** Relation that values are projected into */
    Own<RelationReference> relationRef;

    /* Values (expressions) for projection */
    VecOwn<Expression> expressions;
};

}  // namespace souffle::ram
