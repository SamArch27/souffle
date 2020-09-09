/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file AbstractExistenceCheck.h
 *
 * Defines a class for evaluating conditions in the Relational Algebra
 * Machine.
 *
 ***********************************************************************/

#pragma once

#include "ram/Condition.h"
#include "ram/Expression.h"
#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "ram/Relation.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <cassert>
#include <memory>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class RamAbstractExistenceCheck
 * @brief Abstract existence check for a tuple in a relation
 */
class RamAbstractExistenceCheck : public RamCondition {
public:
    RamAbstractExistenceCheck(
            std::unique_ptr<RamRelationReference> relRef, std::vector<std::unique_ptr<RamExpression>> vals)
            : relationRef(std::move(relRef)), values(std::move(vals)) {
        assert(relationRef != nullptr && "Relation reference is a nullptr");
        for (const auto& v : values) {
            assert(v != nullptr && "value is a nullptr");
        }
    }

    /** @brief Get relation */
    const RamRelation& getRelation() const {
        return *relationRef->get();
    }

    /**
     *  @brief Get arguments of the tuple/pattern
     *  A null pointer element in the vector denotes an unspecified
     *  pattern for a tuple element.
     */
    const std::vector<RamExpression*> getValues() const {
        return toPtrVector(values);
    }

    std::vector<const RamNode*> getChildNodes() const override {
        std::vector<const RamNode*> res = {relationRef.get()};
        for (const auto& cur : values) {
            res.push_back(cur.get());
        }
        return res;
    }

    void apply(const RamNodeMapper& map) override {
        relationRef = map(std::move(relationRef));
        for (auto& val : values) {
            val = map(std::move(val));
        }
    }

protected:
    void print(std::ostream& os) const override {
        os << "("
           << join(values, ",",
                      [](std::ostream& out, const std::unique_ptr<RamExpression>& value) {
                          if (!value) {
                              out << "_";
                          } else {
                              out << *value;
                          }
                      })
           << ") ∈ " << getRelation().getName();
    }

    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamAbstractExistenceCheck&>(node);
        return equal_ptr(relationRef, other.relationRef) && equal_targets(values, other.values);
    }

    /** Relation */
    std::unique_ptr<RamRelationReference> relationRef;

    /** Pattern -- nullptr if undefined */
    std::vector<std::unique_ptr<RamExpression>> values;
};

}  // end of namespace souffle
