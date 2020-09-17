/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file RelationStatement.h
 *
 ***********************************************************************/

#pragma once

#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "ram/Relation.h"
#include "ram/Statement.h"
#include "souffle/utility/ContainerUtil.h"
#include <cassert>
#include <memory>
#include <utility>
#include <vector>

namespace souffle::ram {

/**
 * @class RelationStatement
 * @brief RAM Statements with a single relation
 */
class RelationStatement : public Statement {
public:
    RelationStatement(Own<RelationReference> relRef) : relationRef(std::move(relRef)) {
        assert(relationRef != nullptr && "Relation reference is a null-pointer");
    }

    /** @brief Get RAM relation */
    const Relation& getRelation() const {
        return *relationRef->get();
    }

    std::vector<const Node*> getChildNodes() const override {
        return {relationRef.get()};
    }

    void apply(const NodeMapper& map) override {
        relationRef = map(std::move(relationRef));
    }

protected:
    bool equal(const Node& node) const override {
        const auto& other = static_cast<const RelationStatement&>(node);
        return equal_ptr(relationRef, other.relationRef);
    }

protected:
    /** Relation reference */
    Own<RelationReference> relationRef;
};

}  // namespace souffle::ram
