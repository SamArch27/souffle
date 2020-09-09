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

namespace souffle {

/**
 * @class RamRelationStatement
 * @brief RAM Statements with a single relation
 */
class RamRelationStatement : public RamStatement {
public:
    RamRelationStatement(std::unique_ptr<RamRelationReference> relRef) : relationRef(std::move(relRef)) {
        assert(relationRef != nullptr && "Relation reference is a null-pointer");
    }

    /** @brief Get RAM relation */
    const RamRelation& getRelation() const {
        return *relationRef->get();
    }

    std::vector<const RamNode*> getChildNodes() const override {
        return {relationRef.get()};
    }

    void apply(const RamNodeMapper& map) override {
        relationRef = map(std::move(relationRef));
    }

protected:
    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamRelationStatement&>(node);
        return equal_ptr(relationRef, other.relationRef);
    }

protected:
    /** Relation reference */
    std::unique_ptr<RamRelationReference> relationRef;
};

}  // end of namespace souffle
