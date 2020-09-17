/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020, The Souffle Developers. All rights reserved.
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file RelationSize.h
 *
 * Defines a class for returning the size of a relation.
 *
 ***********************************************************************/

#pragma once

#include "ram/Expression.h"
#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "ram/Relation.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/MiscUtil.h"
#include <cassert>
#include <memory>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

namespace souffle::ram {

/**
 * @class RelationSize
 * @brief Returns the numbers of tuples in a relation
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * size(B)
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RelationSize : public Expression {
public:
    RelationSize(Own<RelationReference> relRef) : relationRef(std::move(relRef)) {
        assert(relationRef != nullptr && "Relation reference is a nullptr");
    }

    /** @brief Get relation */
    const Relation& getRelation() const {
        return *relationRef->get();
    }

    std::vector<const Node*> getChildNodes() const override {
        return {relationRef.get()};
    }

    RelationSize* clone() const override {
        return new RelationSize(souffle::clone(relationRef));
    }

    void apply(const NodeMapper& map) override {
        relationRef = map(std::move(relationRef));
    }

protected:
    void print(std::ostream& os) const override {
        os << "size(" << getRelation().getName() << ")";
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const RelationSize&>(node);
        return equal_ptr(relationRef, other.relationRef);
    }

    /** Relation */
    Own<RelationReference> relationRef;
};

}  // namespace souffle::ram
