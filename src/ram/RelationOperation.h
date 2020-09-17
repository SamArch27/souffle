/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file RelationOperation.h
 *
 ***********************************************************************/

#pragma once

#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "ram/Operation.h"
#include "ram/Relation.h"
#include "ram/TupleOperation.h"
#include "souffle/utility/ContainerUtil.h"
#include <cassert>
#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace souffle::ram {

/**
 * @class RelationOperation
 * @brief Abstract class for operations on relations
 *
 * One such operation is a for loop
 */
class RelationOperation : public TupleOperation {
public:
    RelationOperation(
            Own<RelationReference> relRef, int ident, Own<Operation> nested, std::string profileText = "")
            : TupleOperation(ident, std::move(nested), std::move(profileText)),
              relationRef(std::move(relRef)) {
        assert(relationRef != nullptr && "relation reference is a null-pointer");
    }

    RelationOperation* clone() const override = 0;

    /** @brief Get search relation */
    const Relation& getRelation() const {
        return *relationRef->get();
    }

    void apply(const NodeMapper& map) override {
        TupleOperation::apply(map);
        relationRef = map(std::move(relationRef));
    }

    std::vector<const Node*> getChildNodes() const override {
        auto res = TupleOperation::getChildNodes();
        res.push_back(relationRef.get());
        return res;
    }

protected:
    bool equal(const Node& node) const override {
        const auto& other = static_cast<const RelationOperation&>(node);
        return TupleOperation::equal(other) && equal_ptr(relationRef, other.relationRef);
    }

    /** Search relation */
    Own<RelationReference> relationRef;
};

}  // namespace souffle::ram
