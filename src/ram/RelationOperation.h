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

namespace souffle {

/**
 * @class RamRelationOperation
 * @brief Abstract class for operations on relations
 *
 * One such operation is a for loop
 */
class RamRelationOperation : public RamTupleOperation {
public:
    RamRelationOperation(std::unique_ptr<RamRelationReference> relRef, int ident,
            std::unique_ptr<RamOperation> nested, std::string profileText = "")
            : RamTupleOperation(ident, std::move(nested), std::move(profileText)),
              relationRef(std::move(relRef)) {
        assert(relationRef != nullptr && "relation reference is a null-pointer");
    }

    RamRelationOperation* clone() const override = 0;

    /** @brief Get search relation */
    const RamRelation& getRelation() const {
        return *relationRef->get();
    }

    void apply(const RamNodeMapper& map) override {
        RamTupleOperation::apply(map);
        relationRef = map(std::move(relationRef));
    }

    std::vector<const RamNode*> getChildNodes() const override {
        auto res = RamTupleOperation::getChildNodes();
        res.push_back(relationRef.get());
        return res;
    }

protected:
    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamRelationOperation&>(node);
        return RamTupleOperation::equal(other) && equal_ptr(relationRef, other.relationRef);
    }

    /** Search relation */
    std::unique_ptr<RamRelationReference> relationRef;
};

}  // namespace souffle
