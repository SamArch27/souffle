/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Choice.h
 *
 * Defines the Operation of a relational algebra query.
 *
 ***********************************************************************/

#pragma once

#include "ram/AbstractChoice.h"
#include "ram/Condition.h"
#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "ram/Operation.h"
#include "ram/Relation.h"
#include "ram/RelationOperation.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <cstddef>
#include <iosfwd>
#include <memory>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class RamChoice
 * @brief Find a tuple in a relation such that a given condition holds.
 *
 * Only one tuple is returned (if one exists), even
 * if multiple tuples satisfying the condition exist.
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *  QUERY
 *   ...
 *    CHOICE t1 IN A WHERE (t1.x, t1.y) NOT IN A
 *      ...
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamChoice : public RamRelationOperation, public RamAbstractChoice {
public:
    RamChoice(std::unique_ptr<RamRelationReference> rel, size_t ident, std::unique_ptr<RamCondition> cond,
            std::unique_ptr<RamOperation> nested, std::string profileText = "")
            : RamRelationOperation(std::move(rel), ident, std::move(nested), std::move(profileText)),
              RamAbstractChoice(std::move(cond)) {}

    void apply(const RamNodeMapper& map) override {
        RamRelationOperation::apply(map);
        RamAbstractChoice::apply(map);
    }

    RamChoice* clone() const override {
        return new RamChoice(souffle::clone(relationRef), getTupleId(), souffle::clone(condition),
                souffle::clone(&getOperation()), getProfileText());
    }

    std::vector<const RamNode*> getChildNodes() const override {
        return {nestedOperation.get(), relationRef.get(), RamAbstractChoice::getChildNodes().at(0)};
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos);
        os << "CHOICE t" << getTupleId();
        os << " IN " << getRelation().getName();
        os << " WHERE " << getCondition();
        os << std::endl;
        RamRelationOperation::print(os, tabpos + 1);
    }

    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamChoice&>(node);
        return RamRelationOperation::equal(other) && RamAbstractChoice::equal(other);
    }
};

}  // namespace souffle
