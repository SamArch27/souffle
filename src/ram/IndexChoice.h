/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file IndexChoice.h
 *
 ***********************************************************************/

#pragma once

#include "ram/AbstractChoice.h"
#include "ram/Condition.h"
#include "ram/Expression.h"
#include "ram/IndexOperation.h"
#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "ram/Operation.h"
#include "ram/Relation.h"
#include "ram/RelationOperation.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <cassert>
#include <iosfwd>
#include <memory>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class RamIndexChoice
 * @brief Use an index to find a tuple in a relation such that a given condition holds.
 *
 * Only one tuple is returned (if one exists), even
 * if multiple tuples satisfying the condition exist.
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *  QUERY
 *   ...
 *    CHOICE A AS t1 ON INDEX t1.x=10 AND t1.y = 20
 *    WHERE (t1.x, t1.y) NOT IN A
 *      ...
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamIndexChoice : public RamIndexOperation, public RamAbstractChoice {
public:
    RamIndexChoice(std::unique_ptr<RamRelationReference> r, int ident, std::unique_ptr<RamCondition> cond,
            RamPattern queryPattern, std::unique_ptr<RamOperation> nested, std::string profileText = "")
            : RamIndexOperation(std::move(r), ident, std::move(queryPattern), std::move(nested),
                      std::move(profileText)),
              RamAbstractChoice(std::move(cond)) {
        assert(getRangePattern().first.size() == getRelation().getArity());
        assert(getRangePattern().second.size() == getRelation().getArity());
    }

    void apply(const RamNodeMapper& map) override {
        RamRelationOperation::apply(map);
        for (auto& pattern : queryPattern.first) {
            pattern = map(std::move(pattern));
        }
        for (auto& pattern : queryPattern.second) {
            pattern = map(std::move(pattern));
        }
        RamAbstractChoice::apply(map);
    }

    std::vector<const RamNode*> getChildNodes() const override {
        auto res = RamIndexOperation::getChildNodes();
        res.push_back(RamAbstractChoice::getChildNodes().at(0));
        return res;
    }

    RamIndexChoice* clone() const override {
        RamPattern resQueryPattern;
        for (const auto& i : queryPattern.first) {
            resQueryPattern.first.emplace_back(i->clone());
        }
        for (const auto& i : queryPattern.second) {
            resQueryPattern.second.emplace_back(i->clone());
        }
        auto* res = new RamIndexChoice(souffle::clone(relationRef), getTupleId(), souffle::clone(condition),
                std::move(resQueryPattern), souffle::clone(&getOperation()), getProfileText());
        return res;
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        const RamRelation& rel = getRelation();
        os << times(" ", tabpos);
        os << "CHOICE " << rel.getName() << " AS t" << getTupleId();
        printIndex(os);
        os << " WHERE " << getCondition();
        os << std::endl;
        RamIndexOperation::print(os, tabpos + 1);
    }

    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamIndexChoice&>(node);
        return RamIndexOperation::equal(other) && RamAbstractChoice::equal(other);
    }
};

}  // namespace souffle
