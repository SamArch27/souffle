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
#include "ram/Operation.h"
#include "ram/Relation.h"
#include "ram/RelationOperation.h"
#include "ram/utility/NodeMapper.h"
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
 * @class IndexChoice
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
class IndexChoice : public IndexOperation, public AbstractChoice {
public:
    IndexChoice(std::string rel, int ident, Own<Condition> cond, RamPattern queryPattern,
            Own<Operation> nested, std::string profileText = "")

            : IndexOperation(rel, ident, std::move(queryPattern), std::move(nested), std::move(profileText)),
              AbstractChoice(std::move(cond)) {
        assert(getRangePattern().first.size() == getRangePattern().second.size() && "Arity mismatch");
    }

    void apply(const NodeMapper& map) override {
        RelationOperation::apply(map);
        for (auto& pattern : queryPattern.first) {
            pattern = map(std::move(pattern));
        }
        for (auto& pattern : queryPattern.second) {
            pattern = map(std::move(pattern));
        }
        AbstractChoice::apply(map);
    }

    std::vector<const Node*> getChildNodes() const override {
        auto res = IndexOperation::getChildNodes();
        res.push_back(AbstractChoice::getChildNodes().at(0));
        return res;
    }

    IndexChoice* clone() const override {
        RamPattern resQueryPattern;
        for (const auto& i : queryPattern.first) {
            resQueryPattern.first.emplace_back(i->clone());
        }
        for (const auto& i : queryPattern.second) {
            resQueryPattern.second.emplace_back(i->clone());
        }
        auto* res = new IndexChoice(relation, getTupleId(), souffle::clone(condition),
                std::move(resQueryPattern), souffle::clone(&getOperation()), getProfileText());
        return res;
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos);
        os << "CHOICE " << relation << " AS t" << getTupleId();
        printIndex(os);
        os << " WHERE " << getCondition();
        os << std::endl;
        IndexOperation::print(os, tabpos + 1);
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const IndexChoice&>(node);
        return IndexOperation::equal(other) && AbstractChoice::equal(other);
    }
};

}  // namespace souffle::ram
