/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file IndexOperation.h
 *
 ***********************************************************************/

#pragma once

#include "ram/Expression.h"
#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "ram/Operation.h"
#include "ram/Relation.h"
#include "ram/RelationOperation.h"
#include "ram/Utils.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/MiscUtil.h"
#include <cassert>
#include <iosfwd>
#include <memory>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle::ram {

/** Pattern type for lower/upper bound */
using RamBound = VecOwn<Expression>;
using RamPattern = std::pair<RamBound, RamBound>;

/**
 * @class Relation Scan with Index
 * @brief An abstract class for performing indexed operations
 */
class IndexOperation : public RelationOperation {
public:
    IndexOperation(Own<RelationReference> r, int ident, RamPattern queryPattern, Own<Operation> nested,
            std::string profileText = "")
            : RelationOperation(std::move(r), ident, std::move(nested), std::move(profileText)),
              queryPattern(std::move(queryPattern)) {
        assert(getRangePattern().first.size() == getRelation().getArity() &&
                getRangePattern().second.size() == getRelation().getArity());
        for (const auto& pattern : queryPattern.first) {
            assert(pattern != nullptr && "pattern is a null-pointer");
        }
        for (const auto& pattern : queryPattern.second) {
            assert(pattern != nullptr && "pattern is a null-pointer");
        }
    }

    /**
     * @brief Get range pattern
     * @return A pair of std::vector of pointers to Expression objects
     * These vectors represent the lower and upper bounds for each attribute in the tuple
     * <expr1> <= Tuple[level, element] <= <expr2>
     * We have that at an index for an attribute, its bounds are <expr1> and <expr2> respectively
     * */
    std::pair<std::vector<Expression*>, std::vector<Expression*>> getRangePattern() const {
        return std::make_pair(toPtrVector(queryPattern.first), toPtrVector(queryPattern.second));
    }

    std::vector<const Node*> getChildNodes() const override {
        auto res = RelationOperation::getChildNodes();
        for (auto& pattern : queryPattern.first) {
            res.push_back(pattern.get());
        }
        for (auto& pattern : queryPattern.second) {
            res.push_back(pattern.get());
        }
        return res;
    }

    void apply(const NodeMapper& map) override {
        RelationOperation::apply(map);
        for (auto& pattern : queryPattern.first) {
            pattern = map(std::move(pattern));
        }
        for (auto& pattern : queryPattern.second) {
            pattern = map(std::move(pattern));
        }
    }

    IndexOperation* clone() const override {
        RamPattern resQueryPattern;
        for (const auto& i : queryPattern.first) {
            resQueryPattern.first.emplace_back(i->clone());
        }
        for (const auto& i : queryPattern.second) {
            resQueryPattern.second.emplace_back(i->clone());
        }
        return new IndexOperation(souffle::clone(relationRef), getTupleId(), std::move(resQueryPattern),
                souffle::clone(&getOperation()), getProfileText());
    }

    /** @brief Helper method for printing */
    void printIndex(std::ostream& os) const {
        //  const auto& attrib = getRelation().getAttributeNames();
        bool first = true;
        for (unsigned int i = 0; i < getRelation().getArity(); ++i) {
            // TODO: print proper upper lower/bound

            // early exit if no upper/lower bounds are defined
            if (isUndefValue(queryPattern.first[i].get()) && isUndefValue(queryPattern.second[i].get())) {
                continue;
            }

            if (first) {
                os << " ON INDEX ";
                first = false;
            } else {
                os << " AND ";
            }

            // both bounds defined and equal => equality
            if (!isUndefValue(queryPattern.first[i].get()) && !isUndefValue(queryPattern.second[i].get())) {
                // print equality when lower bound = upper bound
                if (*(queryPattern.first[i]) == *(queryPattern.second[i])) {
                    os << "t" << getTupleId() << ".";
                    os << i << " = ";
                    os << *(queryPattern.first[i]);
                    continue;
                }
            }
            // at least one bound defined => inequality
            if (!isUndefValue(queryPattern.first[i].get()) || !isUndefValue(queryPattern.second[i].get())) {
                if (!isUndefValue(queryPattern.first[i].get())) {
                    os << *(queryPattern.first[i]) << " <= ";
                }

                os << "t" << getTupleId() << ".";
                os << i;

                if (!isUndefValue(queryPattern.second[i].get())) {
                    os << " <= " << *(queryPattern.second[i]);
                }

                continue;
            }
        }
    }

protected:
    bool equal(const Node& node) const override {
        const auto& other = static_cast<const IndexOperation&>(node);
        return RelationOperation::equal(other) &&
               equal_targets(queryPattern.first, other.queryPattern.first) &&
               equal_targets(queryPattern.second, other.queryPattern.second);
    }

    /** Values of index per column of table (if indexable) */
    RamPattern queryPattern;
};

}  // namespace souffle::ram
