/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ParallelIndexChoice.h
 *
 ***********************************************************************/

#pragma once

#include "AggregateOp.h"
#include "ram/AbstractParallel.h"
#include "ram/Condition.h"
#include "ram/Expression.h"
#include "ram/IndexChoice.h"
#include "ram/IndexOperation.h"
#include "ram/NestedOperation.h"
#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "ram/Relation.h"
#include "ram/Utils.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <cassert>
#include <cstddef>
#include <iosfwd>
#include <memory>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle::ram {

/**
 * @class ParallelIndexChoice
 * @brief Use an index to find a tuple in a relation such that a given condition holds in parallel.
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *  QUERY
 *   ...
 *    PARALLEL CHOICE A AS t1 ON INDEX t1.x=10 AND t1.y = 20
 *    WHERE (t1.x, t1.y) NOT IN A
 *      ...
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class ParallelIndexChoice : public IndexChoice, public AbstractParallel {
public:
    ParallelIndexChoice(Own<RelationReference> r, int ident, Own<Condition> cond, RamPattern queryPattern,
            Own<Operation> nested, std::string profileText = "")
            : IndexChoice(std::move(r), ident, std::move(cond), std::move(queryPattern), std::move(nested),
                      profileText) {}

    ParallelIndexChoice* clone() const override {
        RamPattern resQueryPattern;
        for (const auto& i : queryPattern.first) {
            resQueryPattern.first.emplace_back(i->clone());
        }
        for (const auto& i : queryPattern.second) {
            resQueryPattern.second.emplace_back(i->clone());
        }
        auto* res =
                new ParallelIndexChoice(souffle::clone(relationRef), getTupleId(), souffle::clone(condition),
                        std::move(resQueryPattern), souffle::clone(&getOperation()), getProfileText());
        return res;
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        const Relation& rel = getRelation();
        os << times(" ", tabpos);
        os << "PARALLEL CHOICE " << rel.getName() << " AS t" << getTupleId();
        printIndex(os);
        os << " WHERE " << getCondition();
        os << std::endl;
        IndexOperation::print(os, tabpos + 1);
    }
};

}  // namespace souffle::ram
