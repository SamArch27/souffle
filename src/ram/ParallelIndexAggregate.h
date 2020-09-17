/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ParallelIndexAggregate.h
 *
 ***********************************************************************/

#pragma once

#include "AggregateOp.h"
#include "ram/AbstractAggregate.h"
#include "ram/AbstractParallel.h"
#include "ram/Condition.h"
#include "ram/Expression.h"
#include "ram/IndexAggregate.h"
#include "ram/IndexOperation.h"
#include "ram/Node.h"
#include "ram/Operation.h"
#include "ram/Relation.h"
#include "ram/Utils.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <iosfwd>
#include <memory>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle::ram {

/**
 * @class ParallelIndexAggregate
 * @brief Aggregate over values of a relation using an index in parallel
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * t0.0=sum t0.1 SEARCH t0 ∈ S ON INDEX t0.0 = number(1)
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class ParallelIndexAggregate : public IndexAggregate, public AbstractParallel {
public:
    ParallelIndexAggregate(Own<Operation> nested, AggregateOp fun, Own<RelationReference> relRef,
            Own<Expression> expression, Own<Condition> condition, RamPattern queryPattern, int ident)
            : IndexAggregate(std::move(nested), fun, std::move(relRef), std::move(expression),
                      std::move(condition), std::move(queryPattern), ident) {}

    ParallelIndexAggregate* clone() const override {
        RamPattern pattern;
        for (const auto& i : queryPattern.first) {
            pattern.first.emplace_back(i->clone());
        }
        for (const auto& i : queryPattern.second) {
            pattern.second.emplace_back(i->clone());
        }
        return new ParallelIndexAggregate(souffle::clone(&getOperation()), function,
                souffle::clone(relationRef), souffle::clone(expression), souffle::clone(condition),
                std::move(pattern), getTupleId());
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos);
        os << "PARALLEL t" << getTupleId() << ".0=";
        AbstractAggregate::print(os, tabpos);
        os << "SEARCH t" << getTupleId() << " ∈ " << getRelation().getName();
        printIndex(os);
        if (!isTrue(condition.get())) {
            os << " WHERE " << getCondition();
        }
        os << std::endl;
        IndexOperation::print(os, tabpos + 1);
    }
};

}  // namespace souffle::ram
