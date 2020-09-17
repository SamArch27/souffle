/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ParallelIndexScan.h
 *
 ***********************************************************************/

#pragma once

#include "AggregateOp.h"
#include "ram/AbstractParallel.h"
#include "ram/Condition.h"
#include "ram/Expression.h"
#include "ram/IndexOperation.h"
#include "ram/IndexScan.h"
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
 * @class ParallelIndexScan
 * @brief Search for tuples of a relation matching a criteria
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *  QUERY
 *   ...
 *	   PARALLEL FOR t1 IN X ON INDEX t1.c = t0.0
 *	     ...
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class ParallelIndexScan : public IndexScan, public AbstractParallel {
public:
    ParallelIndexScan(Own<RelationReference> rel, int ident, RamPattern queryPattern, Own<Operation> nested,
            std::string profileText = "")
            : IndexScan(std::move(rel), ident, std::move(queryPattern), std::move(nested), profileText) {}

    ParallelIndexScan* clone() const override {
        RamPattern resQueryPattern;
        for (const auto& i : queryPattern.first) {
            resQueryPattern.first.emplace_back(i->clone());
        }
        for (const auto& i : queryPattern.second) {
            resQueryPattern.second.emplace_back(i->clone());
        }
        return new ParallelIndexScan(souffle::clone(relationRef), getTupleId(), std::move(resQueryPattern),
                souffle::clone(&getOperation()), getProfileText());
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        const Relation& rel = getRelation();
        os << times(" ", tabpos);
        os << "PARALLEL FOR t" << getTupleId() << " IN ";
        os << rel.getName();
        printIndex(os);
        os << std::endl;
        IndexOperation::print(os, tabpos + 1);
    }
};

}  // namespace souffle::ram
