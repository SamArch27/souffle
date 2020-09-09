/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file IndexScan.h
 *
 ***********************************************************************/

#pragma once

#include "ram/Expression.h"
#include "ram/IndexOperation.h"
#include "ram/Operation.h"
#include "ram/Relation.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <iosfwd>
#include <memory>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/** Pattern type for lower/upper bound */
using RamPattern =
        std::pair<std::vector<std::unique_ptr<RamExpression>>, std::vector<std::unique_ptr<RamExpression>>>;

/**
 * @class RamIndexScan
 * @brief Search for tuples of a relation matching a criteria
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *  QUERY
 *   ...
 *	 FOR t1 IN X ON INDEX t1.c = t0.0
 *	 ...
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamIndexScan : public RamIndexOperation {
public:
    RamIndexScan(std::unique_ptr<RamRelationReference> r, int ident, RamPattern queryPattern,
            std::unique_ptr<RamOperation> nested, std::string profileText = "")
            : RamIndexOperation(std::move(r), ident, std::move(queryPattern), std::move(nested),
                      std::move(profileText)) {}

    RamIndexScan* clone() const override {
        RamPattern resQueryPattern;
        for (const auto& i : queryPattern.first) {
            resQueryPattern.first.emplace_back(i->clone());
        }
        for (const auto& i : queryPattern.second) {
            resQueryPattern.second.emplace_back(i->clone());
        }
        return new RamIndexScan(souffle::clone(relationRef), getTupleId(), std::move(resQueryPattern),
                souffle::clone(&getOperation()), getProfileText());
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        const RamRelation& rel = getRelation();
        os << times(" ", tabpos);
        os << "FOR t" << getTupleId() << " IN ";
        os << rel.getName();
        printIndex(os);
        os << std::endl;
        RamIndexOperation::print(os, tabpos + 1);
    }
};

}  // namespace souffle
