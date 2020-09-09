/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ParallelChoice.h
 *
 ***********************************************************************/

#pragma once

#include "ram/AbstractParallel.h"
#include "ram/Choice.h"
#include "ram/Condition.h"
#include "ram/Node.h"
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

namespace souffle {

/**
 * @class ParallelRamChoice
 * @brief Find a tuple in a relation such that a given condition holds in parallel.
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *  QUERY
 *   ...
 *    PARALLEL CHOICE t1 IN A WHERE (t1.x, t1.y) NOT IN A
 *      ...
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamParallelChoice : public RamChoice, public RamAbstractParallel {
public:
    RamParallelChoice(std::unique_ptr<RamRelationReference> rel, size_t ident,
            std::unique_ptr<RamCondition> cond, std::unique_ptr<RamOperation> nested,
            std::string profileText = "")
            : RamChoice(std::move(rel), ident, std::move(cond), std::move(nested), profileText) {}

    RamParallelChoice* clone() const override {
        return new RamParallelChoice(souffle::clone(relationRef), getTupleId(), souffle::clone(condition),
                souffle::clone(&getOperation()), getProfileText());
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos);
        os << "PARALLEL CHOICE t" << getTupleId();
        os << " IN " << getRelation().getName();
        os << " WHERE " << getCondition();
        os << std::endl;
        RamRelationOperation::print(os, tabpos + 1);
    }
};

}  // namespace souffle
