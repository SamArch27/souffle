/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Extend.h
 *
 ***********************************************************************/

#pragma once

#include "ram/BinRelationStatement.h"
#include "ram/Relation.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <memory>
#include <ostream>
#include <string>
#include <utility>

namespace souffle {

/**
 * @class RamExtend
 * @brief Extend equivalence relation.
 *
 * The following example merges A into B:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * EXTEND B WITH A
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamExtend : public RamBinRelationStatement {
public:
    RamExtend(std::unique_ptr<RamRelationReference> tRef, std::unique_ptr<RamRelationReference> sRef)
            : RamBinRelationStatement(std::move(sRef), std::move(tRef)) {}

    /** @brief Get source relation */
    const RamRelation& getSourceRelation() const {
        return getFirstRelation();
    }

    /** @brief Get target relation */
    const RamRelation& getTargetRelation() const {
        return getSecondRelation();
    }

    RamExtend* clone() const override {
        auto* res = new RamExtend(souffle::clone(second), souffle::clone(first));
        return res;
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos);
        os << "EXTEND " << getTargetRelation().getName() << " WITH " << getSourceRelation().getName();
        os << std::endl;
    }
};

}  // end of namespace souffle
