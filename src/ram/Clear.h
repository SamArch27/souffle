/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Clear.h
 *
 * Defines abstract class Statement and sub-classes for implementing the
 * Relational Algebra Machine (RAM), which is an abstract machine.
 *
 ***********************************************************************/

#pragma once

#include "ram/Relation.h"
#include "ram/RelationStatement.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <memory>
#include <ostream>
#include <string>
#include <utility>

namespace souffle {

/**
 * @class RamClear
 * @brief Delete tuples of a relation
 *
 * This retains the target relation, but cleans its content
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * CLEAR A
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamClear : public RamRelationStatement {
public:
    RamClear(std::unique_ptr<RamRelationReference> relRef) : RamRelationStatement(std::move(relRef)) {}

    RamClear* clone() const override {
        return new RamClear(souffle::clone(relationRef));
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        const RamRelation& rel = getRelation();
        os << times(" ", tabpos);
        os << "CLEAR ";
        os << rel.getName();
        os << std::endl;
    }
};

}  // end of namespace souffle
