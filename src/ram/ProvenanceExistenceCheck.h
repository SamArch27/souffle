/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ProvenanceExistenceCheck.h
 *
 * Defines a class for evaluating conditions in the Relational Algebra
 * Machine.
 *
 ***********************************************************************/

#pragma once

#include "ram/AbstractExistenceCheck.h"
#include "ram/Expression.h"
#include "ram/Relation.h"
#include "souffle/utility/MiscUtil.h"
#include <memory>
#include <sstream>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class RamProvenanceExistenceCheck
 * @brief Provenance Existence check for a relation
 */
class RamProvenanceExistenceCheck : public RamAbstractExistenceCheck {
public:
    RamProvenanceExistenceCheck(
            std::unique_ptr<RamRelationReference> relRef, std::vector<std::unique_ptr<RamExpression>> vals)
            : RamAbstractExistenceCheck(std::move(relRef), std::move(vals)) {}

    RamProvenanceExistenceCheck* clone() const override {
        std::vector<std::unique_ptr<RamExpression>> newValues;
        for (auto& cur : values) {
            newValues.emplace_back(cur->clone());
        }
        return new RamProvenanceExistenceCheck(souffle::clone(relationRef), std::move(newValues));
    }

protected:
    void print(std::ostream& os) const override {
        os << "prov";
        RamAbstractExistenceCheck::print(os);
    }
};

}  // end of namespace souffle
