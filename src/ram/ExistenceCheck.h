/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ExistenceCheck.h
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
#include <utility>
#include <vector>

namespace souffle::ram {

/**
 * @class ExistenceCheck
 * @brief Existence check for a tuple(-pattern) in a relation
 *
 * Returns true if the tuple is in the relation
 *
 * The following condition is evaluated to true if the
 * tuple element t0.1 is in the relation A:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * t0.1 IN A
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class ExistenceCheck : public AbstractExistenceCheck {
public:
    ExistenceCheck(Own<RelationReference> relRef, VecOwn<Expression> vals)
            : AbstractExistenceCheck(std::move(relRef), std::move(vals)) {}

    ExistenceCheck* clone() const override {
        VecOwn<Expression> newValues;
        for (auto& cur : values) {
            newValues.emplace_back(cur->clone());
        }
        return new ExistenceCheck(souffle::clone(relationRef), std::move(newValues));
    }
};

}  // namespace souffle::ram
