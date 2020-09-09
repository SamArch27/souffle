/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Conjunction.h
 *
 * Defines a class for evaluating conditions in the Relational Algebra
 * Machine.
 *
 ***********************************************************************/

#pragma once

#include "ram/Condition.h"
#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/MiscUtil.h"
#include <cassert>
#include <memory>
#include <sstream>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class RamConjunction
 * @brief A conjunction of conditions
 *
 * Condition of the form "LHS and RHS", where LHS
 * and RHS are conditions
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * C1 AND C2 AND C3
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Is a RamConjunction, which may have LHS "C1"
 * and RHS "C2 AND C3"
 */
class RamConjunction : public RamCondition {
public:
    RamConjunction(std::unique_ptr<RamCondition> l, std::unique_ptr<RamCondition> r)
            : lhs(std::move(l)), rhs(std::move(r)) {
        assert(lhs != nullptr && "left-hand side of conjunction is a nullptr");
        assert(rhs != nullptr && "right-hand side of conjunction is a nullptr");
    }

    /** @brief Get left-hand side of conjunction */
    const RamCondition& getLHS() const {
        return *lhs;
    }

    /** @brief Get right-hand side of conjunction */
    const RamCondition& getRHS() const {
        return *rhs;
    }

    std::vector<const RamNode*> getChildNodes() const override {
        return {lhs.get(), rhs.get()};
    }

    RamConjunction* clone() const override {
        return new RamConjunction(souffle::clone(lhs), souffle::clone(rhs));
    }

    void apply(const RamNodeMapper& map) override {
        lhs = map(std::move(lhs));
        rhs = map(std::move(rhs));
    }

protected:
    void print(std::ostream& os) const override {
        os << "(" << *lhs << " AND " << *rhs << ")";
    }

    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamConjunction&>(node);
        return equal_ptr(lhs, other.lhs) && equal_ptr(rhs, other.rhs);
    }

    /** Left-hand side of conjunction */
    std::unique_ptr<RamCondition> lhs;

    /** Right-hand side of conjunction */
    std::unique_ptr<RamCondition> rhs;
};

}  // end of namespace souffle
