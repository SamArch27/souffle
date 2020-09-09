/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Negation.h
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
 * @class RamNegation
 * @brief Negates a given condition
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * (NOT t0 IN A)
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamNegation : public RamCondition {
public:
    RamNegation(std::unique_ptr<RamCondition> op) : operand(std::move(op)) {
        assert(operand != nullptr && "operand of negation is a null-pointer");
    }

    /** @brief Get operand of negation */
    const RamCondition& getOperand() const {
        return *operand;
    }

    std::vector<const RamNode*> getChildNodes() const override {
        return {operand.get()};
    }

    RamNegation* clone() const override {
        return new RamNegation(souffle::clone(operand));
    }

    void apply(const RamNodeMapper& map) override {
        operand = map(std::move(operand));
    }

protected:
    void print(std::ostream& os) const override {
        os << "(NOT " << *operand << ")";
    }

    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamNegation&>(node);
        return equal_ptr(operand, other.operand);
    }

    /** Operand */
    std::unique_ptr<RamCondition> operand;
};

}  // end of namespace souffle
