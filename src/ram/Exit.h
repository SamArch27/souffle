/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Exit.h
 *
 ***********************************************************************/

#pragma once

#include "ram/Condition.h"
#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "ram/Statement.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <cassert>
#include <memory>
#include <ostream>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class RamExit
 * @brief Exit statement for a loop
 *
 * Exits a loop if exit condition holds.
 *
 * The following example will exit the loop given
 * that A is the empty set:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * EXIT (A = ∅)
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamExit : public RamStatement {
public:
    RamExit(std::unique_ptr<RamCondition> c) : condition(std::move(c)) {
        assert(condition && "condition is a nullptr");
    }

    /** @brief Get exit condition */
    const RamCondition& getCondition() const {
        return *condition;
    }

    std::vector<const RamNode*> getChildNodes() const override {
        return {condition.get()};
    }

    RamExit* clone() const override {
        return new RamExit(souffle::clone(condition));
    }

    void apply(const RamNodeMapper& map) override {
        condition = map(std::move(condition));
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos) << "EXIT " << getCondition() << std::endl;
    }

    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamExit&>(node);
        return equal_ptr(condition, other.condition);
    }

    /** exit condition */
    std::unique_ptr<RamCondition> condition;
};

}  // end of namespace souffle
