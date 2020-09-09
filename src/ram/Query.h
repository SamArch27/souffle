/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Query.h
 *
 ***********************************************************************/

#pragma once

#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "ram/Operation.h"
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
 * @class RamQuery
 * @brief A relational algebra query
 *
 * Corresponds to the core machinery of semi-naive evaluation
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * QUERY
 *   FOR t0 in A
 *     FOR t1 in B
 *       ...
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamQuery : public RamStatement {
public:
    RamQuery(std::unique_ptr<RamOperation> o) : operation(std::move(o)) {
        assert(operation && "operation is a nullptr");
    }

    /** @brief Get RAM operation */
    const RamOperation& getOperation() const {
        return *operation;
    }

    std::vector<const RamNode*> getChildNodes() const override {
        return {operation.get()};
    }

    RamQuery* clone() const override {
        return new RamQuery(souffle::clone(operation));
    }

    void apply(const RamNodeMapper& map) override {
        operation = map(std::move(operation));
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos) << "QUERY" << std::endl;
        operation->print(os, tabpos + 1);
    }

    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamQuery&>(node);
        return equal_ptr(operation, other.operation);
    }

    /** RAM operation */
    std::unique_ptr<RamOperation> operation;
};

}  // end of namespace souffle
