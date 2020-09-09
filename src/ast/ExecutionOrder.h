/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ExecutionOrder.h
 *
 * Defines the execution order class
 *
 ***********************************************************************/

#pragma once

#include "ast/Node.h"
#include "parser/SrcLocation.h"
#include "souffle/utility/StreamUtil.h"
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class AstExecutionOrder
 * @brief An execution order for atoms within a clause;
 *        one or more execution orders form a plan.
 */
class AstExecutionOrder : public AstNode {
public:
    using ExecOrder = std::vector<unsigned int>;

    AstExecutionOrder(ExecOrder order = {}, SrcLocation loc = {}) : order(std::move(order)) {
        setSrcLoc(std::move(loc));
    }

    /** Get order */
    const ExecOrder& getOrder() const {
        return order;
    }

    AstExecutionOrder* clone() const override {
        return new AstExecutionOrder(order, getSrcLoc());
    }

protected:
    void print(std::ostream& out) const override {
        out << "(" << join(order) << ")";
    }

    bool equal(const AstNode& node) const override {
        const auto& other = static_cast<const AstExecutionOrder&>(node);
        return order == other.order;
    }

private:
    /** Literal order of body (starting from 1) */
    ExecOrder order;
};

}  // end of namespace souffle
