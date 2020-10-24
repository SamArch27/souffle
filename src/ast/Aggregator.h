/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Aggregator.h
 *
 * Defines the aggregator class
 *
 ***********************************************************************/

#pragma once

#include "AggregateOp.h"
#include "ast/Argument.h"
#include "ast/Literal.h"
#include "ast/Node.h"
#include "ast/utility/NodeMapper.h"
#include "parser/SrcLocation.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <memory>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle::ast {

/**
 * @class Aggregator
 * @brief Defines the aggregator class
 *
 * Example:
 *   sum y+x: {A(y),B(x)}
 *
 * Aggregates over a sub-query using an aggregate operator
 * and an expression.
 */
class Aggregator : public Argument {
public:
    Aggregator(AggregateOp fun, Own<Argument> expr = nullptr, VecOwn<Literal> body = {}, SrcLocation loc = {})
            : Argument(std::move(loc)), fun(fun), targetExpression(std::move(expr)), body(std::move(body)) {}

    /** Return aggregate operator */
    AggregateOp getOperator() const {
        return fun;
    }

    /** Set aggregate operator */
    void setOperator(AggregateOp op) {
        fun = op;
    }

    /** Return target expression */
    const Argument* getTargetExpression() const {
        return targetExpression.get();
    }

    /** Return body literals */
    std::vector<Literal*> getBodyLiterals() const {
        return toPtrVector(body);
    }

    /** Set body */
    void setBody(VecOwn<Literal> bodyLiterals) {
        body = std::move(bodyLiterals);
    }

    std::vector<const Node*> getChildNodes() const override {
        auto res = Argument::getChildNodes();
        if (targetExpression) {
            res.push_back(targetExpression.get());
        }
        for (auto& cur : body) {
            res.push_back(cur.get());
        }
        return res;
    }

    Aggregator* clone() const override {
        return new Aggregator(fun, souffle::clone(targetExpression), souffle::clone(body), getSrcLoc());
    }

    void apply(const NodeMapper& map) override {
        if (targetExpression) {
            targetExpression = map(std::move(targetExpression));
        }
        for (auto& cur : body) {
            cur = map(std::move(cur));
        }
    }

protected:
    void print(std::ostream& os) const override {
        os << fun;
        if (targetExpression) {
            os << " " << *targetExpression;
        }
        os << " : { " << join(body) << " }";
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const Aggregator&>(node);
        return fun == other.fun && equal_ptr(targetExpression, other.targetExpression) &&
               equal_targets(body, other.body);
    }

private:
    /** Aggregate operator */
    AggregateOp fun;

    /** Aggregate expression */
    Own<Argument> targetExpression;

    /** Body literal of sub-query */
    VecOwn<Literal> body;
};

}  // namespace souffle::ast
