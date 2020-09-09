/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file NestedIntrinsicOperator.h
 *
 ***********************************************************************/

#pragma once

#include "ram/Expression.h"
#include "ram/NestedOperation.h"
#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "ram/Operation.h"
#include "ram/TupleOperation.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <iosfwd>
#include <memory>
#include <ostream>
#include <utility>
#include <vector>

namespace souffle {

enum class RamNestedIntrinsicOp {
    RANGE,
    URANGE,
    FRANGE,
};

inline std::ostream& operator<<(std::ostream& os, RamNestedIntrinsicOp e) {
    switch (e) {
        case RamNestedIntrinsicOp::RANGE: return os << "RANGE";
        case RamNestedIntrinsicOp::URANGE: return os << "URANGE";
        case RamNestedIntrinsicOp::FRANGE: return os << "FRANGE";
        default: fatal("invalid Operation");
    }
}

/**
 * @class RamNestedIntrinsicOperator
 * @brief Effectively identical to `RamIntrinsicOperator`, except it can produce multiple results.
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * RANGE(t0.0, t0.1, t0.2) INTO t1
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamNestedIntrinsicOperator : public RamTupleOperation {
public:
    RamNestedIntrinsicOperator(RamNestedIntrinsicOp op, std::vector<std::unique_ptr<RamExpression>> args,
            std::unique_ptr<RamOperation> nested, int ident)
            : RamTupleOperation(ident, std::move(nested)), args(std::move(args)), op(op) {}

    RamNestedIntrinsicOp getFunction() const {
        return op;
    }

    std::vector<RamExpression*> getArguments() const {
        return toPtrVector(args);
    }

    std::vector<const RamNode*> getChildNodes() const override {
        auto res = RamTupleOperation::getChildNodes();
        for (auto&& x : args) {
            res.push_back(x.get());
        }
        return res;
    }

    RamNestedIntrinsicOperator* clone() const override {
        return new RamNestedIntrinsicOperator(
                op, souffle::clone(args), souffle::clone(&getOperation()), getTupleId());
    }

    void apply(const RamNodeMapper& map) override {
        RamTupleOperation::apply(map);
        for (auto&& x : args) {
            x = map(std::move(x));
        }
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos);
        os << op << "(" << join(args, ",", print_deref<std::unique_ptr<RamExpression>>()) << ") INTO t"
           << getTupleId() << "\n";
        RamNestedOperation::print(os, tabpos + 1);
    }

    bool equal(const RamNode& node) const override {
        auto&& other = static_cast<const RamNestedIntrinsicOperator&>(node);
        return RamTupleOperation::equal(node) && op == other.op && equal_targets(args, other.args);
    }

    std::vector<std::unique_ptr<RamExpression>> args;
    RamNestedIntrinsicOp op;
};

}  // namespace souffle
