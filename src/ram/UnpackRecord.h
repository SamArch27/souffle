/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file UnpackRecord.h
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
#include <cassert>
#include <cstddef>
#include <iosfwd>
#include <memory>
#include <ostream>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class RamUnpackRecord
 * @brief Record lookup
 *
 * Looks up a record with respect to an expression
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * UNPACK t0.0 INTO t1
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamUnpackRecord : public RamTupleOperation {
public:
    RamUnpackRecord(std::unique_ptr<RamOperation> nested, int ident, std::unique_ptr<RamExpression> expr,
            size_t arity)
            : RamTupleOperation(ident, std::move(nested)), expression(std::move(expr)), arity(arity) {
        assert(expression != nullptr && "Expression is a null-pointer");
    }

    /** @brief Get record expression */
    const RamExpression& getExpression() const {
        assert(expression != nullptr && "Expression of unpack-record is a null-pointer");
        return *expression;
    }

    /** @brief Get arity of record */
    std::size_t getArity() const {
        return arity;
    }

    std::vector<const RamNode*> getChildNodes() const override {
        auto res = RamTupleOperation::getChildNodes();
        res.push_back(expression.get());
        return res;
    }

    RamUnpackRecord* clone() const override {
        return new RamUnpackRecord(
                souffle::clone(&getOperation()), getTupleId(), souffle::clone(&getExpression()), arity);
    }

    void apply(const RamNodeMapper& map) override {
        RamTupleOperation::apply(map);
        expression = map(std::move(expression));
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos);
        os << "UNPACK t" << getTupleId() << " FROM " << *expression << "\n";
        RamNestedOperation::print(os, tabpos + 1);
    }

    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamUnpackRecord&>(node);
        return RamTupleOperation::equal(other) && equal_ptr(expression, other.expression) &&
               arity == other.arity;
    }

    /** Expression for record reference */
    std::unique_ptr<RamExpression> expression;

    /** Arity of the unpacked tuple */
    const size_t arity;
};

}  // namespace souffle
