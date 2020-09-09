/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2019, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file SubroutineReturn.h
 *
 ***********************************************************************/

#pragma once

#include "ram/Expression.h"
#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "ram/Operation.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <cassert>
#include <iosfwd>
#include <memory>
#include <ostream>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class RamSubroutineReturn
 * @brief A statement for returning from a ram subroutine
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *   ...
 *     RETURN (t0.0, t0.1)
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamSubroutineReturn : public RamOperation {
public:
    RamSubroutineReturn(std::vector<std::unique_ptr<RamExpression>> vals) : expressions(std::move(vals)) {
        for (const auto& expr : expressions) {
            assert(expr != nullptr && "Expression is a null-pointer");
        }
    }

    /** @brief Getter for expressions */
    std::vector<RamExpression*> getValues() const {
        return toPtrVector(expressions);
    }

    std::vector<const RamNode*> getChildNodes() const override {
        std::vector<const RamNode*> res;
        for (const auto& expr : expressions) {
            res.push_back(expr.get());
        }
        return res;
    }

    RamSubroutineReturn* clone() const override {
        std::vector<std::unique_ptr<RamExpression>> newValues;
        for (auto& expr : expressions) {
            newValues.emplace_back(expr->clone());
        }
        return new RamSubroutineReturn(std::move(newValues));
    }

    void apply(const RamNodeMapper& map) override {
        for (auto& expr : expressions) {
            expr = map(std::move(expr));
        }
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos);
        os << "RETURN (";
        for (auto val : getValues()) {
            os << *val;
            if (val != *(getValues().end() - 1)) {
                os << ", ";
            }
        }
        os << ")" << std::endl;
    }

    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamSubroutineReturn&>(node);
        return equal_targets(expressions, other.expressions);
    }

    /** Return expressions */
    std::vector<std::unique_ptr<RamExpression>> expressions;
};

}  // namespace souffle
