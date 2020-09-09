/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file PackRecord.h
 *
 * Defines a class for evaluating values in the Relational Algebra Machine
 *
 ************************************************************************/

#pragma once

#include "ram/Expression.h"
#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <cassert>
#include <memory>
#include <sstream>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class RamPackRecord
 * @brief Packs a record's arguments into a reference
 */
class RamPackRecord : public RamExpression {
public:
    RamPackRecord(std::vector<std::unique_ptr<RamExpression>> args) : arguments(std::move(args)) {
        for (const auto& arg : arguments) {
            assert(arg != nullptr && "argument is a null-pointer");
        }
    }

    /** @brief Get record arguments */
    std::vector<RamExpression*> getArguments() const {
        return toPtrVector(arguments);
    }

    std::vector<const RamNode*> getChildNodes() const override {
        std::vector<const RamNode*> res;
        for (const auto& cur : arguments) {
            res.push_back(cur.get());
        }
        return res;
    }

    RamPackRecord* clone() const override {
        auto* res = new RamPackRecord({});
        for (auto& cur : arguments) {
            res->arguments.emplace_back(cur->clone());
        }
        return res;
    }

    void apply(const RamNodeMapper& map) override {
        for (auto& arg : arguments) {
            arg = map(std::move(arg));
        }
    }

protected:
    void print(std::ostream& os) const override {
        os << "[" << join(arguments, ",", [](std::ostream& out, const std::unique_ptr<RamExpression>& arg) {
            out << *arg;
        }) << "]";
    }

    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamPackRecord&>(node);
        return equal_targets(arguments, other.arguments);
    }

    /** Arguments */
    std::vector<std::unique_ptr<RamExpression>> arguments;
};

}  // end of namespace souffle
