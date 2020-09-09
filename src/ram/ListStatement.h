/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ListStatement.h
 *
 ***********************************************************************/

#pragma once

#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "ram/Statement.h"
#include "souffle/utility/ContainerUtil.h"
#include <cassert>
#include <memory>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class RamListStatement
 * @brief Abstract class for a list of RAM statements
 */
class RamListStatement : public RamStatement {
public:
    RamListStatement() = default;
    RamListStatement(std::vector<std::unique_ptr<RamStatement>> statements)
            : statements(std::move(statements)) {}

    template <typename... Stmts>
    RamListStatement(std::unique_ptr<Stmts>&&... stmts) {
        std::unique_ptr<RamStatement> tmp[] = {std::move(stmts)...};
        for (auto& cur : tmp) {
            assert(cur.get() != nullptr && "statement is a null-pointer");
            statements.emplace_back(std::move(cur));
        }
    }

    /** @brief Get statements */
    std::vector<RamStatement*> getStatements() const {
        return toPtrVector(statements);
    }

    std::vector<const RamNode*> getChildNodes() const override {
        std::vector<const RamNode*> res;
        for (const auto& cur : statements) {
            res.push_back(cur.get());
        }
        return res;
    }

    void apply(const RamNodeMapper& map) override {
        for (auto& stmt : statements) {
            stmt = map(std::move(stmt));
        }
    }

protected:
    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamListStatement&>(node);
        return equal_targets(statements, other.statements);
    }

protected:
    /** ordered list of RAM statements */
    std::vector<std::unique_ptr<RamStatement>> statements;
};

}  // end of namespace souffle
