/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Sequence.h
 *
 ***********************************************************************/

#pragma once

#include "ram/ListStatement.h"
#include "ram/Statement.h"
#include "souffle/utility/MiscUtil.h"
#include <memory>
#include <ostream>
#include <utility>
#include <vector>

namespace souffle::ram {

/**
 * @class Sequence
 * @brief Sequence of RAM statements
 *
 * Execute statement one by one from an ordered list of statements.
 */
class Sequence : public ListStatement {
public:
    Sequence(VecOwn<Statement> statements) : ListStatement(std::move(statements)) {}
    Sequence() : ListStatement() {}
    template <typename... Stmts>
    Sequence(Own<Statement> first, Own<Stmts>... rest)
            : ListStatement(std::move(first), std::move(rest)...) {}

    Sequence* clone() const override {
        auto* res = new Sequence();
        for (auto& cur : statements) {
            res->statements.push_back(souffle::clone(cur));
        }
        return res;
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        for (const auto& stmt : statements) {
            Statement::print(stmt.get(), os, tabpos);
        }
    }
};

}  // namespace souffle::ram
