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

namespace souffle {

/**
 * @class RamSequence
 * @brief Sequence of RAM statements
 *
 * Execute statement one by one from an ordered list of statements.
 */
class RamSequence : public RamListStatement {
public:
    RamSequence(std::vector<std::unique_ptr<RamStatement>> statements)
            : RamListStatement(std::move(statements)) {}
    RamSequence() : RamListStatement() {}
    template <typename... Stmts>
    RamSequence(std::unique_ptr<RamStatement> first, std::unique_ptr<Stmts>... rest)
            : RamListStatement(std::move(first), std::move(rest)...) {}

    RamSequence* clone() const override {
        auto* res = new RamSequence();
        for (auto& cur : statements) {
            res->statements.push_back(souffle::clone(cur));
        }
        return res;
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        for (const auto& stmt : statements) {
            RamStatement::print(stmt.get(), os, tabpos);
        }
    }
};

}  // end of namespace souffle
