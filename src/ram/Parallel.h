/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Parallel.h
 *
 ***********************************************************************/

#pragma once

#include "ram/ListStatement.h"
#include "ram/Statement.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <memory>
#include <ostream>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class RamParallel
 * @brief Parallel block of statements
 *
 * Execute statements in parallel and wait until all statements have
 * completed their execution before completing the execution of the
 * parallel block.
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * PARALLEL
 *   BEGIN DEBUG...
 *     QUERY
 *       ...
 * END PARALLEL
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamParallel : public RamListStatement {
public:
    RamParallel(std::vector<std::unique_ptr<RamStatement>> statements)
            : RamListStatement(std::move(statements)) {}
    RamParallel() : RamListStatement() {}
    template <typename... Stmts>
    RamParallel(std::unique_ptr<RamStatement> first, std::unique_ptr<Stmts>... rest)
            : RamListStatement(std::move(first), std::move(rest)...) {}

    RamParallel* clone() const override {
        auto* res = new RamParallel();
        for (auto& cur : statements) {
            res->statements.push_back(souffle::clone(cur));
        }
        return res;
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos) << "PARALLEL" << std::endl;
        for (auto const& stmt : statements) {
            RamStatement::print(stmt.get(), os, tabpos + 1);
        }
        os << times(" ", tabpos) << "END PARALLEL" << std::endl;
    }
};

}  // end of namespace souffle
