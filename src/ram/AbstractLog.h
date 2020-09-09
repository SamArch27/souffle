/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2017, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file AbstractLog.h
 *
 ***********************************************************************/

#pragma once

#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "ram/Statement.h"
#include "souffle/utility/ContainerUtil.h"
#include <cassert>
#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class RamAbstractLog
 * @brief Abstract class for logging
 *
 * Comprises a RamStatement and the message (string) to be logged
 */
class RamAbstractLog {
public:
    RamAbstractLog(std::unique_ptr<RamStatement> stmt, std::string msg)
            : statement(std::move(stmt)), message(std::move(msg)) {
        assert(statement && "log statement is a nullptr");
    }

    std::vector<const RamNode*> getChildNodes() const {
        return {statement.get()};
    }

    /** @brief Get logging message */
    const std::string& getMessage() const {
        return message;
    }

    /** @brief Get logging statement */
    const RamStatement& getStatement() const {
        return *statement;
    }

    void apply(const RamNodeMapper& map) {
        statement = map(std::move(statement));
    }

protected:
    bool equal(const RamNode& node) const {
        const auto& other = dynamic_cast<const RamAbstractLog&>(node);
        return equal_ptr(statement, other.statement) && message == other.message;
    }

protected:
    /** logging statement */
    std::unique_ptr<RamStatement> statement;

    /** logging message */
    std::string message;
};

}  // end of namespace souffle
