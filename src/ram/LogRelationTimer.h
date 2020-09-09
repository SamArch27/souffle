/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2017, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file LogRelationTimer.h
 *
 ***********************************************************************/

#pragma once

#include "ram/AbstractLog.h"
#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "ram/Relation.h"
#include "ram/RelationStatement.h"
#include "ram/Statement.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StreamUtil.h"
#include "souffle/utility/StringUtil.h"
#include <memory>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class RamLogRelationTimer
 * @brief Execution time logger for a statement
 *
 * Logs the execution time of a statement. Before and after
 * the execution of the logging statement the wall-clock time
 * is taken to compute the time duration for the statement.
 * Duration and logging message is printed after the execution
 * of the statement.
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * START_TIMER ON A "file.dl [8:1-8:8]\;"
 *   ...
 * END_TIMER
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamLogRelationTimer : public RamRelationStatement, public RamAbstractLog {
public:
    RamLogRelationTimer(
            std::unique_ptr<RamStatement> stmt, std::string msg, std::unique_ptr<RamRelationReference> relRef)
            : RamRelationStatement(std::move(relRef)), RamAbstractLog(std::move(stmt), std::move(msg)) {}

    std::vector<const RamNode*> getChildNodes() const override {
        std::vector<const RamNode*> res = RamRelationStatement::getChildNodes();
        res.push_back(RamAbstractLog::getChildNodes().at(0));
        return res;
    }

    RamLogRelationTimer* clone() const override {
        return new RamLogRelationTimer(souffle::clone(statement), message, souffle::clone(relationRef));
    }

    void apply(const RamNodeMapper& map) override {
        RamRelationStatement::apply(map);
        RamAbstractLog::apply(map);
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos) << "START_TIMER ON " << getRelation().getName() << " \""
           << stringify(message) << "\"" << std::endl;
        RamStatement::print(statement.get(), os, tabpos + 1);
        os << times(" ", tabpos) << "END_TIMER" << std::endl;
    }
};

}  // end of namespace souffle
