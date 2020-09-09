/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file DebugInfo.h
 *
 ***********************************************************************/

#pragma once

#include "ram/AbstractLog.h"
#include "ram/Node.h"
#include "ram/NodeMapper.h"
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
 * @class RamDebugInfo
 * @brief Debug statement
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * BEGIN_DEBUG "gen(1) \nin file /file.dl [7:7-7:10]\;"
 *   ...
 * END_DEBUG
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamDebugInfo : public RamStatement, public RamAbstractLog {
public:
    RamDebugInfo(std::unique_ptr<RamStatement> stmt, std::string msg)
            : RamAbstractLog(std::move(stmt), std::move(msg)) {}

    std::vector<const RamNode*> getChildNodes() const override {
        return RamAbstractLog::getChildNodes();
    }

    RamDebugInfo* clone() const override {
        return new RamDebugInfo(souffle::clone(statement), message);
    }

    void apply(const RamNodeMapper& map) override {
        RamAbstractLog::apply(map);
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos) << "BEGIN_DEBUG \"" << stringify(message) << "\"" << std::endl;
        RamStatement::print(statement.get(), os, tabpos + 1);
        os << times(" ", tabpos) << "END_DEBUG" << std::endl;
    }
};

}  // end of namespace souffle
