/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Filter.h
 *
 ***********************************************************************/

#pragma once

#include "ram/AbstractConditional.h"
#include "ram/Condition.h"
#include "ram/NestedOperation.h"
#include "ram/Node.h"
#include "ram/Operation.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <iosfwd>
#include <memory>
#include <ostream>
#include <string>
#include <utility>

namespace souffle {

/**
 * @class RamFilter
 * @brief Checks whether a given condition holds
 *
 * The RamFilter is essentially an "if" statement.
 *
 * The following example checks that both C1 and C2 hold
 * before proceeding deeper in the loop nest:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * IF C1 AND C2
 *  ...
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamFilter : public RamAbstractConditional {
public:
    RamFilter(std::unique_ptr<RamCondition> cond, std::unique_ptr<RamOperation> nested,
            std::string profileText = "")
            : RamAbstractConditional(std::move(cond), std::move(nested), std::move(profileText)) {}

    RamFilter* clone() const override {
        return new RamFilter(souffle::clone(condition), souffle::clone(&getOperation()), getProfileText());
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos);
        os << "IF " << getCondition() << std::endl;
        RamNestedOperation::print(os, tabpos + 1);
    }
};

}  // namespace souffle
