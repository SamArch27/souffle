/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Break.h
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
 * @class RamBreak
 * @brief Breaks out of the loop if a condition holds
 *
 * The following example will break out of the inner-most
 * loop if the condition (t1.1 = 4) holds:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * FOR t0 in A
 *   FOR t1 in B
 *     IF t0.1 = 4 BREAK
 *     ...
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamBreak : public RamAbstractConditional {
public:
    RamBreak(std::unique_ptr<RamCondition> cond, std::unique_ptr<RamOperation> nested,
            std::string profileText = "")
            : RamAbstractConditional(std::move(cond), std::move(nested), std::move(profileText)) {}

    RamBreak* clone() const override {
        return new RamBreak(souffle::clone(condition), souffle::clone(&getOperation()), getProfileText());
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos);
        os << "IF " << getCondition() << " BREAK" << std::endl;
        RamNestedOperation::print(os, tabpos + 1);
    }
};

}  // namespace souffle
