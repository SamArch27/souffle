/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file RecordInit.h
 *
 * Defines the record initialization class
 *
 ***********************************************************************/

#pragma once

#include "ast/Node.h"
#include "ast/Term.h"
#include "parser/SrcLocation.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class AstRecordInit
 * @brief Defines a record initialization class
 */
class AstRecordInit : public AstTerm {
public:
    AstRecordInit(VecOwn<AstArgument> operands = {}, SrcLocation loc = {})
            : AstTerm(std::move(operands), std::move(loc)) {}

    AstRecordInit* clone() const override {
        return new AstRecordInit(souffle::clone(args), getSrcLoc());
    }

protected:
    void print(std::ostream& os) const override {
        os << "[" << join(args) << "]";
    }
};

}  // end of namespace souffle
