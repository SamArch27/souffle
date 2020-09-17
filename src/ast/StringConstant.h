/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file StringConstant.h
 *
 * Defines the string constant class
 *
 ***********************************************************************/

#pragma once

#include "ast/Constant.h"
#include "parser/SrcLocation.h"
#include <ostream>
#include <string>
#include <utility>

namespace souffle::ast {

/**
 * @class StringConstant
 * @brief String constant class
 */
class StringConstant : public Constant {
public:
    explicit StringConstant(std::string value, SrcLocation loc = {}) : Constant(std::move(value)) {
        setSrcLoc(std::move(loc));
    }

    StringConstant* clone() const override {
        auto* res = new StringConstant(getConstant());
        res->setSrcLoc(getSrcLoc());
        return res;
    }

protected:
    void print(std::ostream& os) const override {
        os << "\"" << getConstant() << "\"";
    }
};

}  // namespace souffle::ast
