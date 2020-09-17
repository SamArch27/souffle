/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Constant.h
 *
 * Defines an abstract class for constants
 *
 ***********************************************************************/

#pragma once

#include "ast/Argument.h"
#include "ast/Node.h"
#include "parser/SrcLocation.h"
#include <ostream>
#include <string>
#include <utility>

namespace souffle::ast {

/**
 * @class Constant
 * @brief Abstract constant class
 */
class Constant : public Argument {
public:
    Constant* clone() const override = 0;

    /** Get string representation of Constant */
    const std::string& getConstant() const {
        return constant;
    }

protected:
    void print(std::ostream& os) const override {
        os << getConstant();
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const Constant&>(node);
        return constant == other.constant;
    }

    Constant(std::string value, SrcLocation loc = {})
            : Argument(std::move(loc)), constant(std::move(value)){};

private:
    /** String representation of constant */
    const std::string constant;
};

}  // namespace souffle::ast
