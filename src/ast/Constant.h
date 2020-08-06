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

#include "Argument.h"
#include "Node.h"
#include "SrcLocation.h"
#include <ostream>
#include <string>
#include <utility>

namespace souffle {

/**
 * @class AstConstant
 * @brief Abstract constant class
 */
class AstConstant : public AstArgument {
public:
    AstConstant* clone() const override = 0;

    /** Get string representation of Constant */
    const std::string& getConstant() const {
        return constant;
    }

protected:
    void print(std::ostream& os) const override {
        os << getConstant();
    }

    bool equal(const AstNode& node) const override {
        const auto& other = static_cast<const AstConstant&>(node);
        return constant == other.constant;
    }

    AstConstant(std::string value, SrcLocation loc = {})
            : AstArgument(std::move(loc)), constant(std::move(value)){};

private:
    /** String representation of constant */
    const std::string constant;
};

}  // end of namespace souffle
