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
 ***********************************************************************/

#pragma once

#include "SrcLocation.h"
#include "ast/Argument.h"
#include "ast/Node.h"
#include <ostream>
#include <string>
#include <utility>

namespace souffle {

/**
 * Abstract Constant
 */
class AstConstant : public AstArgument {
public:
    AstConstant* clone() const override = 0;

    /** @return String representation of Constant */
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
    const std::string constant;
};

}  // end of namespace souffle
