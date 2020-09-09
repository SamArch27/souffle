/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Constant.h
 *
 * Defines a class for evaluating values in the Relational Algebra Machine
 *
 ************************************************************************/

#pragma once

#include "ram/Expression.h"
#include "ram/Node.h"
#include "souffle/RamTypes.h"

namespace souffle {

/**
 * @class RamConstant
 * @brief Represents a Ram Constant
 *
 */
class RamConstant : public RamExpression {
public:
    /** @brief Get constant */
    RamDomain getConstant() const {
        return constant;
    }

protected:
    explicit RamConstant(RamDomain constant) : constant(constant) {}

    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamConstant&>(node);
        return constant == other.constant;
    }

    /** Constant value */
    const RamDomain constant;
};

}  // end of namespace souffle
