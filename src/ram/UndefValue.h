/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file UndefValue.h
 *
 * Defines a class for evaluating values in the Relational Algebra Machine
 *
 ************************************************************************/

#pragma once

#include "ram/Expression.h"
#include <ostream>

namespace souffle {

/**
 * @class RamUndefValue
 * @brief An undefined expression
 *
 * Output is ⊥
 */
class RamUndefValue : public RamExpression {
public:
    RamUndefValue* clone() const override {
        return new RamUndefValue();
    }

protected:
    void print(std::ostream& os) const override {
        os << "⊥";
    }
};

}  // end of namespace souffle
