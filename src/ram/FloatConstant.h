/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file FloatConstant.h
 *
 * Defines a class for evaluating values in the Relational Algebra Machine
 *
 ************************************************************************/

#pragma once

#include "ram/Constant.h"
#include "souffle/RamTypes.h"
#include <ostream>

namespace souffle::ram {

/**
 * @class FloatConstant
 * @brief Represents a float constant
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * float(3.3)
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class FloatConstant : public Constant {
public:
    explicit FloatConstant(RamFloat val) : Constant(ramBitCast(val)) {}

    /** @brief Get value of the constant. */
    RamFloat getValue() const {
        return ramBitCast<RamFloat>(constant);
    }

    /** Create clone */
    FloatConstant* clone() const override {
        return new FloatConstant(getValue());
    }

protected:
    void print(std::ostream& os) const override {
        os << "float(" << getValue() << ")";
    }
};

}  // namespace souffle::ram
