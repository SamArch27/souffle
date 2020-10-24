/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file UnsignedConstant.h
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
 * @class UnsignedConstant
 * @brief Represents a unsigned constant
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * unsigned(5)
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class UnsignedConstant : public Constant {
public:
    explicit UnsignedConstant(RamUnsigned val) : Constant(ramBitCast(val)) {}

    /** @brief Get value of the constant. */
    RamUnsigned getValue() const {
        return ramBitCast<RamUnsigned>(constant);
    }

    /** Create clone */
    UnsignedConstant* clone() const override {
        return new UnsignedConstant(getValue());
    }

protected:
    void print(std::ostream& os) const override {
        os << "unsigned(" << getValue() << ")";
    }
};

}  // namespace souffle::ram
