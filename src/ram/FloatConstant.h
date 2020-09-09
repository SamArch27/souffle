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

namespace souffle {

/**
 * @class RamFloatConstant
 * @brief Represents a float constant
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * float(3.3)
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamFloatConstant : public RamConstant {
public:
    explicit RamFloatConstant(RamFloat val) : RamConstant(ramBitCast(val)) {}

    /** @brief Get value of the constant. */
    RamFloat getValue() const {
        return ramBitCast<RamFloat>(constant);
    }

    /** Create clone */
    RamFloatConstant* clone() const override {
        return new RamFloatConstant(getValue());
    }

protected:
    void print(std::ostream& os) const override {
        os << "float(" << getValue() << ")";
    }
};

}  // end of namespace souffle
