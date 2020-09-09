/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file True.h
 *
 * Defines a class for evaluating conditions in the Relational Algebra
 * Machine.
 *
 ***********************************************************************/

#pragma once

#include "ram/Condition.h"
#include <ostream>

namespace souffle {

/**
 * @class RamTrue
 * @brief True value condition
 *
 * Output is "true"
 */
class RamTrue : public RamCondition {
public:
    RamTrue* clone() const override {
        return new RamTrue();
    }

protected:
    void print(std::ostream& os) const override {
        os << "true";
    }
};

}  // end of namespace souffle
