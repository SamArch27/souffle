/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Condition.h
 *
 * Defines a class for evaluating conditions in the Relational Algebra
 * Machine.
 *
 ***********************************************************************/

#pragma once

#include "ram/Node.h"

namespace souffle {

/**
 * @class RamCondition
 * @brief Abstract class for conditions and boolean values in RAM
 */
class RamCondition : public RamNode {
public:
    RamCondition* clone() const override = 0;
};

}  // end of namespace souffle
