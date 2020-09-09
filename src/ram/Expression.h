/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Expression.h
 *
 * Defines a class for evaluating values in the Relational Algebra Machine
 *
 ************************************************************************/

#pragma once

#include "ram/Node.h"

namespace souffle {

/**
 * @class RamExpression
 * @brief Abstract class for describing scalar values in RAM
 */
class RamExpression : public RamNode {
public:
    RamExpression* clone() const override = 0;
};

}  // end of namespace souffle
