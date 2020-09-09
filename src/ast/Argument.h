/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Argument.h
 *
 * Defines the abstract class for arguments
 *
 ***********************************************************************/

#pragma once

#include "ast/Node.h"

namespace souffle {

/**
 * @class AstArgument
 * @brief An abstract class for arguments
 */
class AstArgument : public AstNode {
public:
    using AstNode::AstNode;

    /** Create clone */
    AstArgument* clone() const override = 0;
};

}  // end of namespace souffle
