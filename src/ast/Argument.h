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
 * Abstract class definitions for AST nodes
 *
 ***********************************************************************/

#pragma once

#include "ast/Node.h"

namespace souffle {

/**
 * Argument
 */
class AstArgument : public AstNode {
public:
    using AstNode::AstNode;

    /** Create clone */
    AstArgument* clone() const override = 0;
};

}  // end of namespace souffle
