/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Type.h
 *
 * Defines the type class
 *
 ***********************************************************************/

#pragma once

#include "Node.h"
#include "QualifiedName.h"
#include "SrcLocation.h"
#include <string>
#include <utility>

namespace souffle {

/**
 *  @class Type
 *  @brief An abstract base class for types
 */
class AstType : public AstNode {
public:
    AstType(AstQualifiedName name = {}, SrcLocation loc = {})
            : AstNode(std::move(loc)), name(std::move(name)) {}

    /** Return type name */
    const AstQualifiedName& getQualifiedName() const {
        return name;
    }

    /** Set type name */
    void setQualifiedName(AstQualifiedName name) {
        this->name = std::move(name);
    }

    AstType* clone() const override = 0;

private:
    /** type name */
    AstQualifiedName name;
};

}  // end of namespace souffle
