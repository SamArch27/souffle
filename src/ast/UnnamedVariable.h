/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file UnnamedVariable.h
 *
 * Defines the unnamed variable class
 *
 ***********************************************************************/

#pragma once

#include "Argument.h"
#include <ostream>

namespace souffle {

/**
 * @class AstUnnamedVariable
 * @brief Unnamed variable class
 */
class AstUnnamedVariable : public AstArgument {
public:
    using AstArgument::AstArgument;

    AstUnnamedVariable* clone() const override {
        return new AstUnnamedVariable(getSrcLoc());
    }

protected:
    void print(std::ostream& os) const override {
        os << "_";
    }
};

}  // end of namespace souffle
