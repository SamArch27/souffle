/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Counter.h
 *
 ***********************************************************************/

#pragma once

#include "ast/Argument.h"
#include <ostream>

namespace souffle {

/**
 * Counter
 */
class AstCounter : public AstArgument {
public:
    using AstArgument::AstArgument;

    AstCounter* clone() const override {
        return new AstCounter(getSrcLoc());
    }

protected:
    void print(std::ostream& os) const override {
        os << "$";
    }
};

}  // end of namespace souffle
