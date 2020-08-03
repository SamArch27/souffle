/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file NilConstant.h
 *
 ***********************************************************************/

#pragma once

#include "SrcLocation.h"
#include "ast/Constant.h"
#include <string>
#include <utility>

namespace souffle {

/**
 * Nil Constant
 */
class AstNilConstant : public AstConstant {
public:
    AstNilConstant(SrcLocation loc = {}) : AstConstant("nil", std::move(loc)) {}

    AstNilConstant* clone() const override {
        return new AstNilConstant(getSrcLoc());
    }
};

}  // end of namespace souffle
