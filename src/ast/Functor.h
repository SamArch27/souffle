/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Functor.h
 *
 ***********************************************************************/

#pragma once

#include "RamTypes.h"
#include "ast/Term.h"
#include <cstddef>

namespace souffle {

/**
 * Functor class
 */

class AstFunctor : public AstTerm {
public:
    virtual TypeAttribute getReturnType() const = 0;
    virtual TypeAttribute getArgType(const size_t arg) const = 0;
    AstFunctor* clone() const override = 0;

protected:
    using AstTerm::AstTerm;
};

}  // end of namespace souffle
