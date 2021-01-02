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
 * Defines the abstract class for functors
 *
 ***********************************************************************/

#pragma once

#include "ast/Term.h"
#include "souffle/TypeAttribute.h"
#include <cstddef>

namespace souffle::ast {

/**
 * @class Functor
 * @brief Abstract functor class
 */

class Functor : public Term {
public:
    Functor* clone() const override = 0;

protected:
    using Term::Term;
};

}  // namespace souffle::ast
