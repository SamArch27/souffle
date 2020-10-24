/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Transformer.h
 *
 * Defines the interface for AST transformation passes.
 *
 ***********************************************************************/

#pragma once

#include "ast/TranslationUnit.h"
#include <string>

namespace souffle::ast::transform {

class Transformer {
private:
    virtual bool transform(TranslationUnit& translationUnit) = 0;

public:
    virtual ~Transformer() = default;

    bool apply(TranslationUnit& translationUnit);

    virtual std::string getName() const = 0;

    virtual Transformer* clone() const = 0;
};

}  // namespace souffle::ast::transform
