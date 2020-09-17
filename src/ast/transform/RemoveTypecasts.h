/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file RemoveTypecasts.h
 *
 * Defines AST transformation passes.
 *
 ***********************************************************************/

#pragma once

#include "ast/TranslationUnit.h"
#include "ast/transform/Transformer.h"
#include <string>

namespace souffle::ast::transform {

/**
 * Transformation to remove typecasts.
 */
class RemoveTypecastsTransformer : public Transformer {
private:
    bool transform(TranslationUnit& translationUnit) override;

public:
    std::string getName() const override {
        return "RemoveTypecastsTransformer";
    }

    RemoveTypecastsTransformer* clone() const override {
        return new RemoveTypecastsTransformer();
    }
};

}  // namespace souffle::ast::transform
