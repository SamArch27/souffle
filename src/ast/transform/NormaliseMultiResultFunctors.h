/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file NormaliseMultiResultFunctors.h
 *
 * Transform pass to normalise all appearances of multi-result functors.
 *
 ***********************************************************************/

#pragma once

#include "ast/transform/Transformer.h"

namespace souffle::ast::transform {

/** Uniquely names all appearances of ranges */
class NormaliseMultiResultFunctorsTransformer : public Transformer {
public:
    std::string getName() const override {
        return "NormaliseMultiResultFunctorsTransformer";
    }

private:
    bool transform(TranslationUnit& translationUnit) override;

    NormaliseMultiResultFunctorsTransformer* clone() const override {
        return new NormaliseMultiResultFunctorsTransformer();
    }
};

}  // namespace souffle::ast::transform
