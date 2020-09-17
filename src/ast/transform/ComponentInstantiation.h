/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ComponentInstantiation.h
 *
 ***********************************************************************/

#pragma once

#include "ast/TranslationUnit.h"
#include "ast/transform/Transformer.h"
#include <string>

namespace souffle::ast::transform {

class ComponentInstantiationTransformer : public Transformer {
public:
    std::string getName() const override {
        return "ComponentInstantiationTransformer";
    }

    ComponentInstantiationTransformer* clone() const override {
        return new ComponentInstantiationTransformer();
    }

private:
    bool transform(TranslationUnit& translationUnit) override;
};

}  // namespace souffle::ast::transform
