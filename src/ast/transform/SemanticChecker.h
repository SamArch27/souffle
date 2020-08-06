/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file SemanticChecker.h
 *
 * Defines the semantic checker pass.
 *
 ***********************************************************************/

#pragma once

#include "Transformer.h"
#include <string>

namespace souffle {

class AstTranslationUnit;

class AstSemanticChecker : public AstTransformer {
public:
    ~AstSemanticChecker() override = default;

    std::string getName() const override {
        return "AstSemanticChecker";
    }

    AstSemanticChecker* clone() const override {
        return new AstSemanticChecker();
    }

private:
    bool transform(AstTranslationUnit& translationUnit) override;
};

}  // end of namespace souffle
