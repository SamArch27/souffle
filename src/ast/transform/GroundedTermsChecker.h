/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file GroundedTermsChecker.h
 *
 * Defines the grounded terms checker pass.
 *
 ***********************************************************************/

#pragma once

#include "Transformer.h"
#include <string>

namespace souffle {

class AstTranslationUnit;

class GroundedTermsChecker : public AstTransformer {
public:
    std::string getName() const override {
        return "GroundedTermsChecker";
    }

    // `apply` but doesn't immediately bail if any errors are found.
    void verify(AstTranslationUnit& translationUnit);

    GroundedTermsChecker* clone() const override {
        return new GroundedTermsChecker();
    }

private:
    bool transform(AstTranslationUnit& translationUnit) override {
        verify(translationUnit);
        return false;
    }
};

}  // end of namespace souffle
