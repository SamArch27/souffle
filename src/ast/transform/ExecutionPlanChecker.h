/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ExecutionPlanChecker.h
 *
 * Defines the execution plan checker pass.
 *
 ***********************************************************************/

#pragma once

#include "Transformer.h"
#include <string>

namespace souffle {

class AstTranslationUnit;

class AstExecutionPlanChecker : public AstTransformer {
public:
    std::string getName() const override {
        return "AstExecutionPlanChecker";
    }

    AstExecutionPlanChecker* clone() const override {
        return new AstExecutionPlanChecker();
    }

private:
    bool transform(AstTranslationUnit& translationUnit) override;
};

}  // end of namespace souffle
