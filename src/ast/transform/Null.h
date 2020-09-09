/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Null.h
 *
 * Defines the interface for Null transformation passes.
 *
 ***********************************************************************/

#pragma once

#include "ast/transform/Meta.h"
#include <set>
#include <string>
#include <vector>

namespace souffle {

class AstTranslationUnit;
class AstTransformer;

/**
 * Transformer that does absolutely nothing
 */
class NullTransformer : public MetaTransformer {
private:
    bool transform(AstTranslationUnit& /* translationUnit */) override {
        return false;
    }

public:
    std::vector<AstTransformer*> getSubtransformers() const override {
        return {};
    }

    void setDebugReport() override {}

    void setVerbosity(bool /* verbose */) override {}

    void disableTransformers(const std::set<std::string>& /* transforms */) override {}

    std::string getName() const override {
        return "NullTransformer";
    }

    NullTransformer* clone() const override {
        return new NullTransformer();
    }
};

}  // end of namespace souffle
