/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2017, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Provenance.h
 *
 * Transformation pass to add provenance information
 *
 ***********************************************************************/

#pragma once

#include "ast/TranslationUnit.h"
#include "ast/transform/Transformer.h"
#include <string>

namespace souffle::ast::transform {

/**
 * Transformation pass to add provenance information
 */
class ProvenanceTransformer : public Transformer {
public:
    std::string getName() const override {
        return "ProvenanceTransformer";
    }

    ProvenanceTransformer* clone() const override {
        return new ProvenanceTransformer();
    }

private:
    bool transform(TranslationUnit& translationUnit) override;
    bool transformMaxHeight(TranslationUnit& translationUnit);
};

}  // namespace souffle::ast::transform
