/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Meta.cpp
 *
 * Defines the interface for AST meta-transformation passes.
 *
 ***********************************************************************/

#include "ast/transform/Meta.h"
#include <chrono>
#include <iostream>

namespace souffle {

bool MetaTransformer::applySubtransformer(AstTranslationUnit& translationUnit, AstTransformer* transformer) {
    auto start = std::chrono::high_resolution_clock::now();
    bool changed = transformer->apply(translationUnit);
    auto end = std::chrono::high_resolution_clock::now();

    if (verbose && (dynamic_cast<MetaTransformer*>(transformer) == nullptr)) {
        std::string changedString = changed ? "changed" : "unchanged";
        std::cout << transformer->getName() << " time: " << std::chrono::duration<double>(end - start).count()
                  << "sec [" << changedString << "]" << std::endl;
    }

    return changed;
}

}  // end of namespace souffle
