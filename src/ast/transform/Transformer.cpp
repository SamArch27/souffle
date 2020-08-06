/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Transformer.cpp
 *
 * Defines the interface for AST transformation passes.
 *
 ***********************************************************************/

#include "Transformer.h"
#include "../TranslationUnit.h"
#include "ErrorReport.h"

namespace souffle {

bool AstTransformer::apply(AstTranslationUnit& translationUnit) {
    // invoke the transformation
    bool changed = transform(translationUnit);

    if (changed) {
        translationUnit.invalidateAnalyses();
    }

    /* Abort evaluation of the program if errors were encountered */
    translationUnit.getErrorReport().exitIfErrors();

    return changed;
}

}  // end of namespace souffle
