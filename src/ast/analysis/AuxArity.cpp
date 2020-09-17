/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020, The Souffle Developers. All rights reserved.
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file AuxArity.cpp
 *
 * Implementation of AST analyses classes
 *
 ***********************************************************************/

#include "ast/analysis/AuxArity.h"
#include "Global.h"

namespace souffle::ast::analysis {

size_t AuxiliaryArityAnalysis::computeArity(const Relation* /* relation */) const {
    if (Global::config().has("provenance")) {
        return 2;
    } else {
        return 0;
    }
}

}  // namespace souffle::ast::analysis
