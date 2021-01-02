/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Functor.cpp
 *
 * Analysis that provides type information for functors
 *
 ***********************************************************************/

#include "ast/analysis/Functor.h"
#include "FunctorOps.h"
#include "ast/FunctorDeclaration.h"
#include "ast/IntrinsicFunctor.h"
#include "ast/TranslationUnit.h"
#include "ast/utility/Utils.h"

namespace souffle::ast::analysis {

void FunctorAnalysis::run(const TranslationUnit& translationUnit) {
    typeAnalysis = translationUnit.getAnalysis<TypeAnalysis>();
}

bool FunctorAnalysis::isStateful(const UserDefinedFunctor* udf) const {
    return typeAnalysis->isStatefulFunctor(udf);
}

TypeAttribute FunctorAnalysis::getReturnType(const Functor* functor) const {
    return typeAnalysis->getFunctorReturnType(functor);
}

const std::vector<TypeAttribute>& FunctorAnalysis::getArgTypes(const UserDefinedFunctor& udf) const {
    return typeAnalysis->getFunctorArgTypes(udf);
}

/** Return argument type of functor */
TypeAttribute FunctorAnalysis::getArgType(const Functor* functor, const size_t idx) const {
    return typeAnalysis->getFunctorArgType(functor, idx);
}

bool FunctorAnalysis::isMultiResult(const Functor& functor) {
    return TypeAnalysis::isMultiResultFunctor(functor);
}

}  // namespace souffle::ast::analysis
