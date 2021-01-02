/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ConstraintTranslator.cpp
 *
 ***********************************************************************/

#include "ast2ram/seminaive/ConstraintTranslator.h"
#include "ast/Atom.h"
#include "ast/BinaryConstraint.h"
#include "ast/TranslationUnit.h"
#include "ast/analysis/AuxArity.h"
#include "ast2ram/ValueTranslator.h"
#include "ast2ram/utility/TranslatorContext.h"
#include "ast2ram/utility/Utils.h"
#include "ast2ram/utility/ValueIndex.h"
#include "ram/Constraint.h"
#include "ram/EmptinessCheck.h"
#include "ram/ExistenceCheck.h"
#include "ram/Negation.h"
#include "ram/ProvenanceExistenceCheck.h"
#include "ram/UndefValue.h"

namespace souffle::ast2ram::seminaive {

Own<ram::Condition> ConstraintTranslator::translateConstraint(const ast::Literal* lit) {
    assert(lit != nullptr && "literal should be defined");
    return ConstraintTranslator(context, symbolTable, index)(*lit);
}

Own<ram::Condition> ConstraintTranslator::visitAtom(const ast::Atom&) {
    return nullptr;  // covered already within the scan/lookup generation step
}

Own<ram::Condition> ConstraintTranslator::visitBinaryConstraint(const ast::BinaryConstraint& binRel) {
    auto valLHS = context.translateValue(symbolTable, index, binRel.getLHS());
    auto valRHS = context.translateValue(symbolTable, index, binRel.getRHS());
    return mk<ram::Constraint>(
            context.getOverloadedBinaryConstraintOperator(&binRel), std::move(valLHS), std::move(valRHS));
}

Own<ram::Condition> ConstraintTranslator::visitNegation(const ast::Negation& neg) {
    const auto* atom = neg.getAtom();
    size_t auxiliaryArity = context.getEvaluationArity(atom);
    assert(auxiliaryArity <= atom->getArity() && "auxiliary arity out of bounds");
    size_t arity = atom->getArity() - auxiliaryArity;

    if (arity == 0) {
        // for a nullary, negation is a simple emptiness check
        return mk<ram::EmptinessCheck>(getConcreteRelationName(atom->getQualifiedName()));
    }

    // else, we construct the atom and create a negation
    VecOwn<ram::Expression> values;
    auto args = atom->getArguments();
    for (size_t i = 0; i < arity; i++) {
        values.push_back(context.translateValue(symbolTable, index, args[i]));
    }
    for (size_t i = 0; i < auxiliaryArity; i++) {
        values.push_back(mk<ram::UndefValue>());
    }
    return mk<ram::Negation>(
            mk<ram::ExistenceCheck>(getConcreteRelationName(atom->getQualifiedName()), std::move(values)));
}
}  // namespace souffle::ast2ram::seminaive
