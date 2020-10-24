/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ProvenanceClauseTranslator.cpp
 *
 * Clause translator when provenance is used
 *
 ***********************************************************************/

#include "ast2ram/ProvenanceClauseTranslator.h"
#include "ast/Atom.h"
#include "ast/BinaryConstraint.h"
#include "ast/Clause.h"
#include "ast/ProvenanceNegation.h"
#include "ast2ram/AstToRamTranslator.h"
#include "ast2ram/ValueIndex.h"
#include "ram/Condition.h"
#include "ram/Relation.h"
#include "ram/SignedConstant.h"
#include "ram/SubroutineReturn.h"

namespace souffle::ast2ram {

Own<ram::Condition> ProvenanceClauseTranslator::createCondition(const ast::Clause& /* originalClause */) {
    return nullptr;
}

Own<ram::Operation> ProvenanceClauseTranslator::createOperation(const ast::Clause& clause) {
    VecOwn<ram::Expression> values;

    // get all values in the body
    for (ast::Literal* lit : clause.getBodyLiterals()) {
        if (auto atom = dynamic_cast<ast::Atom*>(lit)) {
            for (ast::Argument* arg : atom->getArguments()) {
                values.push_back(translator.translateValue(arg, *valueIndex));
            }
        } else if (auto neg = dynamic_cast<ast::ProvenanceNegation*>(lit)) {
            size_t auxiliaryArity = translator.getEvaluationArity(neg->getAtom());
            for (size_t i = 0; i < neg->getAtom()->getArguments().size() - auxiliaryArity; ++i) {
                auto arg = neg->getAtom()->getArguments()[i];
                values.push_back(translator.translateValue(arg, *valueIndex));
            }
            for (size_t i = 0; i < auxiliaryArity; ++i) {
                values.push_back(mk<ram::SignedConstant>(-1));
            }
        } else if (auto neg = dynamic_cast<ast::Negation*>(lit)) {
            for (ast::Argument* arg : neg->getAtom()->getArguments()) {
                values.push_back(translator.translateValue(arg, *valueIndex));
            }
        } else if (auto con = dynamic_cast<ast::BinaryConstraint*>(lit)) {
            values.push_back(translator.translateValue(con->getLHS(), *valueIndex));
            values.push_back(translator.translateValue(con->getRHS(), *valueIndex));
        }
    }

    return mk<ram::SubroutineReturn>(std::move(values));
}

}  // namespace souffle::ast2ram
