/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file SubproofGenerator.h
 *
 ***********************************************************************/

#pragma once

#include "ast2ram/seminaive/ClauseTranslator.h"

namespace souffle::ast {
class Clause;
}

namespace souffle::ram {
class Condition;
class Operation;
class Statement;
}  // namespace souffle::ram

namespace souffle::ast2ram {
class TranslatorContext;
}

namespace souffle::ast2ram::provenance {

class SubproofGenerator : public ast2ram::seminaive::ClauseTranslator {
public:
    SubproofGenerator(const TranslatorContext& context, SymbolTable& symbolTable);
    ~SubproofGenerator();

protected:
    Own<ram::Statement> createRamFactQuery(const ast::Clause& clause) const override;
    Own<ram::Statement> createRamRuleQuery(const ast::Clause& clause) override;
    Own<ram::Operation> addNegatedAtom(Own<ram::Operation> op, const ast::Atom* atom) const override;
    Own<ram::Operation> generateReturnInstantiatedValues(const ast::Clause& clause) const;
    Own<ram::Operation> addBodyLiteralConstraints(
            const ast::Clause& clause, Own<ram::Operation> op) const override;
};
}  // namespace souffle::ast2ram::provenance
