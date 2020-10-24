/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ProvenanceClauseTranslator.h
 *
 * Clause translator when provenance is used
 *
 ***********************************************************************/

#pragma once

#include "ast2ram/ClauseTranslator.h"

namespace souffle::ast {
class Clause;
}

namespace souffle::ram {
class Condition;
class Operation;
}  // namespace souffle::ram

namespace souffle::ast2ram {

class AstToRamTranslator;

class ProvenanceClauseTranslator : public ClauseTranslator {
public:
    ProvenanceClauseTranslator(AstToRamTranslator& translator) : ClauseTranslator(translator) {}

protected:
    Own<ram::Operation> createOperation(const ast::Clause& clause) override;
    Own<ram::Condition> createCondition(const ast::Clause& originalClause) override;
};
}  // namespace souffle::ast2ram
