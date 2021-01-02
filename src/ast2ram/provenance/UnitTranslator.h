/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ProvenanceTranslator.h
 *
 ***********************************************************************/

#pragma once

#include "ast2ram/seminaive/UnitTranslator.h"

namespace souffle::ast {
class Atom;
class Node;
class Program;
class Variable;
}  // namespace souffle::ast

namespace souffle::ram {
class Condition;
class ExistenceCheck;
class Expression;
class Node;
class Operation;
class Statement;
class SubroutineReturn;
}  // namespace souffle::ram

namespace souffle::ast2ram {
class ValueIndex;
}

namespace souffle::ast2ram::provenance {

class UnitTranslator : public ast2ram::seminaive::UnitTranslator {
public:
    UnitTranslator() : ast2ram::seminaive::UnitTranslator() {}

protected:
    Own<ram::Sequence> generateProgram(const ast::TranslationUnit& translationUnit) override;
    Own<ram::Statement> generateClearExpiredRelations(
            const std::set<const ast::Relation*>& expiredRelations) const override;

private:
    /** translate RAM code for subroutine to get subproofs */
    Own<ram::Statement> makeSubproofSubroutine(const ast::Clause& clause);

    /** translate RAM code for subroutine to get subproofs for non-existence of a tuple */
    Own<ram::Statement> makeNegationSubproofSubroutine(const ast::Clause& clause);

    void addProvenanceClauseSubroutines(const ast::Program* program);

    Own<ram::ExistenceCheck> makeRamAtomExistenceCheck(const ast::Atom* atom,
            const std::map<int, const ast::Variable*>& idToVar, ValueIndex& valueIndex) const;
    Own<ram::SubroutineReturn> makeRamReturnTrue() const;
    Own<ram::SubroutineReturn> makeRamReturnFalse() const;
    void transformVariablesToSubroutineArgs(
            ram::Node* node, const std::map<int, const ast::Variable*>& idToVar) const;
    Own<ram::Sequence> makeIfStatement(
            Own<ram::Condition> condition, Own<ram::Operation> trueOp, Own<ram::Operation> falseOp) const;
};

}  // namespace souffle::ast2ram::provenance
