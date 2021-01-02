/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ClauseTranslator.h
 *
 * Translator for clauses from AST to RAM
 *
 ***********************************************************************/

#pragma once

#include "ast2ram/ClauseTranslator.h"
#include "souffle/RamTypes.h"
#include "souffle/utility/ContainerUtil.h"
#include <map>
#include <vector>

namespace souffle {
class SymbolTable;
}

namespace souffle::ast {
class Aggregator;
class Argument;
class Atom;
class BranchInit;
class Clause;
class Constant;
class IntrinsicFunctor;
class Node;
class RecordInit;
class Relation;
}  // namespace souffle::ast

namespace souffle::ram {
class Condition;
class Expression;
class Operation;
class Relation;
class Statement;
}  // namespace souffle::ram

namespace souffle::ast2ram {
class TranslatorContext;
class ValueIndex;
}  // namespace souffle::ast2ram

namespace souffle::ast2ram::seminaive {

class ClauseTranslator : public ast2ram::ClauseTranslator {
public:
    ClauseTranslator(const TranslatorContext& context, SymbolTable& symbolTable);
    ~ClauseTranslator();

    /** Entry points */
    Own<ram::Statement> translateNonRecursiveClause(const ast::Clause& clause);
    Own<ram::Statement> translateRecursiveClause(
            const ast::Clause& clause, const std::set<const ast::Relation*>& scc, size_t version);

protected:
    size_t version{0};
    std::vector<ast::Atom*> sccAtoms{};

    bool isRecursive() const;

    std::string getClauseString(const ast::Clause& clause) const;

    std::string getClauseAtomName(const ast::Clause& clause, const ast::Atom* atom) const;

    virtual Own<ram::Operation> addNegatedAtom(Own<ram::Operation> op, const ast::Atom* atom) const;
    virtual Own<ram::Operation> addNegatedDeltaAtom(Own<ram::Operation> op, const ast::Atom* atom) const;

    Own<ValueIndex> valueIndex;

    /** Main clause translation */
    virtual Own<ram::Statement> createRamFactQuery(const ast::Clause& clause) const;
    virtual Own<ram::Statement> createRamRuleQuery(const ast::Clause& clause);

    virtual Own<ram::Operation> createProjection(const ast::Clause& clause) const;
    virtual Own<ram::Condition> createCondition(const ast::Clause& clause) const;

    std::vector<ast::Atom*> getAtomOrdering(const ast::Clause& clause) const;

    /** Indexing */
    void indexClause(const ast::Clause& clause);
    void indexAtoms(const ast::Clause& clause);
    void indexAggregators(const ast::Clause& clause);
    void indexMultiResultFunctors(const ast::Clause& clause);
    void indexNodeArguments(int nodeLevel, const std::vector<ast::Argument*>& nodeArgs);
    void indexAggregatorBody(const ast::Aggregator& agg);
    void indexGenerator(const ast::Argument& arg);

    /** Core clause translation stages */
    Own<ram::Operation> addVariableBindingConstraints(Own<ram::Operation> op) const;
    virtual Own<ram::Operation> addBodyLiteralConstraints(
            const ast::Clause& clause, Own<ram::Operation> op) const;
    Own<ram::Operation> addGeneratorLevels(Own<ram::Operation> op, const ast::Clause& clause) const;
    Own<ram::Operation> addVariableIntroductions(const ast::Clause& clause, Own<ram::Operation> op);
    Own<ram::Operation> addEntryPoint(const ast::Clause& clause, Own<ram::Operation> op) const;

    /** Levelling methods */
    Own<ram::Operation> addAtomScan(
            Own<ram::Operation> op, const ast::Atom* atom, const ast::Clause& clause, int curLevel) const;
    Own<ram::Operation> addRecordUnpack(
            Own<ram::Operation> op, const ast::RecordInit* rec, int curLevel) const;
    Own<ram::Operation> addAdtUnpack(Own<ram::Operation> op, const ast::BranchInit* adt, int curLevel) const;

    /** Helper methods */
    Own<ram::Operation> addConstantConstraints(
            size_t level, const std::vector<ast::Argument*>& arguments, Own<ram::Operation> op) const;
    Own<ram::Operation> addEqualityCheck(
            Own<ram::Operation> op, Own<ram::Expression> lhs, Own<ram::Expression> rhs, bool isFloat) const;
    Own<ram::Condition> getFunctionalDependencies(const ast::Clause& clause) const;

    /** Constant translation */
    RamDomain getConstantRamRepresentation(SymbolTable& symbolTable, const ast::Constant& constant) const;
    Own<ram::Expression> translateConstant(SymbolTable& symbolTable, const ast::Constant& constant) const;

    /** Generator instantiation */
    Own<ram::Operation> instantiateAggregator(Own<ram::Operation> op, const ast::Clause& clause,
            const ast::Aggregator* agg, int curLevel) const;
    Own<ram::Operation> instantiateMultiResultFunctor(
            Own<ram::Operation> op, const ast::IntrinsicFunctor* inf, int curLevel) const;

private:
    std::vector<const ast::Argument*> generators;
    std::vector<const ast::Node*> operators;

    /** Operation levelling */
    int addGeneratorLevel(const ast::Argument* arg);
    int addOperatorLevel(const ast::Node* node);
};

}  // namespace souffle::ast2ram::seminaive
