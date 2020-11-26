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

#include "souffle/RamTypes.h"
#include "souffle/utility/ContainerUtil.h"
#include <map>
#include <vector>

namespace souffle::ast {
class Argument;
class Clause;
class Constant;
class Node;
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

class ClauseTranslator {
public:
    ClauseTranslator(const TranslatorContext& context) : context(context) {}

    Own<ram::Statement> translateClause(
            const ast::Clause& clause, const ast::Clause& originalClause, const int version = 0);

protected:
    const TranslatorContext& context;

    // value index to keep track of references in the loop nest
    Own<ValueIndex> valueIndex = mk<ValueIndex>();

    // current nesting level
    int level = 0;

    virtual Own<ram::Operation> createOperation(const ast::Clause& clause);
    virtual Own<ram::Condition> createCondition(const ast::Clause& originalClause);

    /** apply constraint filters to a given operation */
    Own<ram::Operation> filterByConstraints(size_t level, const std::vector<ast::Argument*>& arguments,
            Own<ram::Operation> op, bool constrainByFunctors = true);

private:
    std::vector<const ast::Argument*> generators;

    // the order of processed operations
    std::vector<const ast::Node*> op_nesting;

    Own<ast::Clause> getReorderedClause(const ast::Clause& clause, const int version) const;

    void indexValues(const ast::Node* curNode, const std::vector<ast::Argument*>& curNodeArgs,
            std::map<const ast::Node*, int>& nodeLevel, const std::string& relationName,
            size_t relationArity);

    void createValueIndex(const ast::Clause& clause);

    static RamDomain getConstantRamRepresentation(
            const TranslatorContext& context, const ast::Constant& constant);
    static Own<ram::Expression> translateConstant(const TranslatorContext& context, const ast::Constant& c);
};

}  // namespace souffle::ast2ram
