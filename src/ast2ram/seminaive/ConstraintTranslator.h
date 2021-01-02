/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ConstraintTranslator.h
 *
 ***********************************************************************/

#pragma once

#include "ast/utility/Visitor.h"
#include "ast2ram/ConstraintTranslator.h"
#include "souffle/utility/ContainerUtil.h"

namespace souffle {
class SymbolTable;
}

namespace souffle::ast {
class Atom;
class BinaryConstraint;
class Negation;
}  // namespace souffle::ast

namespace souffle::ram {
class Condition;
}

namespace souffle::ast2ram {
class TranslatorContext;
class ValueIndex;
}  // namespace souffle::ast2ram

namespace souffle::ast2ram::seminaive {

class ConstraintTranslator : public ast2ram::ConstraintTranslator {
public:
    ConstraintTranslator(const TranslatorContext& context, SymbolTable& symbolTable, const ValueIndex& index)
            : ast2ram::ConstraintTranslator(context, symbolTable, index) {}

    Own<ram::Condition> translateConstraint(const ast::Literal* lit) override;

    /** -- Visitors -- */
    Own<ram::Condition> visitAtom(const ast::Atom&) override;
    Own<ram::Condition> visitBinaryConstraint(const ast::BinaryConstraint& binRel) override;
    Own<ram::Condition> visitNegation(const ast::Negation& neg) override;
};

}  // namespace souffle::ast2ram::seminaive
