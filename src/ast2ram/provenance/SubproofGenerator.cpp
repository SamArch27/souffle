/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file SubproofGenerator.cpp
 *
 ***********************************************************************/

#include "ast2ram/provenance/SubproofGenerator.h"
#include "Global.h"
#include "ast/Atom.h"
#include "ast/BinaryConstraint.h"
#include "ast/Clause.h"
#include "ast/utility/Utils.h"
#include "ast2ram/ConstraintTranslator.h"
#include "ast2ram/ValueTranslator.h"
#include "ast2ram/seminaive/ClauseTranslator.h"
#include "ast2ram/utility/TranslatorContext.h"
#include "ast2ram/utility/Utils.h"
#include "ast2ram/utility/ValueIndex.h"
#include "ram/Condition.h"
#include "ram/Constraint.h"
#include "ram/Filter.h"
#include "ram/Negation.h"
#include "ram/ProvenanceExistenceCheck.h"
#include "ram/Query.h"
#include "ram/Relation.h"
#include "ram/SignedConstant.h"
#include "ram/Statement.h"
#include "ram/SubroutineArgument.h"
#include "ram/SubroutineReturn.h"
#include "ram/UndefValue.h"

namespace souffle::ast2ram::provenance {

SubproofGenerator::SubproofGenerator(const TranslatorContext& context, SymbolTable& symbolTable)
        : ast2ram::seminaive::ClauseTranslator(context, symbolTable) {}

SubproofGenerator::~SubproofGenerator() = default;

Own<ram::Operation> SubproofGenerator::addNegatedAtom(Own<ram::Operation> op, const ast::Atom* atom) const {
    size_t auxiliaryArity = context.getEvaluationArity(atom);
    assert(auxiliaryArity <= atom->getArity() && "auxiliary arity out of bounds");
    size_t arity = atom->getArity() - auxiliaryArity;

    VecOwn<ram::Expression> values;

    auto args = atom->getArguments();
    for (size_t i = 0; i < arity; i++) {
        values.push_back(context.translateValue(symbolTable, *valueIndex, args[i]));
    }

    // undefined value for rule number
    values.push_back(mk<ram::UndefValue>());
    // add the height annotation for provenanceNotExists
    for (size_t height = 1; height < auxiliaryArity; height++) {
        values.push_back(context.translateValue(symbolTable, *valueIndex, args[arity + height]));
    }

    return mk<ram::Filter>(mk<ram::Negation>(mk<ram::ProvenanceExistenceCheck>(
                                   getConcreteRelationName(atom->getQualifiedName()), std::move(values))),
            std::move(op));
}

Own<ram::Statement> SubproofGenerator::createRamFactQuery(const ast::Clause& clause) const {
    assert(isFact(clause) && "clause should be fact");
    assert(!isRecursive() && "recursive clauses cannot have facts");
    return mk<ram::Query>(generateReturnInstantiatedValues(clause));
}

Own<ram::Statement> SubproofGenerator::createRamRuleQuery(const ast::Clause& clause) {
    assert(isRule(clause) && "clause should be rule");

    // Index all variables and generators in the clause
    valueIndex = mk<ValueIndex>();
    indexClause(clause);

    // Set up the RAM statement bottom-up
    auto op = generateReturnInstantiatedValues(clause);
    op = addVariableBindingConstraints(std::move(op));
    op = addBodyLiteralConstraints(clause, std::move(op));
    op = addGeneratorLevels(std::move(op), clause);
    op = addVariableIntroductions(clause, std::move(op));
    return mk<ram::Query>(std::move(op));
}

Own<ram::Operation> SubproofGenerator::addBodyLiteralConstraints(
        const ast::Clause& clause, Own<ram::Operation> op) const {
    // Add all non-constraints, and then constraints
    std::vector<const ast::Constraint*> constraints;
    for (const auto* lit : clause.getBodyLiterals()) {
        if (const auto* constraint = dynamic_cast<const ast::Constraint*>(lit)) {
            constraints.push_back(constraint);
            continue;
        }

        if (auto condition = context.translateConstraint(symbolTable, *valueIndex, lit)) {
            op = mk<ram::Filter>(std::move(condition), std::move(op));
        }
    }

    for (const auto* constraint : constraints) {
        if (auto condition = context.translateConstraint(symbolTable, *valueIndex, constraint)) {
            op = mk<ram::Filter>(std::move(condition), std::move(op));
        }
    }

    // index of level argument in argument list
    const auto* head = clause.getHead();
    const auto& headArgs = head->getArguments();
    size_t auxiliaryArity = context.getAuxiliaryArity(clause.getHead());
    size_t levelIndex = clause.getHead()->getArguments().size() - auxiliaryArity;
    for (size_t i = 0; i < head->getArity() - auxiliaryArity; i++) {
        auto arg = headArgs.at(i);
        if (const auto* var = dynamic_cast<const ast::Variable*>(arg)) {
            // FIXME: float equiv (`FEQ`)
            auto lhs = context.translateValue(symbolTable, *valueIndex, var);
            auto constraint = mk<ram::Constraint>(
                    BinaryConstraintOp::EQ, std::move(lhs), mk<ram::SubroutineArgument>(i));
            op = mk<ram::Filter>(std::move(constraint), std::move(op));
        } else if (const auto* func = dynamic_cast<const ast::Functor*>(arg)) {
            TypeAttribute returnType = context.getFunctorReturnType(func);
            auto opEq = returnType == TypeAttribute::Float ? BinaryConstraintOp::FEQ : BinaryConstraintOp::EQ;
            auto lhs = context.translateValue(symbolTable, *valueIndex, func);
            auto constraint = mk<ram::Constraint>(opEq, std::move(lhs), mk<ram::SubroutineArgument>(i));
            op = mk<ram::Filter>(std::move(constraint), std::move(op));
        } else if (const auto* rec = dynamic_cast<const ast::RecordInit*>(arg)) {
            auto lhs = context.translateValue(symbolTable, *valueIndex, rec);
            auto constraint = mk<ram::Constraint>(
                    BinaryConstraintOp::EQ, std::move(lhs), mk<ram::SubroutineArgument>(i));
            op = mk<ram::Filter>(std::move(constraint), std::move(op));
        } else if (const auto* adt = dynamic_cast<const ast::BranchInit*>(arg)) {
            // TODO (azreika): fill this out like record arguments
            assert(false && adt && "unhandled");
        }
    }

    // add constraint for each argument in head of atom

    // add level constraints, i.e., that each body literal has height less than that of the head atom
    for (const auto* lit : clause.getBodyLiterals()) {
        if (const auto* atom = dynamic_cast<const ast::Atom*>(lit)) {
            // arity - 1 is the level number in body atoms
            auto arity = atom->getArity();
            auto atomArgs = atom->getArguments();
            auto valLHS = context.translateValue(symbolTable, *valueIndex, atomArgs.at(arity - 1));

            // add the constraint
            auto constraint = mk<ram::Constraint>(
                    BinaryConstraintOp::LT, std::move(valLHS), mk<ram::SubroutineArgument>(levelIndex));
            op = mk<ram::Filter>(std::move(constraint), std::move(op));
        }
    }

    if (isRecursive()) {
        if (clause.getHead()->getArity() > 0) {
            // also negate the head
            op = addNegatedAtom(std::move(op), clause.getHead());
        }

        // also add in prev stuff
        for (size_t i = version + 1; i < sccAtoms.size(); i++) {
            op = addNegatedDeltaAtom(std::move(op), sccAtoms.at(i));
        }
    }

    return op;
}

Own<ram::Operation> SubproofGenerator::generateReturnInstantiatedValues(const ast::Clause& clause) const {
    VecOwn<ram::Expression> values;

    // get all values in the body
    for (ast::Literal* lit : clause.getBodyLiterals()) {
        if (auto atom = dynamic_cast<ast::Atom*>(lit)) {
            for (ast::Argument* arg : atom->getArguments()) {
                values.push_back(context.translateValue(symbolTable, *valueIndex, arg));
            }
        } else if (auto neg = dynamic_cast<ast::Negation*>(lit)) {
            for (ast::Argument* arg : neg->getAtom()->getArguments()) {
                values.push_back(context.translateValue(symbolTable, *valueIndex, arg));
            }
        }
    }

    for (const auto* constraint : ast::getBodyLiterals<const ast::BinaryConstraint>(clause)) {
        values.push_back(context.translateValue(symbolTable, *valueIndex, constraint->getLHS()));
        values.push_back(context.translateValue(symbolTable, *valueIndex, constraint->getRHS()));
    }

    // final provenance negation
    if (isRecursive()) {
        const auto* head = clause.getHead();
        size_t auxiliaryArity = context.getEvaluationArity(head);
        for (size_t i = 0; i < head->getArguments().size() - auxiliaryArity; i++) {
            auto arg = head->getArguments().at(i);
            values.push_back(context.translateValue(symbolTable, *valueIndex, arg));
        }
        for (size_t i = 0; i < auxiliaryArity; ++i) {
            values.push_back(mk<ram::SignedConstant>(-1));
        }
    }

    const auto* head = clause.getHead();
    const auto& headArgs = head->getArguments();
    size_t auxiliaryArity = context.getAuxiliaryArity(clause.getHead());
    size_t levelIndex = clause.getHead()->getArguments().size() - auxiliaryArity;
    for (size_t i = 0; i < head->getArity() - auxiliaryArity; i++) {
        auto arg = headArgs.at(i);
        if (const auto* var = dynamic_cast<const ast::Variable*>(arg)) {
            values.push_back(context.translateValue(symbolTable, *valueIndex, var));
            values.push_back(mk<ram::SubroutineArgument>(i));
        } else if (const auto* func = dynamic_cast<const ast::Functor*>(arg)) {
            values.push_back(context.translateValue(symbolTable, *valueIndex, func));
            values.push_back(mk<ram::SubroutineArgument>(i));
        } else if (const auto* rec = dynamic_cast<const ast::RecordInit*>(arg)) {
            values.push_back(context.translateValue(symbolTable, *valueIndex, rec));
            values.push_back(mk<ram::SubroutineArgument>(i));
        } else if (const auto* adt = dynamic_cast<const ast::BranchInit*>(arg)) {
            // TODO (azreika): fill this out like record arguments
            assert(false && adt && "unhandled");
        }
    }

    for (const auto* lit : clause.getBodyLiterals()) {
        if (const auto* atom = dynamic_cast<const ast::Atom*>(lit)) {
            auto arity = atom->getArity();
            auto atomArgs = atom->getArguments();
            values.push_back(context.translateValue(symbolTable, *valueIndex, atomArgs.at(arity - 1)));
            values.push_back(mk<ram::SubroutineArgument>(levelIndex));
        }
    }

    return mk<ram::SubroutineReturn>(std::move(values));
}

}  // namespace souffle::ast2ram::provenance
