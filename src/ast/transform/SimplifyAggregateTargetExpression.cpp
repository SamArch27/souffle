/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file SimplifyAggregateTargetExpression.cpp
 *
 ***********************************************************************/

#include "ast/transform/SimplifyAggregateTargetExpression.h"
#include "ast/Argument.h"
#include "ast/TranslationUnit.h"
#include "ast/analysis/Aggregate.h"
#include "ast/transform/GroundWitnesses.h"
#include "ast/utility/NodeMapper.h"
#include "ast/utility/Visitor.h"

namespace souffle::ast::transform {

bool SimplifyAggregateTargetExpressionTransformer::transform(TranslationUnit& translationUnit) {
    Program& program = translationUnit.getProgram();
    // Map all aggregates with complex target expressions to aggregates
    // with simple target expressions and an extra equality literal in the body
    // Note: we need to be careful that we don't inadvertently turn
    // a local variable (recognised as local by the fact that it occurs in the target expression)
    // to an injected variable.
    // I.e it is possible that this happens:
    // .. :- A(y), x = sum y + z : { B(y, z) }
    // -> :- A(y), x = sum z0: { B(y, z), z0 = y + z.
    struct AggregateTESimplifier : public NodeMapper {
        mutable bool changed = false;
        TranslationUnit* tu;
        const Clause* originatingClause;

        AggregateTESimplifier(TranslationUnit* unit, const Clause* c) : tu(unit), originatingClause(c) {}

        bool causedChange() {
            return changed;
        }
        std::unique_ptr<Node> operator()(std::unique_ptr<Node> node) const override {
            if (auto* aggregate = dynamic_cast<Aggregator*>(node.get())) {
                // Check if the target expression is complex
                if (aggregate->getTargetExpression() != nullptr &&
                        dynamic_cast<const Variable*>(aggregate->getTargetExpression()) == nullptr) {
                    // If it's complex, come up with a unique variable name to stand
                    // in the place of the target expression. This will be set equal to the target
                    // expression.
                    // What we might have though now is that a variable in the TE was shadowing
                    // a variable from the outer scope. Now we have "forgotten" this shadowing
                    // and need to restore it by scoping that variable properly.
                    // We know that a variable from the TE is shadowing another variable
                    // if a variable with the same name appears range-restricted in the outer scope.

                    // make a unique target expression variable
                    auto newTargetExpression =
                            mk<Variable>(analysis::findUniqueVariableName(*originatingClause, "x"));
                    auto equalityLiteral = std::make_unique<BinaryConstraint>(BinaryConstraintOp::EQ,
                            souffle::clone(newTargetExpression),
                            souffle::clone(aggregate->getTargetExpression()));
                    std::vector<std::unique_ptr<Literal>> newBody;
                    for (Literal* literal : aggregate->getBodyLiterals()) {
                        newBody.push_back(souffle::clone(literal));
                    }
                    newBody.push_back(std::move(equalityLiteral));
                    // If there are occurrences of the same variable in the outer scope
                    // Then we need to be careful. There are two ensuing situations:
                    // 1) The variable in the outer scope is ungrounded (or occurs in the head)
                    //      => We have a witness, and we shouldn't rename this variable, because it is not
                    //      local.
                    // 2) The variable in the outer scope is grounded
                    //      => We need to rename this because it is a local variable (the grounding of the
                    //      outer scope
                    //         variable is shadowed by occurrence of the variable in the target expression)

                    // We already have a way to find witnesses and also to find variables occurring outside
                    // this aggregate. We will take the set minus of variablesOccurringOutside - witnesses.
                    // Whichever variables are in this set need to be renamed within the aggregate subclause.
                    auto witnesses = analysis::getWitnessVariables(*tu, *originatingClause, *aggregate);
                    std::set<std::string> varsOutside =
                            analysis::getVariablesOutsideAggregate(*originatingClause, *aggregate);

                    std::set<std::string> varsGroundedOutside;
                    for (auto& varName : varsOutside) {
                        if (witnesses.find(varName) == witnesses.end()) {
                            varsGroundedOutside.insert(varName);
                        }
                    }
                    // rename all variables that were grounded outside
                    // (we had an occurrence of the same variable name in the TE,
                    // the implication being that the occurrence of that variable
                    // in the scope of the aggregate subclause should be local,
                    // not grounded from the outer scope (injected)
                    visitDepthFirst(*aggregate->getTargetExpression(), [&](const Variable& v) {
                        if (varsGroundedOutside.find(v.getName()) != varsGroundedOutside.end()) {
                            // rename it everywhere in the body so that we've scoped this properly.
                            std::string newVarName =
                                    analysis::findUniqueVariableName(*originatingClause, v.getName());
                            for (auto& literal : newBody) {
                                visitDepthFirst(*literal, [&](const Variable& literalVar) {
                                    if (literalVar == v) {
                                        const_cast<Variable&>(literalVar).setName(newVarName);
                                    }
                                });
                            }
                        }
                    });

                    // set up a new aggregate to replace this one
                    auto newAggregate = mk<Aggregator>(
                            aggregate->getOperator(), std::move(newTargetExpression), std::move(newBody));
                    changed = true;
                    return newAggregate;
                }
            }
            node->apply(*this);
            return node;
        }
    };

    bool changed = false;
    visitDepthFirst(program, [&](const Clause& clause) {
        Own<Clause> oldClause = souffle::clone(&clause);
        AggregateTESimplifier teSimplifier(&translationUnit, oldClause.get());
        const_cast<Clause&>(clause).apply(teSimplifier);
        changed = changed || teSimplifier.causedChange();
    });
    return changed;
}
}  // namespace souffle::ast::transform
