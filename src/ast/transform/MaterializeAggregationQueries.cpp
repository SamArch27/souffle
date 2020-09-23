/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file MaterializeAggregationQueries.cpp
 *
 ***********************************************************************/

#include "ast/transform/MaterializeAggregationQueries.h"
#include "AggregateOp.h"
#include "ast/Aggregator.h"
#include "ast/Argument.h"
#include "ast/Atom.h"
#include "ast/Attribute.h"
#include "ast/Clause.h"
#include "ast/Literal.h"
#include "ast/Node.h"
#include "ast/Program.h"
#include "ast/QualifiedName.h"
#include "ast/Relation.h"
#include "ast/TranslationUnit.h"
#include "ast/UnnamedVariable.h"
#include "ast/Variable.h"
#include "ast/analysis/Ground.h"
#include "ast/analysis/Type.h"
#include "ast/analysis/TypeSystem.h"
#include "ast/utility/LambdaNodeMapper.h"
#include "ast/utility/Utils.h"
#include "ast/utility/Visitor.h"
#include "souffle/TypeAttribute.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StringUtil.h"
#include <algorithm>
#include <map>
#include <memory>
#include <set>
#include <utility>
#include <vector>

namespace souffle::ast::transform {

bool MaterializeAggregationQueriesTransformer::materializeAggregationQueries(
        TranslationUnit& translationUnit) {
    bool changed = false;

    Program& program = translationUnit.getProgram();

    // if an aggregator has a body consisting of more than an atom => create new relation
    int counter = 0;
    visitDepthFirst(program, [&](const Clause& clause) {
        visitDepthFirst(clause, [&](const Aggregator& agg) {
            // check whether a materialization is required
            if (!needsMaterializedRelation(agg)) {
                return;
            }
            changed = true;

            // -- create a new clause --

            auto relName = "__agg_body_rel_" + toString(counter++);
            while (getRelation(program, relName) != nullptr) {
                relName = "__agg_body_rel_" + toString(counter++);
            }
            // create the new clause for the materialised rule
            auto* aggClause = new Clause();
            // create the body of the new materialised rule
            for (const auto& cur : agg.getBodyLiterals()) {
                aggClause->addToBody(souffle::clone(cur));
            }
            // find stuff for which we need a grounding
            for (const auto& argPair : analysis::getGroundedTerms(translationUnit, *aggClause)) {
                const auto* variable = dynamic_cast<const ast::Variable*>(argPair.first);
                bool variableIsGrounded = argPair.second;
                // if it's not even a variable type or the term is grounded
                // then skip it
                if (variable == nullptr || variableIsGrounded) {
                    continue;
                }

                for (const auto& lit : clause.getBodyLiterals()) {
                    const auto* atom = dynamic_cast<const Atom*>(lit);
                    if (atom == nullptr) {
                        continue;  // it's not an atom so it can't help ground anything
                    }
                    // Pull in everything that will restrict OR ground the variable
                    bool added = false;
                    visitDepthFirst(*atom, [&](const ast::Variable& var) {
                        if (added) {
                            return;
                        }
                        if (var.getName() == variable->getName()) {
                            aggClause->addToBody(souffle::clone(atom));
                            added = true;
                        }
                    });
                }
            }
            // -- update aggregate --

            // Keep track of variables that occur in the outer scope (i.e. NOT inside any aggregate)
            std::map<std::string, int> varCtr;

            // Start by counting occurrences of all variables in the clause
            visitDepthFirst(clause, [&](const ast::Variable& var) { varCtr[var.getName()]++; });

            // Then count variables occurring in each aggregate
            // so that we can deduce which variable occur only on the outer scope
            std::map<const Aggregator*, std::map<std::string, int>> aggVarMap;
            visitDepthFirst(clause, [&](const Aggregator& agg) {
                visitDepthFirst(agg, [&](const ast::Variable& var) { aggVarMap[&agg][var.getName()]++; });
            });

            std::map<const Aggregator*, const Aggregator*> parent;
            // Figure out parent/child relationships between the aggregates
            // so that we know which variables are occurring on each level
            visitDepthFirstPostOrder(clause, [&](const Aggregator& agg) {
                visitDepthFirst(agg, [&](const Aggregator& descendantAgg) {
                    if (agg == descendantAgg) {
                        return;
                    }
                    if (parent[&descendantAgg] == nullptr) {
                        parent[&descendantAgg] = &agg;
                    }
                });
            });

            // Figure out which variables occur on the outer scope by looking at
            // the aggregates without agggregate parents, and minusing those from
            // the outer scope varCtr map
            visitDepthFirst(clause, [&](const Aggregator& agg) {
                if (parent[&agg] == nullptr) {
                    for (auto const& pair : aggVarMap[&agg]) {
                        std::string varName = pair.first;
                        int numOccurrences = pair.second;
                        varCtr[varName] -= numOccurrences;
                    }
                }
            });
            // But the current aggregate we're dealing with's target expression
            // "counts" as the outer scope, so restore this
            if (agg.getTargetExpression() != nullptr) {
                visitDepthFirst(*agg.getTargetExpression(),
                        [&](const ast::Variable& var) { varCtr[var.getName()]++; });
            }

            // correct aggVarMap so that it counts which variables occurr in the aggregate,
            // and not the variables that occur in an inner aggregate
            // This way, we know which arguments are necessary for the head of the aggregate body relation
            visitDepthFirst(clause, [&](const Aggregator& agg) {
                if (parent[&agg] != nullptr) {
                    // iterate through child map and minus it from the parent map
                    for (auto const& pair : aggVarMap[&agg]) {
                        std::string varName = pair.first;
                        int numOccurrences = pair.second;
                        aggVarMap[parent[&agg]][varName] -= numOccurrences;
                    }
                }
            });

            // build new relation and atom
            auto* head = new Atom();
            head->setQualifiedName(relName);
            std::vector<bool> symbolArguments;

            // Insert all variables occurring in the body of the aggregate into the head
            for (const auto& pair : aggVarMap[&agg]) {
                std::string var = pair.first;
                int n = pair.second;
                // if it doesn't occur in this level, don't add it
                if (n > 0) {
                    head->addArgument(mk<ast::Variable>(var));
                }
            }

            aggClause->setHead(Own<Atom>(head));

            // instantiate unnamed variables in count operations
            if (agg.getOperator() == AggregateOp::COUNT) {
                int count = 0;
                for (const auto& cur : aggClause->getBodyLiterals()) {
                    cur->apply(makeLambdaAstMapper([&](Own<Node> node) -> Own<Node> {
                        // check whether it is a unnamed variable
                        auto* var = dynamic_cast<UnnamedVariable*>(node.get());
                        if (var == nullptr) {
                            return node;
                        }

                        // replace by variable
                        auto name = " _" + toString(count++);
                        auto res = new ast::Variable(name);

                        // extend head
                        head->addArgument(souffle::clone(res));

                        // return replacement
                        return Own<Node>(res);
                    }));
                }
            }

            // -- build relation --

            auto* rel = new Relation();
            rel->setQualifiedName(relName);
            // add attributes
            std::map<const Argument*, analysis::TypeSet> argTypes =
                    analysis::TypeAnalysis::analyseTypes(translationUnit, *aggClause);
            for (const auto& cur : head->getArguments()) {
                rel->addAttribute(mk<Attribute>(toString(*cur),
                        (analysis::isOfKind(argTypes[cur], TypeAttribute::Signed)) ? "number" : "symbol"));
            }

            program.addClause(Own<Clause>(aggClause));
            program.addRelation(Own<Relation>(rel));

            // add arguments to head of aggregate body atom (__agg_body_rel_n)
            VecOwn<Argument> args;
            for (auto arg : head->getArguments()) {
                if (auto* var = dynamic_cast<ast::Variable*>(arg)) {
                    // replace local variable by underscore if local
                    if (varCtr[var->getName()] == 0) {
                        args.emplace_back(new UnnamedVariable());
                        continue;
                    }
                }
                args.emplace_back(arg->clone());
            }
            auto aggAtom = mk<Atom>(head->getQualifiedName(), std::move(args), head->getSrcLoc());

            VecOwn<Literal> newBody;
            newBody.push_back(std::move(aggAtom));
            const_cast<Aggregator&>(agg).setBody(std::move(newBody));
        });
    });
    return changed;
}

bool MaterializeAggregationQueriesTransformer::needsMaterializedRelation(const Aggregator& agg) {
    // everything with more than 1 atom  => materialize
    int countAtoms = 0;
    const Atom* atom = nullptr;
    for (const auto& literal : agg.getBodyLiterals()) {
        const Atom* currentAtom = dynamic_cast<const Atom*>(literal);
        if (currentAtom != nullptr) {
            ++countAtoms;
            atom = currentAtom;
        }
    }

    if (countAtoms > 1) {
        return true;
    }

    bool seenInnerAggregate = false;
    // If we have an aggregate within this aggregate => materialize
    visitDepthFirst(agg, [&](const Aggregator& innerAgg) {
        if (agg != innerAgg) {
            seenInnerAggregate = true;
        }
    });

    if (seenInnerAggregate) {
        return true;
    }

    // If the same variable occurs several times => materialize
    bool duplicates = false;
    std::set<std::string> vars;
    if (atom != nullptr) {
        visitDepthFirst(*atom, [&](const ast::Variable& var) {
            duplicates = duplicates || !vars.insert(var.getName()).second;
        });
    }

    // If there are duplicates a materialization is required
    // for all others the materialization can be skipped
    return duplicates;
}

}  // namespace souffle::ast::transform
