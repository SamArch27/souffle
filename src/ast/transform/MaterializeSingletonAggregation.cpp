/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file MaterializeSingletonAggregation.cpp
 *
 ***********************************************************************/

#include "ast/transform/MaterializeSingletonAggregation.h"
#include "ast/Aggregator.h"
#include "ast/Argument.h"
#include "ast/Atom.h"
#include "ast/Attribute.h"
#include "ast/BinaryConstraint.h"
#include "ast/Clause.h"
#include "ast/Literal.h"
#include "ast/Node.h"
#include "ast/Program.h"
#include "ast/QualifiedName.h"
#include "ast/Relation.h"
#include "ast/TranslationUnit.h"
#include "ast/Variable.h"
#include "ast/analysis/Aggregate.h"
#include "ast/utility/NodeMapper.h"
#include "ast/utility/Utils.h"
#include "ast/utility/Visitor.h"
#include "souffle/BinaryConstraintOps.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StringUtil.h"
#include <cassert>
#include <map>
#include <memory>
#include <set>
#include <utility>
#include <vector>

namespace souffle::ast::transform {

bool MaterializeSingletonAggregationTransformer::transform(TranslationUnit& translationUnit) {
    Program& program = translationUnit.getProgram();
    std::set<std::pair<Aggregator*, Clause*>> pairs;
    // avoid trying to deal with inner aggregates directly.
    // We will apply a fixpoint operator so that it ends up all getting
    // wound out but we can't rush this.
    std::set<const Aggregator*> innerAggregates;
    visitDepthFirst(program, [&](const Aggregator& agg) {
        visitDepthFirst(agg, [&](const Aggregator& innerAgg) {
            if (agg != innerAgg) {
                innerAggregates.insert(&innerAgg);
            }
        });
    });

    // collect references to clause / aggregate pairs
    visitDepthFirst(program, [&](const Clause& clause) {
        visitDepthFirst(clause, [&](const Aggregator& agg) {
            // only unroll one level at a time
            if (innerAggregates.find(&agg) != innerAggregates.end()) {
                return;
            }
            // if the aggregate isn't single valued
            // (ie it relies on a grounding from the outer scope)
            // or it's a constituent of the only atom in the clause,
            // then there's no point materialising it!
            if (!isSingleValued(translationUnit, agg, clause) || clause.getBodyLiterals().size() == 1) {
                return;
            }
            auto* foundAggregate = const_cast<Aggregator*>(&agg);
            auto* foundClause = const_cast<Clause*>(&clause);
            pairs.insert(std::make_pair(foundAggregate, foundClause));
        });
    });
    for (auto pair : pairs) {
        // Clone the aggregate that we're going to be deleting.
        auto aggregate = souffle::clone(pair.first);
        Clause* clause = pair.second;
        // synthesise an aggregate relation
        // __agg_rel_0()
        auto aggRel = mk<Relation>();
        auto aggHead = mk<Atom>();
        auto aggClause = mk<Clause>();

        std::string aggRelName = analysis::findUniqueRelationName(program, "__agg_single");
        aggRel->setQualifiedName(aggRelName);
        aggHead->setQualifiedName(aggRelName);

        // create a synthesised variable to replace the aggregate term!
        std::string variableName = analysis::findUniqueVariableName(*clause, "z");
        auto variable = mk<ast::Variable>(variableName);

        // Infer types
        auto argTypes = analysis::TypeAnalysis::analyseTypes(translationUnit, *clause);
        auto const curArgType = argTypes[pair.first];
        assert(!curArgType.empty() && "unexpected empty typeset");

        // __agg_single(z) :- ...
        aggHead->addArgument(souffle::clone(variable));
        aggRel->addAttribute(mk<Attribute>(variableName, curArgType.begin()->getName()));
        aggClause->setHead(souffle::clone(aggHead));

        //    A(x) :- x = sum .., B(x).
        // -> A(x) :- x = z, B(x), __agg_single(z).
        auto equalityLiteral = mk<BinaryConstraint>(
                BinaryConstraintOp::EQ, souffle::clone(variable), souffle::clone(aggregate));
        // __agg_single(z) :- z = sum ...
        aggClause->addToBody(std::move(equalityLiteral));

        program.addRelation(std::move(aggRel));
        program.addClause(std::move(aggClause));

        // the only thing left to do is just replace the aggregate terms in the original
        // clause with the synthesised variable
        struct replaceAggregate : public NodeMapper {
            const Aggregator& aggregate;
            const Own<ast::Variable> variable;
            replaceAggregate(const Aggregator& aggregate, Own<ast::Variable> variable)
                    : aggregate(aggregate), variable(std::move(variable)) {}
            Own<Node> operator()(Own<Node> node) const override {
                if (auto* current = dynamic_cast<Aggregator*>(node.get())) {
                    if (*current == aggregate) {
                        auto replacement = souffle::clone(variable);
                        assert(replacement != nullptr);
                        return replacement;
                    }
                }
                node->apply(*this);
                return node;
            }
        };
        replaceAggregate update(*aggregate, std::move(variable));
        clause->apply(update);
        clause->addToBody(std::move(aggHead));
    }
    return pairs.size() > 0;
}

bool MaterializeSingletonAggregationTransformer::isSingleValued(
        const TranslationUnit& tu, const Aggregator& agg, const Clause& clause) {
    // An aggregate is single valued as long as it is not complex.
    // This just means there are NO injected variables in the aggregate.
    auto injectedVariables = analysis::getInjectedVariables(tu, clause, agg);
    return injectedVariables.empty();
}

}  // namespace souffle::ast::transform
