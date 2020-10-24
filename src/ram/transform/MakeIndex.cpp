/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file MakeIndex.cpp
 *
 ***********************************************************************/

#include "ram/transform/MakeIndex.h"
#include "FunctorOps.h"
#include "RelationTag.h"
#include "ram/Condition.h"
#include "ram/Constraint.h"
#include "ram/Expression.h"
#include "ram/Node.h"
#include "ram/Operation.h"
#include "ram/Program.h"
#include "ram/Relation.h"
#include "ram/Statement.h"
#include "ram/utility/Utils.h"
#include "ram/utility/Visitor.h"
#include "souffle/BinaryConstraintOps.h"
#include "souffle/RamTypes.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/MiscUtil.h"
#include <algorithm>
#include <cstddef>
#include <functional>
#include <memory>
#include <tuple>
#include <utility>
#include <vector>

namespace souffle::ram::transform {

using ExpressionPair = std::pair<Own<Expression>, Own<Expression>>;

ExpressionPair MakeIndexTransformer::getExpressionPair(
        const Constraint* binRelOp, size_t& element, int identifier) {
    if (isLessEqual(binRelOp->getOperator())) {
        // Tuple[level, element] <= <expr>
        if (const auto* lhs = dynamic_cast<const TupleElement*>(&binRelOp->getLHS())) {
            const Expression* rhs = &binRelOp->getRHS();
            if (lhs->getTupleId() == identifier && rla->getLevel(rhs) < identifier) {
                element = lhs->getElement();
                return {mk<UndefValue>(), clone(rhs)};
            }
        }
        // <expr> <= Tuple[level, element]
        if (const auto* rhs = dynamic_cast<const TupleElement*>(&binRelOp->getRHS())) {
            const Expression* lhs = &binRelOp->getLHS();
            if (rhs->getTupleId() == identifier && rla->getLevel(lhs) < identifier) {
                element = rhs->getElement();
                return {clone(lhs), mk<UndefValue>()};
            }
        }
    }

    if (isGreaterEqual(binRelOp->getOperator())) {
        // Tuple[level, element] >= <expr>
        if (const auto* lhs = dynamic_cast<const TupleElement*>(&binRelOp->getLHS())) {
            const Expression* rhs = &binRelOp->getRHS();
            if (lhs->getTupleId() == identifier && rla->getLevel(rhs) < identifier) {
                element = lhs->getElement();
                return {clone(rhs), mk<UndefValue>()};
            }
        }
        // <expr> >= Tuple[level, element]
        if (const auto* rhs = dynamic_cast<const TupleElement*>(&binRelOp->getRHS())) {
            const Expression* lhs = &binRelOp->getLHS();
            if (rhs->getTupleId() == identifier && rla->getLevel(lhs) < identifier) {
                element = rhs->getElement();
                return {mk<UndefValue>(), clone(lhs)};
            }
        }
    }
    return {mk<UndefValue>(), mk<UndefValue>()};
}

// Retrieves the <expr1> <= Tuple[level, element] <= <expr2> part of the constraint as a pair { <expr1>,
// <expr2> }
ExpressionPair MakeIndexTransformer::getLowerUpperExpression(Condition* c, size_t& element, int identifier) {
    if (auto* binRelOp = dynamic_cast<Constraint*>(c)) {
        bool interpreter = !Global::config().has("compile") && !Global::config().has("dl-program") &&
                           !Global::config().has("generate") && !Global::config().has("swig");
        // don't index FEQ in interpreter mode
        if (binRelOp->getOperator() == BinaryConstraintOp::FEQ && interpreter) {
            return {mk<UndefValue>(), mk<UndefValue>()};
        } else if (isEqConstraint(binRelOp->getOperator())) {
            if (const auto* lhs = dynamic_cast<const TupleElement*>(&binRelOp->getLHS())) {
                const Expression* rhs = &binRelOp->getRHS();
                if (lhs->getTupleId() == identifier && rla->getLevel(rhs) < identifier) {
                    element = lhs->getElement();
                    return {clone(rhs), clone(rhs)};
                }
            }
            if (const auto* rhs = dynamic_cast<const TupleElement*>(&binRelOp->getRHS())) {
                const Expression* lhs = &binRelOp->getLHS();
                if (rhs->getTupleId() == identifier && rla->getLevel(lhs) < identifier) {
                    element = rhs->getElement();
                    return {clone(lhs), clone(lhs)};
                }
            }
        } else if (isWeakIneqConstraint(binRelOp->getOperator())) {
            return getExpressionPair(binRelOp, element, identifier);
        }
    }
    return {mk<UndefValue>(), mk<UndefValue>()};
}

Own<Condition> MakeIndexTransformer::constructPattern(const std::vector<std::string>& attributeTypes,
        RamPattern& queryPattern, bool& indexable, VecOwn<Condition> conditionList, int identifier) {
    // Remaining conditions which cannot be handled by an index
    Own<Condition> condition;
    auto addCondition = [&](Own<Condition> c) {
        if (condition != nullptr) {
            condition = mk<Conjunction>(std::move(condition), std::move(c));
        } else {
            condition = std::move(c);
        }
    };

    // transform condition list so that every strict inequality becomes a weak inequality + filter
    // e.g. Tuple[level, element] < <expr> --> Tuple[level, element] <= <expr> and Tuple[level, element] !=
    // <expr>
    std::vector<std::unique_ptr<Condition>> toAppend;
    auto it = conditionList.begin();
    while (it != conditionList.end()) {
        auto* binRelOp = dynamic_cast<Constraint*>(it->get());
        if (binRelOp == nullptr) {
            ++it;
            continue;
        }

        bool transformable = false;

        if (isStrictIneqConstraint(binRelOp->getOperator())) {
            if (const auto* lhs = dynamic_cast<const TupleElement*>(&binRelOp->getLHS())) {
                const Expression* rhs = &binRelOp->getRHS();
                if (lhs->getTupleId() == identifier && rla->getLevel(rhs) < identifier) {
                    transformable = true;
                }
            }
            if (const auto* rhs = dynamic_cast<const TupleElement*>(&binRelOp->getRHS())) {
                const Expression* lhs = &binRelOp->getLHS();
                if (rhs->getTupleId() == identifier && rla->getLevel(lhs) < identifier) {
                    transformable = true;
                }
            }
        }

        if (transformable) {
            // append the weak version of inequality
            toAppend.emplace_back(
                    std::make_unique<Constraint>(convertStrictToWeakIneqConstraint(binRelOp->getOperator()),
                            clone(&binRelOp->getLHS()), clone(&binRelOp->getRHS())));
            // append the != constraint
            toAppend.emplace_back(
                    std::make_unique<Constraint>(convertStrictToNotEqualConstraint(binRelOp->getOperator()),
                            clone(&binRelOp->getLHS()), clone(&binRelOp->getRHS())));

            // remove the strict version of inequality
            it = conditionList.erase(it);
        } else {
            ++it;
        }
    }

    std::transform(toAppend.begin(), toAppend.end(), std::back_inserter(conditionList),
            [](const std::unique_ptr<Condition>& cond) { return clone(cond); });

    // Build query pattern and remaining condition
    for (auto& cond : conditionList) {
        size_t element = 0;
        Own<Expression> lowerExpression;
        Own<Expression> upperExpression;
        std::tie(lowerExpression, upperExpression) = getLowerUpperExpression(cond.get(), element, identifier);

        // we have new bounds if at least one is defined
        if (!isUndefValue(lowerExpression.get()) || !isUndefValue(upperExpression.get())) {
            // if no previous bounds are set then just assign them, consider both bounds to be set (but not
            // necessarily defined) in all remaining cases
            auto type = attributeTypes[element];
            indexable = true;
            if (isUndefValue(queryPattern.first[element].get()) &&
                    isUndefValue(queryPattern.second[element].get())) {
                queryPattern.first[element] = std::move(lowerExpression);
                queryPattern.second[element] = std::move(upperExpression);
                // if lower bound is undefined and we have a new lower bound then assign it
            } else if (isUndefValue(queryPattern.first[element].get()) &&
                       !isUndefValue(lowerExpression.get()) && isUndefValue(upperExpression.get())) {
                queryPattern.first[element] = std::move(lowerExpression);
                // if upper bound is undefined and we have a new upper bound then assign it
            } else if (isUndefValue(queryPattern.second[element].get()) &&
                       isUndefValue(lowerExpression.get()) && !isUndefValue(upperExpression.get())) {
                queryPattern.second[element] = std::move(upperExpression);
                // if both bounds are defined ...
                // and equal then we have a previous equality constraint i.e. Tuple[level, element] = <expr1>
            } else if (!isUndefValue(queryPattern.first[element].get()) &&
                       !isUndefValue(queryPattern.second[element].get()) &&
                       (*(queryPattern.first[element]) == *(queryPattern.second[element]))) {
                // new equality constraint i.e. Tuple[level, element] = <expr2>
                // simply hoist <expr1> = <expr2> to the outer loop
                if (!isUndefValue(lowerExpression.get()) && !isUndefValue(upperExpression.get())) {
                    // FIXME: `FEQ` handling; need to know if the expr is a float exp or not
                    addCondition(mk<Constraint>(getEqConstraint(type),
                            souffle::clone(queryPattern.first[element]), std::move(lowerExpression)));
                }
                // new lower bound i.e. Tuple[level, element] >= <expr2>
                // we need to hoist <expr1> >= <expr2> to the outer loop
                else if (!isUndefValue(lowerExpression.get()) && isUndefValue(upperExpression.get())) {
                    addCondition(mk<Constraint>(getGreaterEqualConstraint(type),
                            souffle::clone(queryPattern.first[element]), std::move(lowerExpression)));
                }
                // new upper bound i.e. Tuple[level, element] <= <expr2>
                // we need to hoist <expr1> <= <expr2> to the outer loop
                else if (isUndefValue(lowerExpression.get()) && !isUndefValue(upperExpression.get())) {
                    addCondition(mk<Constraint>(getLessEqualConstraint(type),
                            souffle::clone(queryPattern.first[element]), std::move(upperExpression)));
                }
                // if either bound is defined but they aren't equal we must consider the cases for updating
                // them note that at this point we know that if we have a lower/upper bound it can't be the
                // first one
            } else if (!isUndefValue(queryPattern.first[element].get()) ||
                       !isUndefValue(queryPattern.second[element].get())) {
                // if we have a new equality constraint and previous inequality constraints
                if (!isUndefValue(lowerExpression.get()) && !isUndefValue(upperExpression.get()) &&
                        *lowerExpression == *upperExpression) {
                    // if Tuple[level, element] >= <expr1> and we see Tuple[level, element] = <expr2>
                    // need to hoist <expr2> >= <expr1> to the outer loop
                    if (!isUndefValue(queryPattern.first[element].get())) {
                        addCondition(mk<Constraint>(getGreaterEqualConstraint(type),
                                souffle::clone(lowerExpression), std::move(queryPattern.first[element])));
                    }
                    // if Tuple[level, element] <= <expr1> and we see Tuple[level, element] = <expr2>
                    // need to hoist <expr2> <= <expr1> to the outer loop
                    if (!isUndefValue(queryPattern.second[element].get())) {
                        addCondition(mk<Constraint>(getLessEqualConstraint(type),
                                souffle::clone(upperExpression), std::move(queryPattern.second[element])));
                    }
                    // finally replace bounds with equality constraint
                    queryPattern.first[element] = std::move(lowerExpression);
                    queryPattern.second[element] = std::move(upperExpression);
                    // if we have a new lower bound
                } else if (!isUndefValue(lowerExpression.get())) {
                    // we want the tightest lower bound so we take the max
                    VecOwn<Expression> maxArguments;
                    maxArguments.push_back(std::move(queryPattern.first[element]));
                    maxArguments.push_back(std::move(lowerExpression));

                    queryPattern.first[element] =
                            mk<IntrinsicOperator>(getMaxOp(type), std::move(maxArguments));
                    // if we have a new upper bound
                } else if (!isUndefValue(upperExpression.get())) {
                    // we want the tightest upper bound so we take the min
                    VecOwn<Expression> minArguments;
                    minArguments.push_back(std::move(queryPattern.second[element]));
                    minArguments.push_back(std::move(upperExpression));

                    queryPattern.second[element] =
                            mk<IntrinsicOperator>(getMinOp(type), std::move(minArguments));
                }
            }
        } else {
            addCondition(std::move(cond));
        }
    }

    // Avoid null-pointers for condition and query pattern
    if (condition == nullptr) {
        condition = mk<True>();
    }
    return condition;
}

Own<Operation> MakeIndexTransformer::rewriteAggregate(const Aggregate* agg) {
    if (dynamic_cast<const True*>(&agg->getCondition()) == nullptr) {
        const Relation& rel = relAnalysis->lookup(agg->getRelation());
        int identifier = agg->getTupleId();
        RamPattern queryPattern;
        for (unsigned int i = 0; i < rel.getArity(); ++i) {
            queryPattern.first.push_back(mk<UndefValue>());
            queryPattern.second.push_back(mk<UndefValue>());
        }

        bool indexable = false;
        Own<Condition> condition = constructPattern(rel.getAttributeTypes(), queryPattern, indexable,
                toConjunctionList(&agg->getCondition()), identifier);
        if (indexable) {
            return mk<IndexAggregate>(souffle::clone(&agg->getOperation()), agg->getFunction(),
                    agg->getRelation(), souffle::clone(&agg->getExpression()), std::move(condition),
                    std::move(queryPattern), agg->getTupleId());
        }
    }
    return nullptr;
}

Own<Operation> MakeIndexTransformer::rewriteScan(const Scan* scan) {
    if (const auto* filter = dynamic_cast<const Filter*>(&scan->getOperation())) {
        const Relation& rel = relAnalysis->lookup(scan->getRelation());
        const int identifier = scan->getTupleId();
        RamPattern queryPattern;
        for (unsigned int i = 0; i < rel.getArity(); ++i) {
            queryPattern.first.push_back(mk<UndefValue>());
            queryPattern.second.push_back(mk<UndefValue>());
        }

        bool indexable = false;
        Own<Condition> condition = constructPattern(rel.getAttributeTypes(), queryPattern, indexable,
                toConjunctionList(&filter->getCondition()), identifier);
        if (indexable) {
            Own<Operation> op = souffle::clone(&filter->getOperation());
            if (!isTrue(condition.get())) {
                op = mk<Filter>(std::move(condition), std::move(op));
            }
            return mk<IndexScan>(scan->getRelation(), identifier, std::move(queryPattern), std::move(op),
                    scan->getProfileText());
        }
    }
    return nullptr;
}

Own<Operation> MakeIndexTransformer::rewriteIndexScan(const IndexScan* iscan) {
    if (const auto* filter = dynamic_cast<const Filter*>(&iscan->getOperation())) {
        const Relation& rel = relAnalysis->lookup(iscan->getRelation());
        const int identifier = iscan->getTupleId();

        RamPattern strengthenedPattern;
        strengthenedPattern.first = clone(iscan->getRangePattern().first);
        strengthenedPattern.second = clone(iscan->getRangePattern().second);

        bool indexable = false;
        // strengthen the pattern with construct pattern
        Own<Condition> condition = constructPattern(rel.getAttributeTypes(), strengthenedPattern, indexable,
                toConjunctionList(&filter->getCondition()), identifier);

        if (indexable) {
            // Merge Index Pattern here

            Own<Operation> op = souffle::clone(&filter->getOperation());
            if (!isTrue(condition.get())) {
                op = mk<Filter>(std::move(condition), std::move(op));
            }
            return mk<IndexScan>(iscan->getRelation(), identifier, std::move(strengthenedPattern),
                    std::move(op), iscan->getProfileText());
        }
    }
    return nullptr;
}

bool MakeIndexTransformer::makeIndex(Program& program) {
    bool changed = false;
    visitDepthFirst(program, [&](const Query& query) {
        std::function<Own<Node>(Own<Node>)> scanRewriter = [&](Own<Node> node) -> Own<Node> {
            if (const Scan* scan = dynamic_cast<Scan*>(node.get())) {
                const Relation& rel = relAnalysis->lookup(scan->getRelation());
                if (rel.getRepresentation() != RelationRepresentation::INFO) {
                    if (Own<Operation> op = rewriteScan(scan)) {
                        changed = true;
                        node = std::move(op);
                    }
                }
            } else if (const IndexScan* iscan = dynamic_cast<IndexScan*>(node.get())) {
                if (Own<Operation> op = rewriteIndexScan(iscan)) {
                    changed = true;
                    node = std::move(op);
                }
            } else if (const Aggregate* agg = dynamic_cast<Aggregate*>(node.get())) {
                if (Own<Operation> op = rewriteAggregate(agg)) {
                    changed = true;
                    node = std::move(op);
                }
            }
            node->apply(makeLambdaRamMapper(scanRewriter));
            return node;
        };
        const_cast<Query*>(&query)->apply(makeLambdaRamMapper(scanRewriter));
    });
    return changed;
}

}  // namespace souffle::ram::transform
