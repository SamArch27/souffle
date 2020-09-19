/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file IndexedInequality.cpp
 *
 ***********************************************************************/

#include "ram/transform/IndexedInequality.h"
#include "ram/Condition.h"
#include "ram/Expression.h"
#include "ram/Node.h"
#include "ram/Operation.h"
#include "ram/Program.h"
#include "ram/Relation.h"
#include "ram/Statement.h"
#include "ram/Utils.h"
#include "ram/Visitor.h"
#include "souffle/BinaryConstraintOps.h"
#include "souffle/utility/MiscUtil.h"
#include <algorithm>
#include <cstddef>
#include <functional>
#include <memory>
#include <unordered_set>
#include <utility>
#include <vector>

namespace souffle::ram::transform {

bool IndexedInequalityTransformer::transformIndexToFilter(Program& program) {
    bool changed = false;

    // helper for collecting conditions from filter operations
    auto addCondition = [](Own<Condition> condition, Own<Condition> c) -> Own<Condition> {
        if (condition == nullptr) {
            return c;
        } else {
            return mk<Conjunction>(std::move(condition), std::move(c));
        }
    };

    visitDepthFirst(program, [&](const Query& query) {
        std::function<Own<Node>(Own<Node>)> indexToFilterRewriter = [&](Own<Node> node) -> Own<Node> {
            // find a IndexOperation
            if (const IndexOperation* indexOperation = dynamic_cast<IndexOperation*>(node.get())) {
                auto indexSelection = idxAnalysis->getIndexes(indexOperation->getRelation());
                auto attributesToDischarge = indexSelection.getAttributesToDischarge(
                        ram::analysis::SearchSignature::getFixed(
                                idxAnalysis->getSearchSignature(indexOperation)),
                        indexOperation->getRelation());
                auto pattern = indexOperation->getRangePattern();
                Own<Condition> condition;
                RamPattern updatedPattern;

                for (Expression* p : indexOperation->getRangePattern().first) {
                    updatedPattern.first.emplace_back(p->clone());
                }
                for (Expression* p : indexOperation->getRangePattern().second) {
                    updatedPattern.second.emplace_back(p->clone());
                }
                for (auto i : attributesToDischarge) {
                    // move constraints out of the indexed inequality and into a conjuction
                    Own<Constraint> lowerBound;
                    Own<Constraint> upperBound;
                    changed = true;

                    if (!isUndefValue(pattern.first[i])) {
                        lowerBound =
                                mk<Constraint>(getGreaterEqualConstraint(
                                                       indexOperation->getRelation().getAttributeTypes()[i]),
                                        mk<TupleElement>(indexOperation->getTupleId(), i),
                                        souffle::clone(pattern.first[i]));
                        condition = addCondition(std::move(condition), souffle::clone(lowerBound));
                    }

                    if (!isUndefValue(pattern.second[i])) {
                        upperBound = mk<Constraint>(
                                getLessEqualConstraint(indexOperation->getRelation().getAttributeTypes()[i]),
                                mk<TupleElement>(indexOperation->getTupleId(), i),
                                souffle::clone(pattern.second[i]));
                        condition = addCondition(std::move(condition), souffle::clone(upperBound));
                    }

                    // reset the bounds
                    updatedPattern.first[i] = mk<UndefValue>();
                    updatedPattern.second[i] = mk<UndefValue>();
                }

                if (condition) {
                    auto nestedOp = souffle::clone(&indexOperation->getOperation());
                    auto filter = mk<Filter>(souffle::clone(condition), souffle::clone(nestedOp));

                    // need to rewrite the node with the same index operation
                    if (const IndexScan* iscan = dynamic_cast<IndexScan*>(node.get())) {
                        node = mk<IndexScan>(mk<RelationReference>(&iscan->getRelation()),
                                iscan->getTupleId(), std::move(updatedPattern), std::move(filter),
                                iscan->getProfileText());
                    } else if (const ParallelIndexScan* pscan =
                                       dynamic_cast<ParallelIndexScan*>(node.get())) {
                        node = mk<ParallelIndexScan>(mk<RelationReference>(&pscan->getRelation()),
                                pscan->getTupleId(), std::move(updatedPattern), std::move(filter),
                                pscan->getProfileText());
                    } else if (const IndexChoice* ichoice = dynamic_cast<IndexChoice*>(node.get())) {
                        node = mk<IndexChoice>(mk<RelationReference>(&ichoice->getRelation()),
                                ichoice->getTupleId(), souffle::clone(&ichoice->getCondition()),
                                std::move(updatedPattern), std::move(filter), ichoice->getProfileText());
                    } else if (const IndexAggregate* iagg = dynamic_cast<IndexAggregate*>(node.get())) {
                        // in the case of an aggregate we must strengthen the condition of the aggregate
                        // it doesn't make sense to nest a filter operation because the aggregate needs the
                        // condition in its scope
                        auto strengthenedCondition = addCondition(
                                Own<Condition>(souffle::clone(&iagg->getCondition())), std::move(condition));

                        node = mk<IndexAggregate>(std::move(nestedOp), iagg->getFunction(),
                                mk<RelationReference>(&iagg->getRelation()),
                                souffle::clone(&iagg->getExpression()), std::move(strengthenedCondition),
                                std::move(updatedPattern), iagg->getTupleId());
                    } else {
                        fatal("New IndexOperation subclass found but not supported while making index.");
                    }
                }
            }
            node->apply(makeLambdaRamMapper(indexToFilterRewriter));
            return node;
        };
        const_cast<Query*>(&query)->apply(makeLambdaRamMapper(indexToFilterRewriter));
    });

    visitDepthFirst(program, [&](const Query& query) {
        std::function<Own<Node>(Own<Node>)> removeEmptyIndexRewriter = [&](Own<Node> node) -> Own<Node> {
            // find an IndexOperation
            if (const IndexOperation* indexOperation = dynamic_cast<IndexOperation*>(node.get())) {
                auto pattern = indexOperation->getRangePattern();
                size_t length = pattern.first.size();
                bool foundRealIndexableOperation = false;

                for (size_t i = 0; i < length; ++i) {
                    // if both bounds are undefined we don't have a box query
                    if (isUndefValue(pattern.first[i]) && isUndefValue(pattern.second[i])) {
                        continue;
                    }
                    // if lower and upper bounds are equal its also not a box query
                    foundRealIndexableOperation = true;
                    break;
                }
                if (!foundRealIndexableOperation) {
                    // need to rewrite the node with a semantically equivalent operation to get rid of the
                    // index operation i.e. IndexScan with no indexable attributes -> Scan
                    if (const IndexScan* iscan = dynamic_cast<IndexScan*>(node.get())) {
                        node = mk<Scan>(mk<RelationReference>(&iscan->getRelation()), iscan->getTupleId(),
                                souffle::clone(&iscan->getOperation()), iscan->getProfileText());
                    } else if (const ParallelIndexScan* pscan =
                                       dynamic_cast<ParallelIndexScan*>(node.get())) {
                        node = mk<ParallelScan>(mk<RelationReference>(&pscan->getRelation()),
                                pscan->getTupleId(), souffle::clone(&pscan->getOperation()),
                                pscan->getProfileText());
                    } else if (const IndexChoice* ichoice = dynamic_cast<IndexChoice*>(node.get())) {
                        node = mk<Choice>(mk<RelationReference>(&ichoice->getRelation()),
                                ichoice->getTupleId(), souffle::clone(&ichoice->getCondition()),
                                souffle::clone(&ichoice->getOperation()), ichoice->getProfileText());
                    } else if (const IndexAggregate* iagg = dynamic_cast<IndexAggregate*>(node.get())) {
                        node = mk<Aggregate>(souffle::clone(&iagg->getOperation()), iagg->getFunction(),
                                mk<RelationReference>(&iagg->getRelation()),
                                souffle::clone(&iagg->getExpression()), souffle::clone(&iagg->getCondition()),
                                iagg->getTupleId());
                    } else {
                        fatal("New IndexOperation subclass found but not supported while transforming "
                              "index.");
                    }
                }
            }
            node->apply(makeLambdaRamMapper(removeEmptyIndexRewriter));
            return node;
        };
        const_cast<Query*>(&query)->apply(makeLambdaRamMapper(removeEmptyIndexRewriter));
    });
    return changed;
}

}  // namespace souffle::ram::transform
