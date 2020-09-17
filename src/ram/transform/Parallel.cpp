/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Parallel.cpp
 *
 ***********************************************************************/

#include "ram/transform/Parallel.h"
#include "ram/Condition.h"
#include "ram/Expression.h"
#include "ram/Node.h"
#include "ram/Operation.h"
#include "ram/Program.h"
#include "ram/Relation.h"
#include "ram/Statement.h"
#include "ram/Visitor.h"
#include "souffle/utility/MiscUtil.h"
#include <functional>
#include <memory>
#include <utility>
#include <vector>

namespace souffle::ram::transform {

bool ParallelTransformer::parallelizeOperations(Program& program) {
    bool changed = false;

    // parallelize the most outer loop only
    // most outer loops can be scan/choice/indexScan/indexChoice
    visitDepthFirst(program, [&](const Query& query) {
        std::function<Own<Node>(Own<Node>)> parallelRewriter = [&](Own<Node> node) -> Own<Node> {
            if (const Scan* scan = dynamic_cast<Scan*>(node.get())) {
                if (scan->getTupleId() == 0 && scan->getRelation().getArity() > 0) {
                    if (!isA<Project>(&scan->getOperation())) {
                        changed = true;
                        return mk<ParallelScan>(mk<RelationReference>(&scan->getRelation()),
                                scan->getTupleId(), souffle::clone(&scan->getOperation()),
                                scan->getProfileText());
                    }
                }
            } else if (const Choice* choice = dynamic_cast<Choice*>(node.get())) {
                if (choice->getTupleId() == 0) {
                    changed = true;
                    return mk<ParallelChoice>(mk<RelationReference>(&choice->getRelation()),
                            choice->getTupleId(), souffle::clone(&choice->getCondition()),
                            souffle::clone(&choice->getOperation()), choice->getProfileText());
                }
            } else if (const IndexScan* indexScan = dynamic_cast<IndexScan*>(node.get())) {
                if (indexScan->getTupleId() == 0) {
                    changed = true;
                    const Relation& rel = indexScan->getRelation();
                    RamPattern queryPattern = clone(indexScan->getRangePattern());
                    return mk<ParallelIndexScan>(mk<RelationReference>(&rel), indexScan->getTupleId(),
                            std::move(queryPattern), souffle::clone(&indexScan->getOperation()),
                            indexScan->getProfileText());
                }
            } else if (const IndexChoice* indexChoice = dynamic_cast<IndexChoice*>(node.get())) {
                if (indexChoice->getTupleId() == 0) {
                    changed = true;
                    const Relation& rel = indexChoice->getRelation();
                    RamPattern queryPattern = clone(indexChoice->getRangePattern());
                    return mk<ParallelIndexChoice>(mk<RelationReference>(&rel), indexChoice->getTupleId(),
                            souffle::clone(&indexChoice->getCondition()), std::move(queryPattern),
                            souffle::clone(&indexChoice->getOperation()), indexChoice->getProfileText());
                }
            } else if (const Aggregate* aggregate = dynamic_cast<Aggregate*>(node.get())) {
                if (aggregate->getTupleId() == 0 && !aggregate->getRelation().isNullary()) {
                    changed = true;
                    const Relation& rel = aggregate->getRelation();
                    return mk<ParallelAggregate>(Own<Operation>(aggregate->getOperation().clone()),
                            aggregate->getFunction(), mk<RelationReference>(&rel),
                            Own<Expression>(aggregate->getExpression().clone()),
                            Own<Condition>(aggregate->getCondition().clone()), aggregate->getTupleId());
                }
            } else if (const IndexAggregate* indexAggregate = dynamic_cast<IndexAggregate*>(node.get())) {
                if (indexAggregate->getTupleId() == 0 && !indexAggregate->getRelation().isNullary()) {
                    changed = true;
                    const Relation& rel = indexAggregate->getRelation();
                    RamPattern queryPattern = clone(indexAggregate->getRangePattern());
                    return mk<ParallelIndexAggregate>(Own<Operation>(indexAggregate->getOperation().clone()),
                            indexAggregate->getFunction(), mk<RelationReference>(&rel),
                            Own<Expression>(indexAggregate->getExpression().clone()),
                            Own<Condition>(indexAggregate->getCondition().clone()), std::move(queryPattern),
                            indexAggregate->getTupleId());
                }
            }
            node->apply(makeLambdaRamMapper(parallelRewriter));
            return node;
        };
        const_cast<Query*>(&query)->apply(makeLambdaRamMapper(parallelRewriter));
    });
    return changed;
}

}  // namespace souffle::ram::transform
