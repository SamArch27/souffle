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
#include "ram/utility/Visitor.h"
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
                const Relation& rel = relAnalysis->lookup(scan->getRelation());
                if (scan->getTupleId() == 0 && rel.getArity() > 0) {
                    if (!isA<Project>(&scan->getOperation())) {
                        changed = true;
                        return mk<ParallelScan>(scan->getRelation(), scan->getTupleId(),
                                souffle::clone(&scan->getOperation()), scan->getProfileText());
                    }
                }
            } else if (const Choice* choice = dynamic_cast<Choice*>(node.get())) {
                if (choice->getTupleId() == 0) {
                    changed = true;
                    return mk<ParallelChoice>(choice->getRelation(), choice->getTupleId(),
                            souffle::clone(&choice->getCondition()), souffle::clone(&choice->getOperation()),
                            choice->getProfileText());
                }
            } else if (const IndexScan* indexScan = dynamic_cast<IndexScan*>(node.get())) {
                if (indexScan->getTupleId() == 0) {
                    changed = true;
                    RamPattern queryPattern = clone(indexScan->getRangePattern());
                    return mk<ParallelIndexScan>(indexScan->getRelation(), indexScan->getTupleId(),
                            std::move(queryPattern), souffle::clone(&indexScan->getOperation()),
                            indexScan->getProfileText());
                }
            } else if (const IndexChoice* indexChoice = dynamic_cast<IndexChoice*>(node.get())) {
                if (indexChoice->getTupleId() == 0) {
                    changed = true;
                    RamPattern queryPattern = clone(indexChoice->getRangePattern());
                    return mk<ParallelIndexChoice>(indexChoice->getRelation(), indexChoice->getTupleId(),
                            souffle::clone(&indexChoice->getCondition()), std::move(queryPattern),
                            souffle::clone(&indexChoice->getOperation()), indexChoice->getProfileText());
                }
            } else if (const Aggregate* aggregate = dynamic_cast<Aggregate*>(node.get())) {
                const Relation& rel = relAnalysis->lookup(aggregate->getRelation());
                if (aggregate->getTupleId() == 0 && !rel.isNullary()) {
                    changed = true;
                    return mk<ParallelAggregate>(Own<Operation>(aggregate->getOperation().clone()),
                            aggregate->getFunction(), aggregate->getRelation(),
                            Own<Expression>(aggregate->getExpression().clone()),
                            Own<Condition>(aggregate->getCondition().clone()), aggregate->getTupleId());
                }
            } else if (const IndexAggregate* indexAggregate = dynamic_cast<IndexAggregate*>(node.get())) {
                const Relation& rel = relAnalysis->lookup(indexAggregate->getRelation());
                if (indexAggregate->getTupleId() == 0 && !rel.isNullary()) {
                    changed = true;
                    RamPattern queryPattern = clone(indexAggregate->getRangePattern());
                    return mk<ParallelIndexAggregate>(Own<Operation>(indexAggregate->getOperation().clone()),
                            indexAggregate->getFunction(), indexAggregate->getRelation(),
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
