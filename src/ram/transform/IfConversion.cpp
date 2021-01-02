/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file IfConversion.cpp
 *
 ***********************************************************************/

#include "ram/transform/IfConversion.h"
#include "ram/Condition.h"
#include "ram/Expression.h"
#include "ram/Node.h"
#include "ram/Operation.h"
#include "ram/Program.h"
#include "ram/Relation.h"
#include "ram/Statement.h"
#include "ram/utility/Visitor.h"
#include "souffle/utility/MiscUtil.h"
#include <algorithm>
#include <cstddef>
#include <functional>
#include <utility>
#include <vector>

namespace souffle::ram::transform {

Own<Operation> IfConversionTransformer::rewriteIndexScan(const IndexScan* indexScan) {
    // check whether tuple is used in subsequent operations
    bool tupleNotUsed = true;
    visitDepthFirst(*indexScan, [&](const TupleElement& element) {
        if (element.getTupleId() == indexScan->getTupleId()) {
            tupleNotUsed = false;
        }
    });

    // if not used, transform the IndexScan operation to an existence check
    if (tupleNotUsed) {
        // replace IndexScan with an Filter/Existence check
        VecOwn<Expression> newValues;

        size_t arity = indexScan->getRangePattern().first.size();
        for (size_t i = 0; i < arity; ++i) {
            if (*(indexScan->getRangePattern().first[i]) != *(indexScan->getRangePattern().second[i])) {
                return nullptr;
            }
        }

        for (auto& cur : indexScan->getRangePattern().second) {
            Expression* val = nullptr;
            if (cur != nullptr) {
                val = cur->clone();
            }
            newValues.emplace_back(val);
        }

        // check if there is a break statement nested in the Scan - if so, remove it
        Operation* newOp;
        if (const auto* breakOp = dynamic_cast<const Break*>(&indexScan->getOperation())) {
            newOp = breakOp->getOperation().clone();
        } else {
            newOp = indexScan->getOperation().clone();
        }

        return mk<Filter>(mk<ExistenceCheck>(indexScan->getRelation(), std::move(newValues)),
                Own<Operation>(newOp), indexScan->getProfileText());
    }
    return nullptr;
}

bool IfConversionTransformer::convertIndexScans(Program& program) {
    bool changed = false;
    visitDepthFirst(program, [&](const Query& query) {
        std::function<Own<Node>(Own<Node>)> scanRewriter = [&](Own<Node> node) -> Own<Node> {
            if (const IndexScan* scan = dynamic_cast<IndexScan*>(node.get())) {
                if (Own<Operation> op = rewriteIndexScan(scan)) {
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
