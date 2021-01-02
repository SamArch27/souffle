/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ChoiceConversion.cpp
 *
 ***********************************************************************/

#include "ram/transform/ChoiceConversion.h"
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
#include <functional>
#include <utility>
#include <vector>

namespace souffle::ram::transform {

Own<Operation> ChoiceConversionTransformer::rewriteScan(const Scan* scan) {
    bool transformTuple = false;

    // Check that Filter follows the Scan in the loop nest
    if (const auto* filter = dynamic_cast<const Filter*>(&scan->getOperation())) {
        // Check that the Filter uses the identifier in the Scan
        if (rla->getLevel(&filter->getCondition()) == scan->getTupleId()) {
            transformTuple = true;
            // Check that the filter is not referred to after
            const auto* nextNode = dynamic_cast<const Node*>(&filter->getOperation());

            visitDepthFirst(*nextNode, [&](const TupleElement& element) {
                if (element.getTupleId() == scan->getTupleId()) {
                    transformTuple = false;
                }
            });
        }
    }

    // Convert the Scan/If pair into a Choice
    if (transformTuple) {
        VecOwn<Expression> newValues;
        const auto* filter = dynamic_cast<const Filter*>(&scan->getOperation());
        const int identifier = scan->getTupleId();

        return mk<Choice>(scan->getRelation(), identifier, souffle::clone(&filter->getCondition()),
                souffle::clone(&filter->getOperation()), scan->getProfileText());
    }
    return nullptr;
}

Own<Operation> ChoiceConversionTransformer::rewriteIndexScan(const IndexScan* indexScan) {
    bool transformTuple = false;

    // Check that Filter follows the IndexScan in the loop nest
    if (const auto* filter = dynamic_cast<const Filter*>(&indexScan->getOperation())) {
        // Check that the Filter uses the identifier in the IndexScan
        if (rla->getLevel(&filter->getCondition()) == indexScan->getTupleId()) {
            transformTuple = true;
            // Check that the filter is not referred to after
            const auto* nextNode = dynamic_cast<const Node*>(&filter->getOperation());

            visitDepthFirst(*nextNode, [&](const TupleElement& element) {
                if (element.getTupleId() == indexScan->getTupleId()) {
                    transformTuple = false;
                }
            });
        }
    }

    // Convert the IndexScan/If pair into an IndexChoice
    if (transformTuple) {
        RamPattern newValues;
        const auto* filter = dynamic_cast<const Filter*>(&indexScan->getOperation());
        const int identifier = indexScan->getTupleId();
        const std::string& rel = indexScan->getRelation();

        for (auto& cur : indexScan->getRangePattern().first) {
            Expression* val = nullptr;
            if (cur != nullptr) {
                val = cur->clone();
            }
            newValues.first.emplace_back(val);
        }
        for (auto& cur : indexScan->getRangePattern().second) {
            Expression* val = nullptr;
            if (cur != nullptr) {
                val = cur->clone();
            }
            newValues.second.emplace_back(val);
        }

        return mk<IndexChoice>(rel, identifier, souffle::clone(&filter->getCondition()), std::move(newValues),
                souffle::clone(&filter->getOperation()), indexScan->getProfileText());
    }
    return nullptr;
}

bool ChoiceConversionTransformer::convertScans(Program& program) {
    bool changed = false;
    visitDepthFirst(program, [&](const Query& query) {
        std::function<Own<Node>(Own<Node>)> scanRewriter = [&](Own<Node> node) -> Own<Node> {
            if (const Scan* scan = dynamic_cast<Scan*>(node.get())) {
                if (Own<Operation> op = rewriteScan(scan)) {
                    changed = true;
                    node = std::move(op);
                }
            } else if (const IndexScan* indexScan = dynamic_cast<IndexScan*>(node.get())) {
                if (Own<Operation> op = rewriteIndexScan(indexScan)) {
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
