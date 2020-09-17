/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file CollapseFilters.cpp
 *
 ***********************************************************************/

#include "ram/transform/CollapseFilters.h"
#include "ram/Condition.h"
#include "ram/Node.h"
#include "ram/Operation.h"
#include "ram/Program.h"
#include "ram/Statement.h"
#include "ram/Utils.h"
#include "ram/Visitor.h"
#include "souffle/utility/MiscUtil.h"
#include <algorithm>
#include <functional>
#include <memory>
#include <vector>

namespace souffle::ram::transform {

bool CollapseFiltersTransformer::collapseFilters(Program& program) {
    bool changed = false;
    visitDepthFirst(program, [&](const Query& query) {
        std::function<Own<Node>(Own<Node>)> filterRewriter = [&](Own<Node> node) -> Own<Node> {
            if (const Filter* filter = dynamic_cast<Filter*>(node.get())) {
                // true if two consecutive filters in loop nest found
                bool canCollapse = false;

                // storing conditions for collapsing
                VecOwn<Condition> conditions;

                const Filter* prevFilter = filter;
                conditions.emplace_back(filter->getCondition().clone());
                while (auto* nextFilter = dynamic_cast<Filter*>(&prevFilter->getOperation())) {
                    canCollapse = true;
                    conditions.emplace_back(nextFilter->getCondition().clone());
                    prevFilter = nextFilter;
                }

                if (canCollapse) {
                    changed = true;
                    node = mk<Filter>(toCondition(conditions), souffle::clone(&prevFilter->getOperation()),
                            prevFilter->getProfileText());
                }
            }
            node->apply(makeLambdaRamMapper(filterRewriter));
            return node;
        };
        const_cast<Query*>(&query)->apply(makeLambdaRamMapper(filterRewriter));
    });
    return changed;
}

}  // namespace souffle::ram::transform
