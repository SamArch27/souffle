/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2019, The Souffle Developers. All rights reserved.
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file InterpreterViewContext.h
 *
 * Declares the InterpreterViewContext class.
 * Each Query operation has an InterpreterViewContext assoicated with it.
 * The view context contains information about views creation during execution.
 ***********************************************************************/

#pragma once

#include "interpreter/InterpreterNode.h"
#include <array>
#include <memory>
#include <vector>

namespace souffle {

/**
 * @class InterpreterViewContext
 * @brief This class contains information for views (Hints) creation for ram::Query and ram::Parallel
 * operation.
 */
class InterpreterViewContext {
public:
    /** @brief Add outer-most filter operation which requires a view.  */
    void addViewOperationForFilter(Own<InterpreterNode> node) {
        outerFilterViewOps.push_back(std::move(node));
    }

    /** @brief Add outer-most filter operation which does not require a view.  */
    void addViewFreeOperationForFilter(Own<InterpreterNode> node) {
        outerFilterViewFreeOps.push_back(std::move(node));
    }

    /** @brief Add nested operation which require a View (Hints).  */
    void addViewOperationForNested(Own<InterpreterNode> op) {
        nestedViewOps.push_back(std::move(op));
    }

    /** @brief Return outer-most filter operations.  */
    const VecOwn<InterpreterNode>& getOuterFilterViewOps() {
        return outerFilterViewOps;
    }

    /** @brief Return views for outer-most filter operations.  */
    const VecOwn<InterpreterNode>& getOuterFilterViewFreeOps() {
        return outerFilterViewFreeOps;
    }

    /** @brief Return nested operations */
    VecOwn<InterpreterNode>& getViewsInNestedOperation() {
        return nestedViewOps;
    }

    /** @brief Return Views information for outer filter operation */
    std::vector<std::array<size_t, 3>>& getViewInfoForFilter() {
        return viewInfoForFilter;
    }

    /** @brief Return Views information for nested operation */
    std::vector<std::array<size_t, 3>>& getViewInfoForNested() {
        return viewInfoForNested;
    }

    /** @brief Add View creation information into the list for outer filter.  */
    void addViewInfoForFilter(size_t relId, size_t indexPos, size_t viewPos) {
        viewInfoForFilter.push_back({relId, indexPos, viewPos});
    }

    /** @brief Add View creation information into the list for nested oprations. */
    void addViewInfoForNested(size_t relId, size_t indexPos, size_t viewPos) {
        viewInfoForNested.push_back({relId, indexPos, viewPos});
    }

    /** If this context has information for parallel operation.  */
    bool isParallel = false;

private:
    /** Vector of filter operation, views required */
    VecOwn<InterpreterNode> outerFilterViewOps;
    /** Vector of filter operations, no views required. */
    VecOwn<InterpreterNode> outerFilterViewFreeOps;
    /** Vector of nested operations */
    VecOwn<InterpreterNode> nestedViewOps;
    /** Vector of View information in filter operations */
    std::vector<std::array<size_t, 3>> viewInfoForFilter;
    /** Vector of View information in nested operations */
    std::vector<std::array<size_t, 3>> viewInfoForNested;
};

}  // namespace souffle
