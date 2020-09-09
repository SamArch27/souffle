/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file LambdaNodeMapper.h
 *
 * Declaration of RAM node and mappers for RAM nodes
 *
 ***********************************************************************/

#pragma once

#include "ram/NodeMapper.h"
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <typeinfo>
#include <utility>
#include <vector>

namespace souffle {

class RamNode;

/**
 * @class LambdaRamNodeMapper
 * @brief A special RamNodeMapper wrapping a lambda conducting node transformations.
 */
template <typename Lambda>
class LambdaRamNodeMapper : public RamNodeMapper {
    const Lambda& lambda;

public:
    /**
     * @brief Constructor for LambdaRamNodeMapper
     */
    LambdaRamNodeMapper(const Lambda& lambda) : lambda(lambda) {}

    /**
     * @brief Applies lambda
     */
    std::unique_ptr<RamNode> operator()(std::unique_ptr<RamNode> node) const override {
        std::unique_ptr<RamNode> result = lambda(std::move(node));
        assert(result != nullptr && "null-pointer in lambda ram-node mapper");
        return result;
    }
};

/**
 * @brief Creates a node mapper based on a corresponding lambda expression.
 */
template <typename Lambda>
LambdaRamNodeMapper<Lambda> makeLambdaRamMapper(const Lambda& lambda) {
    return LambdaRamNodeMapper<Lambda>(lambda);
}

}  // end of namespace souffle
