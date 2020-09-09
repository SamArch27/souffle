/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file NodeMapper.h
 *
 * Declaration of RAM node and mappers for RAM nodes
 *
 ***********************************************************************/

#pragma once

#include "souffle/utility/MiscUtil.h"
#include <cassert>
#include <memory>

namespace souffle {

class RamNode;

/**
 * @class RamNodeMapper
 * @brief An abstract class for manipulating RAM Nodes by substitution
 */
class RamNodeMapper {
public:
    virtual ~RamNodeMapper() = default;

    /**
     * @brief Abstract replacement method for a node.
     *
     * If the given nodes is to be replaced, the handed in node
     * will be destroyed by the mapper and the returned node
     * will become owned by the caller.
     */
    virtual std::unique_ptr<RamNode> operator()(std::unique_ptr<RamNode> node) const = 0;

    /**
     * @brief Wrapper for any subclass of the RAM node hierarchy performing type casts.
     */
    template <typename T>
    std::unique_ptr<T> operator()(std::unique_ptr<T> node) const {
        std::unique_ptr<RamNode> resPtr =
                (*this)(std::unique_ptr<RamNode>(static_cast<RamNode*>(node.release())));
        assert(isA<T>(resPtr.get()) && "Invalid target node!");
        return std::unique_ptr<T>(dynamic_cast<T*>(resPtr.release()));
    }
};

}  // end of namespace souffle
