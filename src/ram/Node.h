/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Node.h
 *
 * Declaration of RAM node and mappers for RAM nodes
 *
 ***********************************************************************/

#pragma once

#include "ram/LambdaNodeMapper.h"
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <typeinfo>
#include <utility>
#include <vector>

namespace souffle {

class RamNodeMapper;

/**
 *  @class RamNode
 *  @brief RamNode is a superclass for all RAM IR classes.
 */
class RamNode {
public:
    /*
     * @brief A virtual destructor for RAM nodes
     */
    virtual ~RamNode() = default;

    /**
     * @brief Equivalence check for two RAM nodes
     */
    bool operator==(const RamNode& other) const {
        return this == &other || (typeid(*this) == typeid(other) && equal(other));
    }

    /**
     * @brief Inequality check for two RAM nodes
     */
    bool operator!=(const RamNode& other) const {
        return !(*this == other);
    }

    /**
     * @brief Create a clone (i.e. deep copy) of this node
     */
    virtual RamNode* clone() const = 0;

    /**
     * @brief Apply the mapper to all child nodes
     */
    virtual void apply(const RamNodeMapper&) {}

    /**
     * @brief Rewrite a child node
     */
    virtual void rewrite(const RamNode* oldNode, std::unique_ptr<RamNode> newNode) {
        assert(oldNode != nullptr && "old node is a null-pointer");
        assert(newNode != nullptr && "new node is a null-pointer");
        std::function<std::unique_ptr<RamNode>(std::unique_ptr<RamNode>)> rewriter =
                [&](std::unique_ptr<RamNode> node) -> std::unique_ptr<RamNode> {
            if (oldNode == node.get()) {
                return std::move(newNode);
            } else {
                node->apply(makeLambdaRamMapper(rewriter));
                return node;
            }
        };
        apply(makeLambdaRamMapper(rewriter));
    };

    /**
     * @brief Obtain list of all embedded child nodes
     */
    virtual std::vector<const RamNode*> getChildNodes() const {
        return {};
    }

    /**
     * Print RAM on a stream
     */
    friend std::ostream& operator<<(std::ostream& out, const RamNode& node) {
        node.print(out);
        return out;
    }

protected:
    /**
     * @brief Print RAM node
     */
    virtual void print(std::ostream& out = std::cout) const = 0;

    /**
     * @brief Equality check for two RAM nodes.
     * Default action is that nothing needs to be checked.
     */
    virtual bool equal(const RamNode&) const {
        return true;
    }
};

}  // end of namespace souffle
