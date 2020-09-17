/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Node.h
 *
 * Defines the AST abstract node class
 *
 ***********************************************************************/

#pragma once

#include "parser/SrcLocation.h"
#include <iosfwd>
#include <string>
#include <typeinfo>
#include <utility>
#include <vector>

namespace souffle::ast {

class NodeMapper;

/**
 *  @class Node
 *  @brief Abstract class for syntactic elements in an input program.
 */
class Node {
public:
    Node(SrcLocation loc = {}) : location(std::move(loc)){};
    virtual ~Node() = default;

    /** Return source location of the Node */
    const SrcLocation& getSrcLoc() const {
        return location;
    }

    /** Set source location for the Node */
    void setSrcLoc(SrcLocation l) {
        location = std::move(l);
    }

    /** Return source location of the syntactic element */
    std::string extloc() const {
        return location.extloc();
    }

    /** Equivalence check for two AST nodes */
    bool operator==(const Node& other) const {
        if (this == &other) {
            return true;
        } else if (typeid(*this) == typeid(*&other)) {
            return equal(other);
        }
        return false;
    }

    /** Inequality check for two AST nodes */
    bool operator!=(const Node& other) const {
        return !(*this == other);
    }

    /** Create a clone (i.e. deep copy) of this node */
    virtual Node* clone() const = 0;

    /** Apply the mapper to all child nodes */
    virtual void apply(const NodeMapper& /* mapper */) {}

    /** Obtain a list of all embedded AST child nodes */
    virtual std::vector<const Node*> getChildNodes() const {
        return {};
    }

    /** Print node onto an output stream */
    friend std::ostream& operator<<(std::ostream& out, const Node& node) {
        node.print(out);
        return out;
    }

protected:
    /** Output to a given output stream */
    virtual void print(std::ostream& os) const = 0;

    /** Abstract equality check for two AST nodes */
    virtual bool equal(const Node& /* other */) const {
        return true;
    }

private:
    /** Source location of a syntactic element */
    SrcLocation location;
};

}  // namespace souffle::ast
