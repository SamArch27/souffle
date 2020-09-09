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

namespace souffle {

class AstNodeMapper;

/**
 *  @class AstNode
 *  @brief Abstract class for syntactic elements in an input program.
 */
class AstNode {
public:
    AstNode(SrcLocation loc = {}) : location(std::move(loc)){};
    virtual ~AstNode() = default;

    /** Return source location of the AstNode */
    const SrcLocation& getSrcLoc() const {
        return location;
    }

    /** Set source location for the AstNode */
    void setSrcLoc(SrcLocation l) {
        location = std::move(l);
    }

    /** Return source location of the syntactic element */
    std::string extloc() const {
        return location.extloc();
    }

    /** Equivalence check for two AST nodes */
    bool operator==(const AstNode& other) const {
        if (this == &other) {
            return true;
        } else if (typeid(*this) == typeid(*&other)) {
            return equal(other);
        }
        return false;
    }

    /** Inequality check for two AST nodes */
    bool operator!=(const AstNode& other) const {
        return !(*this == other);
    }

    /** Create a clone (i.e. deep copy) of this node */
    virtual AstNode* clone() const = 0;

    /** Apply the mapper to all child nodes */
    virtual void apply(const AstNodeMapper& /* mapper */) {}

    /** Obtain a list of all embedded AST child nodes */
    virtual std::vector<const AstNode*> getChildNodes() const {
        return {};
    }

    /** Print node onto an output stream */
    friend std::ostream& operator<<(std::ostream& out, const AstNode& node) {
        node.print(out);
        return out;
    }

protected:
    /** Output to a given output stream */
    virtual void print(std::ostream& os) const = 0;

    /** Abstract equality check for two AST nodes */
    virtual bool equal(const AstNode& /* other */) const {
        return true;
    }

private:
    /** Source location of a syntactic element */
    SrcLocation location;
};

}  // end of namespace souffle
