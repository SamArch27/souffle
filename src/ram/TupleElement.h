/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file TupleElement.h
 *
 * Defines a class for evaluating values in the Relational Algebra Machine
 *
 ************************************************************************/

#pragma once

#include "ram/Expression.h"
#include "ram/Node.h"
#include <cstdlib>
#include <ostream>

namespace souffle::ram {

/**
 * @class TupleElement
 * @brief Access element from the current tuple in a tuple environment
 *
 * In the following example, the tuple element t0.1 is accessed:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * IF t0.1 in A
 * 	...
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class TupleElement : public Expression {
public:
    TupleElement(size_t ident, size_t elem) : identifier(ident), element(elem) {}
    /** @brief Get identifier */
    int getTupleId() const {
        return identifier;
    }

    /** @brief Get element */
    size_t getElement() const {
        return element;
    }

    TupleElement* clone() const override {
        return new TupleElement(identifier, element);
    }

protected:
    void print(std::ostream& os) const override {
        os << "t" << identifier << "." << element;
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const TupleElement&>(node);
        return identifier == other.identifier && element == other.element;
    }

    /** Identifier for the tuple */
    const size_t identifier;

    /** Element number */
    const size_t element;
};

}  // namespace souffle::ram
