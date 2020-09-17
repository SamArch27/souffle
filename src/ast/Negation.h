/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Negation.h
 *
 * Define the negated atom class
 *
 ***********************************************************************/

#pragma once

#include "ast/Atom.h"
#include "ast/Literal.h"
#include "ast/Node.h"
#include "ast/utility/NodeMapper.h"
#include "parser/SrcLocation.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/MiscUtil.h"
#include <cassert>
#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace souffle::ast {

/**
 * @class Negation
 * @brief Negation of an atom negated atom
 *
 * Example:
 *     !parent(x,y).
 *
 * A negated atom can only occur in the body of a clause.
 */
class Negation : public Literal {
public:
    Negation(Own<Atom> atom, SrcLocation loc = {}) : Literal(std::move(loc)), atom(std::move(atom)) {}

    /** Get negated atom */
    Atom* getAtom() const {
        return atom.get();
    }

    Negation* clone() const override {
        return new Negation(souffle::clone(atom), getSrcLoc());
    }

    void apply(const NodeMapper& map) override {
        atom = map(std::move(atom));
    }

    std::vector<const Node*> getChildNodes() const override {
        return {atom.get()};
    }

protected:
    void print(std::ostream& os) const override {
        os << "!" << *atom;
    }

    bool equal(const Node& node) const override {
        assert(isA<Negation>(&node));
        const auto& other = static_cast<const Negation&>(node);
        return equal_ptr(atom, other.atom);
    }

    /** Negated atom */
    Own<Atom> atom;
};

}  // namespace souffle::ast
