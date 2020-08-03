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
 * Define class for negated atoms.
 *
 ***********************************************************************/

#pragma once

#include "SrcLocation.h"
#include "ast/Atom.h"
#include "ast/Literal.h"
#include "ast/Node.h"
#include "ast/NodeMapper.h"
#include "utility/ContainerUtil.h"
#include "utility/MiscUtil.h"
#include <cassert>
#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * Subclass of Literal that represents a negated atom, * e.g., !parent(x,y).
 * A Negated atom occurs in a body of clause and cannot occur in a head of a clause.
 */
class AstNegation : public AstLiteral {
public:
    AstNegation(Own<AstAtom> atom, SrcLocation loc = {})
            : AstLiteral(std::move(loc)), atom(std::move(atom)) {}

    /** get negated atom */
    AstAtom* getAtom() const {
        return atom.get();
    }

    AstNegation* clone() const override {
        return new AstNegation(souffle::clone(atom), getSrcLoc());
    }

    void apply(const AstNodeMapper& map) override {
        atom = map(std::move(atom));
    }

    std::vector<const AstNode*> getChildNodes() const override {
        return {atom.get()};
    }

protected:
    void print(std::ostream& os) const override {
        os << "!" << *atom;
    }

    bool equal(const AstNode& node) const override {
        assert(nullptr != dynamic_cast<const AstNegation*>(&node));
        const auto& other = static_cast<const AstNegation&>(node);
        return equal_ptr(atom, other.atom);
    }

    /** negated atom */
    Own<AstAtom> atom;
};

}  // end of namespace souffle
