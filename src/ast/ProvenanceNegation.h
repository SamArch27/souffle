/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018, The Souffle Developers. All rights reserved.
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ProvenanceNegation.h
 *
 * Defines the provenance negation class
 *
 ***********************************************************************/

#pragma once

#include "ast/Atom.h"
#include "ast/Negation.h"
#include "ast/Node.h"
#include "souffle/utility/MiscUtil.h"
#include <iostream>
#include <memory>

namespace souffle {

/**
 * Subclass of Literal that represents a negated atom, * e.g., !parent(x,y).
 * A Negated atom occurs in a body of clause and cannot occur in a head of a clause.
 *
 * Specialised for provenance: used for existence check that tuple doesn't already exist
 */
class AstProvenanceNegation : public AstNegation {
public:
    using AstNegation::AstNegation;

    AstProvenanceNegation* clone() const override {
        return new AstProvenanceNegation(souffle::clone(atom), getSrcLoc());
    }

protected:
    void print(std::ostream& os) const override {
        os << "prov!" << *atom;
    }
};

}  // end of namespace souffle
