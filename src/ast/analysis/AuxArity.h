/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020, The Souffle Developers. All rights reserved.
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file AuxArity.h
 *
 * Define of AST analyses classes
 *
 ***********************************************************************/

#pragma once

#include "ast/Atom.h"
#include "ast/Program.h"
#include "ast/Relation.h"
#include "ast/TranslationUnit.h"
#include "ast/analysis/Analysis.h"
#include "ast/utility/Utils.h"
#include <string>

namespace souffle::ast::analysis {

/**
 * Determine the auxiliary arity for relations
 */
class AuxiliaryArityAnalysis : public Analysis {
public:
    static constexpr const char* name = "auxiliary-arity";

    AuxiliaryArityAnalysis() : Analysis(name) {}

    void run(const TranslationUnit& translationUnit) override {
        program = translationUnit.getProgram();
    }

    /**
     * Returns the number of auxiliary parameters of an atom's relation
     * @param atom the atom to report on
     * @return number of auxiliary attributes
     */
    size_t getArity(const Atom* atom) const {
        return computeArity(getRelation(*program, atom->getQualifiedName()));
    }

    /**
     * Returns the number of auxiliary parameters of a relation
     * @param relation the relation to report on
     * @return number of auxiliary attributes
     */
    size_t getArity(const Relation* relation) const {
        return computeArity(relation);
    }

private:
    /**
     * Returns the number of auxiliary parameters of a relation
     * @param relation the relation to report on
     * @return number of auxiliary attributes
     */
    size_t computeArity(const Relation* relation) const;

    const Program* program = nullptr;
};

}  // namespace souffle::ast::analysis
