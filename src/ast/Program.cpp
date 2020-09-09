/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Program.cpp
 *
 * Defines the program class
 *
 * TODO(b-scholz): Remove ast/utility/Utils.h dependency!
 *
 ***********************************************************************/

#include "ast/Program.h"
#include "ast/Clause.h"
#include "ast/Directive.h"
#include "ast/FunctorDeclaration.h"
#include "ast/Pragma.h"
#include "ast/QualifiedName.h"
#include "ast/Relation.h"
#include "ast/Type.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/MiscUtil.h"
#include <cassert>
#include <utility>
#include <vector>

namespace souffle {

void AstProgram::addRelation(Own<AstRelation> relation) {
    auto* existingRelation = getIf(getRelations(), [&](const AstRelation* current) {
        return current->getQualifiedName() == relation->getQualifiedName();
    });
    assert(existingRelation == nullptr && "Redefinition of relation!");
    relations.push_back(std::move(relation));
}

bool AstProgram::removeRelationDecl(const AstQualifiedName& name) {
    for (auto it = relations.begin(); it != relations.end(); it++) {
        const auto& rel = *it;
        if (rel->getQualifiedName() == name) {
            relations.erase(it);
            return true;
        }
    }
    return false;
}

void AstProgram::addClause(Own<AstClause> clause) {
    assert(clause != nullptr && "Undefined clause");
    assert(clause->getHead() != nullptr && "Undefined head of the clause");
    clauses.push_back(std::move(clause));
}

bool AstProgram::removeClause(const AstClause* clause) {
    for (auto it = clauses.begin(); it != clauses.end(); it++) {
        if (**it == *clause) {
            clauses.erase(it);
            return true;
        }
    }
    return false;
}

bool AstProgram::removeDirective(const AstDirective* directive) {
    for (auto it = directives.begin(); it != directives.end(); it++) {
        if (**it == *directive) {
            directives.erase(it);
            return true;
        }
    }
    return false;
}

void AstProgram::addType(Own<AstType> type) {
    auto* existingType = getIf(getTypes(),
            [&](const AstType* current) { return current->getQualifiedName() == type->getQualifiedName(); });
    assert(existingType == nullptr && "Redefinition of type!");
    types.push_back(std::move(type));
}

void AstProgram::addPragma(Own<AstPragma> pragma) {
    assert(pragma && "NULL pragma");
    pragmas.push_back(std::move(pragma));
}

void AstProgram::addFunctorDeclaration(Own<souffle::AstFunctorDeclaration> f) {
    auto* existingFunctorDecl = getIf(getFunctorDeclarations(),
            [&](const AstFunctorDeclaration* current) { return current->getName() == f->getName(); });
    assert(existingFunctorDecl == nullptr && "Redefinition of functor!");
    functors.push_back(std::move(f));
}

}  // namespace souffle
