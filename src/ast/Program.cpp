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
#include <cassert>
#include <string>
#include <utility>
#include <vector>

namespace souffle::ast {

void Program::addRelation(Own<Relation> relation) {
    auto* existingRelation = getIf(getRelations(), [&](const Relation* current) {
        return current->getQualifiedName() == relation->getQualifiedName();
    });
    if (existingRelation != nullptr) {
        return;
    }
    assert(existingRelation == nullptr && "Redefinition of relation!");
    relations.push_back(std::move(relation));
}

bool Program::removeRelationDecl(const QualifiedName& name) {
    for (auto it = relations.begin(); it != relations.end(); it++) {
        const auto& rel = *it;
        if (rel->getQualifiedName() == name) {
            relations.erase(it);
            return true;
        }
    }
    return false;
}

void Program::addClause(Own<Clause> clause) {
    assert(clause != nullptr && "Undefined clause");
    assert(clause->getHead() != nullptr && "Undefined head of the clause");
    clauses.push_back(std::move(clause));
}

bool Program::removeClause(const Clause* clause) {
    for (auto it = clauses.begin(); it != clauses.end(); it++) {
        if (**it == *clause) {
            clauses.erase(it);
            return true;
        }
    }
    return false;
}

bool Program::removeDirective(const Directive* directive) {
    for (auto it = directives.begin(); it != directives.end(); it++) {
        if (**it == *directive) {
            directives.erase(it);
            return true;
        }
    }
    return false;
}

void Program::addType(Own<Type> type) {
    auto* existingType = getIf(getTypes(),
            [&](const Type* current) { return current->getQualifiedName() == type->getQualifiedName(); });
    assert(existingType == nullptr && "Redefinition of type!");
    types.push_back(std::move(type));
}

void Program::addPragma(Own<Pragma> pragma) {
    assert(pragma && "NULL pragma");
    pragmas.push_back(std::move(pragma));
}

void Program::addFunctorDeclaration(Own<FunctorDeclaration> f) {
    auto* existingFunctorDecl = getIf(getFunctorDeclarations(),
            [&](const FunctorDeclaration* current) { return current->getName() == f->getName(); });
    assert(existingFunctorDecl == nullptr && "Redefinition of functor!");
    functors.push_back(std::move(f));
}

void Program::clearComponents() {
    components.clear();
    instantiations.clear();
}

}  // namespace souffle::ast
