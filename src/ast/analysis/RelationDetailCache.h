/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file RelationDetailCache.h
 *
 * Defines the class to build the precedence graph,
 * compute strongly connected components of the precedence graph, and
 * build the strongly connected component graph.
 *
 ***********************************************************************/

#pragma once

#include "ast/QualifiedName.h"
#include "ast/Relation.h"
#include "ast/analysis/Analysis.h"
#include <cassert>
#include <map>
#include <set>
#include <string>

namespace souffle::ast {

class Clause;
class TranslationUnit;

namespace analysis {

/**
 * Analysis pass mapping identifiers with relations and clauses.
 */
class RelationDetailCacheAnalysis : public Analysis {
public:
    static constexpr const char* name = "relation-detail";

    RelationDetailCacheAnalysis() : Analysis(name) {}

    void run(const TranslationUnit& translationUnit) override;

    void print(std::ostream& os) const override;

    Relation* getRelation(const QualifiedName& name) const {
        if (nameToRelation.find(name) != nameToRelation.end()) {
            return nameToRelation.at(name);
        }
        return nullptr;
    }

    std::set<Clause*> getClauses(const Relation* rel) const {
        assert(rel != nullptr && "invalid relation");
        return getClauses(rel->getQualifiedName());
    }

    std::set<Clause*> getClauses(const QualifiedName& name) const {
        if (nameToClauses.find(name) != nameToClauses.end()) {
            return nameToClauses.at(name);
        }
        return std::set<Clause*>();
    }

private:
    std::map<QualifiedName, Relation*> nameToRelation;
    std::map<QualifiedName, std::set<Clause*>> nameToClauses;
};

}  // namespace analysis
}  // namespace souffle::ast
