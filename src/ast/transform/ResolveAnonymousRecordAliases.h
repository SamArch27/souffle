/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ResolveAnonymousRecordAliases.h
 *
 ***********************************************************************/

#pragma once

#include "Transformer.h"
#include <map>
#include <string>

namespace souffle {

class AstClause;
class AstRecordInit;
class AstTranslationUnit;

/**
 * Transformer resolving aliases for anonymous records.
 *
 * The transformer works by searching the clause for equalities
 * of the form a = [...], where a is an anonymous record, and replacing
 * all occurrences of a with the RHS.
 *
 * The transformer is to be called in conjunction with FoldAnonymousRecords.
 **/
class ResolveAnonymousRecordAliases : public AstTransformer {
public:
    std::string getName() const override {
        return "ResolveAnonymousRecordAliases";
    }

    ResolveAnonymousRecordAliases* clone() const override {
        return new ResolveAnonymousRecordAliases();
    }

private:
    bool transform(AstTranslationUnit& translationUnit) override;

    /**
     * Use mapping found by findVariablesRecordMapping to substitute
     * a records for each variable that operates on records.
     **/
    bool replaceNamedVariables(AstTranslationUnit&, AstClause&);

    /**
     * For each variable equal to some anonymous record,
     * assign a value of that record.
     **/
    std::map<std::string, const AstRecordInit*> findVariablesRecordMapping(
            AstTranslationUnit&, const AstClause&);

    /**
     * For unnamed variables, replace each equation _ op record with true.
     **/
    bool replaceUnnamedVariable(AstClause&);
};

}  // end of namespace souffle
