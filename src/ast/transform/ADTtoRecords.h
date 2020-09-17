/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ADTtoRecords.h
 *
 * Defines the desugaring of ADTs to records.
 *
 * Each record has one of two possible forms:
 * - [branch_id, argument]    if a branch takes a single argument.
 * - [branch_id, [arguments]] otherwise
 *
 * Branch ID is given by a lexicographical ordering of branches within an ADT.
 *
 ***********************************************************************/

#pragma once

#include "ast/TranslationUnit.h"
#include "ast/transform/Transformer.h"
#include <string>

namespace souffle::ast::transform {

class ADTtoRecordsTransformer : public Transformer {
public:
    std::string getName() const override {
        return "ADTtoRecords";
    }

    ADTtoRecordsTransformer* clone() const override {
        return new ADTtoRecordsTransformer();
    }

private:
    bool transform(TranslationUnit& translationUnit) override;
};

}  // namespace souffle::ast::transform
