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
 * Each record has a form [branch_id, [arguments]].
 * Branch ID is given by a lexicographical ordering of branches within an ADT.
 *
 ***********************************************************************/

#pragma once

#include "ast/transform/Transformer.h"

namespace souffle {

class ADTtoRecordsTransformer : public AstTransformer {
public:
    std::string getName() const override {
        return "ADTtoRecords";
    }

    ADTtoRecordsTransformer* clone() const override {
        return new ADTtoRecordsTransformer();
    }

private:
    bool transform(AstTranslationUnit& translationUnit) override;
};

}  // namespace souffle
