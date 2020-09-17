/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ChoiceConversion.h
 *
 ***********************************************************************/

#pragma once

#include "ram/IndexScan.h"
#include "ram/Operation.h"
#include "ram/Program.h"
#include "ram/Scan.h"
#include "ram/TranslationUnit.h"
#include "ram/analysis/Level.h"
#include "ram/transform/Transformer.h"
#include <memory>
#include <string>

namespace souffle::ram::transform {

/**
 * @class ChoiceConversionTransformer
 * @brief Convert (Scan/If)/(IndexScan/If) operaitons to
 * (Choice)/(IndexChoice) operations

 * If there exists Scan/IndexScan operations in the RAM, and the
 * variables are used in a subsequent Filter operation but no
 * subsequent operation in the tree (up until and including
 * the Project), the operations are rewritten to Choice/IndexChoice
 * operations.
 *
 * For example,
 *
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *  QUERY
 *   ...
 *    FOR t1 IN A ON INDEX t1.x=10 AND t1.y = 20
 *    	IF (t1.x, t1.y) NOT IN A
 *          ... // no occurrence of t1
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *
 * will be rewritten to
 *
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *  QUERY
 *   ...
 *    CHOICE A AS t1 ON INDEX t1.x=10 AND t1.y = 20
 *    WHERE (t1.x, t1.y) NOT IN A
 *      ...
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *
 */
class ChoiceConversionTransformer : public Transformer {
public:
    std::string getName() const override {
        return "ChoiceConversionTransformer";
    }

    /**
     * @brief Rewrite Scan operations
     * @param A scan operation
     * @result The old operation if the if-conversion fails; otherwise the Choice operation
     *
     * Rewrites Scan/If pair to a Choice operation if value
     * is not used in a consecutive RAM operation
     */
    Own<Operation> rewriteScan(const Scan* scan);

    /**
     * @brief Rewrite IndexScan operations
     * @param An index operation
     * @result The old operation if the if-conversion fails; otherwise the IndexChoice operation
     *
     * Rewrites IndexScan/If pair to an IndexChoice operation if value
     * is not used in a consecutive RAM operation
     */
    Own<Operation> rewriteIndexScan(const IndexScan* indexScan);

    /**
     * @brief Apply choice-conversion to the whole program
     * @param RAM program
     * @result A flag indicating whether the RAM program has been changed.
     *
     * Search for queries and rewrite their Scan/IndexScan and If operations if possible.
     */
    bool convertScans(Program& program);

protected:
    analysis::LevelAnalysis* rla{nullptr};
    bool transform(TranslationUnit& translationUnit) override {
        rla = translationUnit.getAnalysis<analysis::LevelAnalysis>();
        return convertScans(translationUnit.getProgram());
    }
};

}  // namespace souffle::ram::transform
