/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020. The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file SimplifyAggregateTargetExpression.h
 *
 ***********************************************************************/
#pragma once

#include "ast/Aggregator.h"
#include "ast/TranslationUnit.h"
#include "ast/transform/Transformer.h"
#include <string>

namespace souffle::ast::transform {
/**
 * Transformation pass to rename aggregation variables to make them unique.
 */
class SimplifyAggregateTargetExpressionTransformer : public Transformer {
public:
    std::string getName() const override {
        return "SimplifyAggregateTargetExpressionTransformer";
    }

    SimplifyAggregateTargetExpressionTransformer* clone() const override {
        return new SimplifyAggregateTargetExpressionTransformer();
    }

private:
    bool transform(TranslationUnit& translationUnit) override;

    /**
     * Generates an equivalent aggregator with a simplified target expression.
     * @param tu translation unit
     * @param clause clause containing the aggregator
     * @param aggregator with a complex target expression
     * @return equivalent aggregator with a simple target expression
     */
    static Aggregator* simplifyTargetExpression(
            const TranslationUnit& tu, const Clause* clause, const Aggregator* aggregator);
};
}  // namespace souffle::ast::transform
