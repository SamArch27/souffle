/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file MaterializeSingletonAggregation.h
 *
 * Replaces literals containing single-valued aggregates with
 * a synthesised relation
 *
 ***********************************************************************/

#pragma once

#include "ast/Aggregator.h"
#include "ast/Clause.h"
#include "ast/Program.h"
#include "ast/TranslationUnit.h"
#include "ast/transform/Transformer.h"
#include <string>

namespace souffle::ast::transform {

/**
 * Replaces literals containing single-valued aggregates with
 * a synthesised relation
 */
class MaterializeSingletonAggregationTransformer : public Transformer {
public:
    std::string getName() const override {
        return "MaterializeSingletonAggregationTransformer";
    }

    MaterializeSingletonAggregationTransformer* clone() const override {
        return new MaterializeSingletonAggregationTransformer();
    }

private:
    bool transform(TranslationUnit& translationUnit) override;
    /**
     * Determines whether an aggregate is single-valued,
     * ie the aggregate does not depend on the outer scope.
     */
    static bool isSingleValued(const Aggregator& agg, const Clause& clause);
    /**
     * findUniqueVariableName returns a variable name that hasn't appeared
     * in the given clause.
     */
    static std::string findUniqueVariableName(const Clause& clause);
    /**
     * findUniqueAggregateRelationName returns a synthesised aggregate
     * relation name that hasn't appeared
     * in the given clause.
     */
    static std::string findUniqueAggregateRelationName(const Program& program);
};

}  // namespace souffle::ast::transform
