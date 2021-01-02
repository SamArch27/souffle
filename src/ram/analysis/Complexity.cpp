/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2019, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Complexity.cpp
 *
 * Implementation of RAM Complexity Analysis
 *
 ***********************************************************************/

#include "ram/analysis/Complexity.h"
#include "ram/Condition.h"
#include "ram/Conjunction.h"
#include "ram/EmptinessCheck.h"
#include "ram/ExistenceCheck.h"
#include "ram/Expression.h"
#include "ram/Negation.h"
#include "ram/Node.h"
#include "ram/ProvenanceExistenceCheck.h"
#include "ram/Relation.h"
#include "ram/utility/Visitor.h"
#include <cassert>

namespace souffle::ram::analysis {

int ComplexityAnalysis::getComplexity(const Node* node) const {
    // visitor
    class ValueComplexityVisitor : public Visitor<int> {
    public:
        ValueComplexityVisitor(RelationAnalysis* relAnalysis) : ra(relAnalysis) {}

        // conjunction
        int visitConjunction(const Conjunction& conj) override {
            return visit(conj.getLHS()) + visit(conj.getRHS());
        }

        // negation
        int visitNegation(const Negation& neg) override {
            return visit(neg.getOperand());
        }

        // existence check
        int visitExistenceCheck(const ExistenceCheck&) override {
            return 2;
        }

        // provenance existence check
        int visitProvenanceExistenceCheck(const ProvenanceExistenceCheck&) override {
            return 2;
        }

        // emptiness check
        int visitEmptinessCheck(const EmptinessCheck& emptiness) override {
            // emptiness check for nullary relations is for free; others have weight one
            return (ra->lookup(emptiness.getRelation()).getArity() > 0) ? 1 : 0;
        }

        // default rule
        int visitNode(const Node&) override {
            return 0;
        }

    protected:
        RelationAnalysis* ra{nullptr};
    };

    assert((isA<Expression>(node) || isA<Condition>(node)) && "not an expression/condition/operation");
    return ValueComplexityVisitor(ra).visit(node);
}

}  // namespace souffle::ram::analysis
