/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file NormaliseMultiResultFunctors.cpp
 *
 * Transform pass to normalise all appearances of multi-result functors.
 *
 ***********************************************************************/

#include "ast/transform/NormaliseMultiResultFunctors.h"
#include "ast/BinaryConstraint.h"
#include "ast/IntrinsicFunctor.h"
#include "ast/Program.h"
#include "ast/TranslationUnit.h"
#include "ast/Variable.h"
#include "ast/analysis/Functor.h"
#include "souffle/utility/ContainerUtil.h"

namespace souffle::ast::transform {

bool NormaliseMultiResultFunctorsTransformer::transform(TranslationUnit& translationUnit) {
    bool changed = false;
    auto& program = translationUnit.getProgram();

    // Assign a unique name to each multi-result functor
    struct name_functors : public NodeMapper {
        mutable int count{0};
        mutable std::vector<std::pair<std::string, Own<IntrinsicFunctor>>> functorNames{};
        name_functors() = default;

        std::vector<std::pair<std::string, Own<IntrinsicFunctor>>> getFunctorNames() {
            return std::move(functorNames);
        }

        Own<Node> operator()(Own<Node> node) const override {
            node->apply(*this);
            if (auto* inf = dynamic_cast<IntrinsicFunctor*>(node.get())) {
                if (analysis::FunctorAnalysis::isMultiResult(*inf)) {
                    std::stringstream newName;
                    newName << "@multires_" << count++;
                    functorNames.push_back({newName.str(), Own<IntrinsicFunctor>(inf->clone())});
                    return mk<Variable>(newName.str());
                }
            }
            return node;
        }
    };

    // Apply the mapper to each clause
    for (auto* clause : program.getClauses()) {
        name_functors update;
        clause->apply(update);
        for (auto& [name, func] : update.getFunctorNames()) {
            changed = true;
            auto eqOp = (func->getFunctionOp() == FunctorOp::FRANGE) ? BinaryConstraintOp::FEQ
                                                                     : BinaryConstraintOp::EQ;
            clause->addToBody(mk<BinaryConstraint>(eqOp, mk<Variable>(name), std::move(func)));
        }
    }
    return changed;
}

}  // namespace souffle::ast::transform
