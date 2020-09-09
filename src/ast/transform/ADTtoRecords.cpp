/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ADTtoRecords.cpp
 *
 ***********************************************************************/

#include "ast/transform/ADTtoRecords.h"
#include "ast/AlgebraicDataType.h"
#include "ast/Argument.h"
#include "ast/BranchInit.h"
#include "ast/Node.h"
#include "ast/NumericConstant.h"
#include "ast/RecordInit.h"
#include "ast/TranslationUnit.h"
#include "ast/analysis/TypeEnvironment.h"
#include "ast/analysis/TypeSystem.h"
#include "souffle/utility/ContainerUtil.h"
#include <cassert>
#include <memory>

namespace souffle {

bool ADTtoRecordsTransformer::transform(AstTranslationUnit& tu) {
    struct ADTsFuneral : public AstNodeMapper {
        mutable bool changed{false};
        AstTranslationUnit& tu;
        const SumTypeBranchesAnalysis& sumTypesBranches = *tu.getAnalysis<SumTypeBranchesAnalysis>();

        ADTsFuneral(AstTranslationUnit& tu) : tu(tu){};

        Own<AstNode> operator()(Own<AstNode> node) const override {
            // Rewrite sub-expressions first
            node->apply(*this);

            if (!isA<AstBranchInit>(node)) {
                return node;
            }

            changed = true;

            auto& adt = *as<AstBranchInit>(node);

            auto& type = sumTypesBranches.unsafeGetType(adt.getConstructor());
            assert(isA<AlgebraicDataType>(type));

            auto& branches = as<AlgebraicDataType>(type)->getBranches();

            // Find branch ID.
            AlgebraicDataType::Branch searchDummy{adt.getConstructor(), {}};
            auto iterToBranch = std::lower_bound(branches.begin(), branches.end(), searchDummy,
                    [](const AlgebraicDataType::Branch& left, const AlgebraicDataType::Branch& right) {
                        return left.name < right.name;
                    });

            // Branch id corresponds to the position in lexicographical ordering.
            auto branchID = std::distance(std::begin(branches), iterToBranch);

            // Collect branch arguments
            VecOwn<AstArgument> branchArguments;
            for (auto* arg : adt.getArguments()) {
                branchArguments.emplace_back(arg->clone());
            }

            // Store branch arguments as record [branch_args...]
            auto branchArgsAsRecord = mk<AstArgument, AstRecordInit>(std::move(branchArguments));

            // Arguments for the resulting record [branch_id, [branch_args...]].
            VecOwn<AstArgument> finalRecordArgs;

            finalRecordArgs.push_back(mk<AstArgument, AstNumericConstant>(branchID));
            finalRecordArgs.push_back(std::move(branchArgsAsRecord));

            return mk<AstRecordInit>(std::move(finalRecordArgs), adt.getSrcLoc());
        }
    };

    ADTsFuneral mapper(tu);
    tu.getProgram()->apply(mapper);
    return mapper.changed;
}

}  // namespace souffle
