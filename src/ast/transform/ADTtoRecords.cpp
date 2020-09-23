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
#include "ast/Argument.h"
#include "ast/BranchInit.h"
#include "ast/Node.h"
#include "ast/NumericConstant.h"
#include "ast/Program.h"
#include "ast/RecordInit.h"
#include "ast/TranslationUnit.h"
#include "ast/analysis/SumTypeBranches.h"
#include "ast/analysis/TypeSystem.h"
#include "ast/utility/NodeMapper.h"
#include "souffle/utility/ContainerUtil.h"
#include <algorithm>
#include <cassert>
#include <iterator>
#include <memory>
#include <utility>
#include <vector>

namespace souffle::ast::transform {

bool ADTtoRecordsTransformer::transform(TranslationUnit& tu) {
    struct ADTsFuneral : public NodeMapper {
        mutable bool changed{false};
        TranslationUnit& tu;
        const analysis::SumTypeBranchesAnalysis& sumTypesBranches =
                *tu.getAnalysis<analysis::SumTypeBranchesAnalysis>();

        ADTsFuneral(TranslationUnit& tu) : tu(tu){};

        Own<Node> operator()(Own<Node> node) const override {
            // Rewrite sub-expressions first
            node->apply(*this);

            if (!isA<BranchInit>(node)) {
                return node;
            }

            changed = true;

            auto& adt = *as<BranchInit>(node);

            auto& type = sumTypesBranches.unsafeGetType(adt.getConstructor());
            assert(isA<analysis::AlgebraicDataType>(type));

            auto& branches = as<analysis::AlgebraicDataType>(type)->getBranches();

            // Find branch ID.
            analysis::AlgebraicDataType::Branch searchDummy{adt.getConstructor(), {}};
            auto iterToBranch = std::lower_bound(branches.begin(), branches.end(), searchDummy,
                    [](const analysis::AlgebraicDataType::Branch& left,
                            const analysis::AlgebraicDataType::Branch& right) {
                        return left.name < right.name;
                    });

            // Branch id corresponds to the position in lexicographical ordering.
            auto branchID = std::distance(std::begin(branches), iterToBranch);

            // Collect branch arguments
            VecOwn<Argument> branchArguments;
            for (auto* arg : adt.getArguments()) {
                branchArguments.emplace_back(arg->clone());
            }

            // Branch is stored either as [branch_id, [arguments]]
            // or [branch_id, argument] in case of a single argument.
            auto branchArgs = [&]() -> Own<ast::Argument> {
                if (branchArguments.size() != 1) {
                    return mk<Argument, RecordInit>(std::move(branchArguments));
                } else {
                    return std::move(branchArguments.at(0));
                }
            }();

            // Arguments for the resulting record [branch_id, branch_args].
            VecOwn<Argument> finalRecordArgs;

            finalRecordArgs.push_back(mk<Argument, NumericConstant>(branchID));
            finalRecordArgs.push_back(std::move(branchArgs));

            return mk<RecordInit>(std::move(finalRecordArgs), adt.getSrcLoc());
        }
    };

    ADTsFuneral mapper(tu);
    tu.getProgram().apply(mapper);
    return mapper.changed;
}

}  // namespace souffle::ast::transform
