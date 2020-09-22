/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ExecutionPlanChecker.cpp
 *
 * Implementation of the execution plan checker pass.
 *
 ***********************************************************************/

#include "ast/transform/ExecutionPlanChecker.h"
#include "ast/Atom.h"
#include "ast/Clause.h"
#include "ast/ExecutionOrder.h"
#include "ast/ExecutionPlan.h"
#include "ast/Relation.h"
#include "ast/TranslationUnit.h"
#include "ast/analysis/RecursiveClauses.h"
#include "ast/analysis/RelationSchedule.h"
#include "ast/utility/Utils.h"
#include "reports/ErrorReport.h"
#include <algorithm>
#include <map>
#include <set>
#include <utility>
#include <vector>

namespace souffle::ast::transform {

bool ExecutionPlanChecker::transform(TranslationUnit& translationUnit) {
    auto* relationSchedule = translationUnit.getAnalysis<analysis::RelationScheduleAnalysis>();
    auto* recursiveClauses = translationUnit.getAnalysis<analysis::RecursiveClausesAnalysis>();
    auto&& report = translationUnit.getErrorReport();

    Program& program = translationUnit.getProgram();
    for (const analysis::RelationScheduleAnalysisStep& step : relationSchedule->schedule()) {
        const std::set<const Relation*>& scc = step.computed();
        for (const Relation* rel : scc) {
            for (const Clause* clause : getClauses(program, *rel)) {
                if (!recursiveClauses->recursive(clause)) {
                    continue;
                }
                if (clause->getExecutionPlan() == nullptr) {
                    continue;
                }
                int version = 0;
                for (const auto* atom : getBodyLiterals<Atom>(*clause)) {
                    if (scc.count(getAtomRelation(atom, &program)) != 0u) {
                        version++;
                    }
                }
                int maxVersion = -1;
                for (auto const& cur : clause->getExecutionPlan()->getOrders()) {
                    maxVersion = std::max(cur.first, maxVersion);
                }

                if (version <= maxVersion) {
                    for (const auto& cur : clause->getExecutionPlan()->getOrders()) {
                        if (cur.first >= version) {
                            report.addDiagnostic(Diagnostic(Diagnostic::Type::ERROR,
                                    DiagnosticMessage(
                                            "execution plan for version " + std::to_string(cur.first),
                                            cur.second->getSrcLoc()),
                                    {DiagnosticMessage("only versions 0.." + std::to_string(version - 1) +
                                                       " permitted")}));
                        }
                    }
                }
            }
        }
    }
    return false;
}

}  // namespace souffle::ast::transform
