/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file UserDefinedFunctors.cpp
 *
 ***********************************************************************/

#include "ast/transform/UserDefinedFunctors.h"
#include "ast/FunctorDeclaration.h"
#include "ast/Node.h"
#include "ast/Program.h"
#include "ast/TranslationUnit.h"
#include "ast/UserDefinedFunctor.h"
#include "ast/utility/NodeMapper.h"
#include "reports/ErrorReport.h"
#include "souffle/TypeAttribute.h"
#include "souffle/utility/ContainerUtil.h"
#include <memory>
#include <vector>

namespace souffle::ast::transform {

bool UserDefinedFunctorsTransformer::transform(TranslationUnit& translationUnit) {
    struct UserFunctorRewriter : public NodeMapper {
        mutable bool changed{false};
        const Program& program;
        ErrorReport& report;

        UserFunctorRewriter(const Program& program, ErrorReport& report) : program(program), report(report){};

        Own<Node> operator()(Own<Node> node) const override {
            node->apply(*this);

            if (auto* userFunctor = dynamic_cast<UserDefinedFunctor*>(node.get())) {
                const FunctorDeclaration* functorDeclaration =
                        getIf(program.getFunctorDeclarations(), [&](const FunctorDeclaration* current) {
                            return current->getName() == userFunctor->getName();
                        });

                // Check if the functor has been declared
                if (functorDeclaration == nullptr) {
                    report.addError("User-defined functor hasn't been declared", userFunctor->getSrcLoc());
                    return node;
                }

                // Check arity correctness.
                if (functorDeclaration->getArity() != userFunctor->getArguments().size()) {
                    report.addError("Mismatching number of arguments of functor", userFunctor->getSrcLoc());
                    return node;
                }

                // Set types of functor instance based on its declaration.
                userFunctor->setTypes(functorDeclaration->getArgsTypes(), functorDeclaration->getReturnType(),
                        functorDeclaration->isStateful());

                changed = true;
            }
            return node;
        }
    };
    UserFunctorRewriter update(*translationUnit.getProgram(), translationUnit.getErrorReport());
    translationUnit.getProgram()->apply(update);
    return update.changed;
}

}  // namespace souffle::ast::transform
