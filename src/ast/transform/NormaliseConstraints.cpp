/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file NormaliseConstraints.cpp
 *
 ***********************************************************************/

#include "ast/transform/NormaliseConstraints.h"
#include "ast/Argument.h"
#include "ast/BinaryConstraint.h"
#include "ast/Clause.h"
#include "ast/Literal.h"
#include "ast/Node.h"
#include "ast/NumericConstant.h"
#include "ast/Program.h"
#include "ast/Relation.h"
#include "ast/StringConstant.h"
#include "ast/TranslationUnit.h"
#include "ast/UnnamedVariable.h"
#include "ast/Variable.h"
#include "ast/utility/NodeMapper.h"
#include "ast/utility/Utils.h"
#include "souffle/BinaryConstraintOps.h"
#include "souffle/utility/MiscUtil.h"
#include <cassert>
#include <memory>
#include <optional>
#include <ostream>
#include <set>
#include <vector>

namespace souffle::ast::transform {

bool NormaliseConstraintsTransformer::transform(TranslationUnit& translationUnit) {
    bool changed = false;

    // set a prefix for variables bound by magic-set for identification later
    // prepended by + to avoid conflict with user-defined variables
    static constexpr const char* boundPrefix = "+abdul";

    Program& program = translationUnit.getProgram();

    /* Create a node mapper that recursively replaces all constants and underscores
     * with named variables.
     *
     * The mapper keeps track of constraints that should be added to the original
     * clause it is being applied on in a given constraint set.
     */
    struct constraintNormaliser : public NodeMapper {
        std::set<BinaryConstraint*>& constraints;
        mutable int changeCount;

        constraintNormaliser(std::set<BinaryConstraint*>& constraints, int changeCount)
                : constraints(constraints), changeCount(changeCount) {}

        bool hasChanged() const {
            return changeCount > 0;
        }

        int getChangeCount() const {
            return changeCount;
        }

        Own<Node> operator()(Own<Node> node) const override {
            if (auto* stringConstant = dynamic_cast<StringConstant*>(node.get())) {
                // string constant found
                changeCount++;

                // create new variable name (with appropriate suffix)
                std::string constantValue = stringConstant->getConstant();
                std::stringstream newVariableName;
                newVariableName << boundPrefix << changeCount << "_" << constantValue << "_s";

                // create new constraint (+abdulX = constant)
                auto newVariable = mk<ast::Variable>(newVariableName.str());
                constraints.insert(new BinaryConstraint(
                        BinaryConstraintOp::EQ, souffle::clone(newVariable), souffle::clone(stringConstant)));

                // update constant to be the variable created
                return newVariable;
            } else if (auto* numberConstant = dynamic_cast<NumericConstant*>(node.get())) {
                // number constant found
                changeCount++;

                // create new variable name (with appropriate suffix)
                std::stringstream newVariableName;
                newVariableName << boundPrefix << changeCount << "_" << numberConstant->getConstant() << "_n";

                assert(numberConstant->getType() && "numeric constant hasn't been poly-constrained");
                auto opEq = *numberConstant->getType() == NumericConstant::Type::Float
                                    ? BinaryConstraintOp::FEQ
                                    : BinaryConstraintOp::EQ;

                // create new constraint (+abdulX = constant)
                auto newVariable = mk<ast::Variable>(newVariableName.str());
                constraints.insert(new BinaryConstraint(
                        opEq, souffle::clone(newVariable), souffle::clone(numberConstant)));

                // update constant to be the variable created
                return newVariable;
            } else if (isA<UnnamedVariable>(node.get())) {
                // underscore found
                changeCount++;

                // create new variable name
                std::stringstream newVariableName;
                newVariableName << "+underscore" << changeCount;

                return mk<ast::Variable>(newVariableName.str());
            }

            node->apply(*this);
            return node;
        }
    };

    int changeCount = 0;  // number of constants and underscores seen so far

    // apply the change to all clauses in the program
    for (Relation* rel : program.getRelations()) {
        for (Clause* clause : getClauses(program, *rel)) {
            if (isFact(*clause)) {
                continue;  // don't normalise facts
            }

            std::set<BinaryConstraint*> constraints;
            constraintNormaliser update(constraints, changeCount);
            clause->apply(update);

            changeCount = update.getChangeCount();
            changed = changed || update.hasChanged();

            for (BinaryConstraint* constraint : constraints) {
                clause->addToBody(Own<BinaryConstraint>(constraint));
            }
        }
    }

    return changed;
}

}  // namespace souffle::ast::transform
