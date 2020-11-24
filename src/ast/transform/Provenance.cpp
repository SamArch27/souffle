/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2017, The Souffle Developers. All rights reserved.
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Provenance.cpp
 *
 * Implements Transformer for adding provenance information via extra columns
 *
 ***********************************************************************/

#include "ast/transform/Provenance.h"
#include "RelationTag.h"
#include "ast/Aggregator.h"
#include "ast/Argument.h"
#include "ast/Atom.h"
#include "ast/Attribute.h"
#include "ast/BinaryConstraint.h"
#include "ast/Clause.h"
#include "ast/Constant.h"
#include "ast/Functor.h"
#include "ast/IntrinsicFunctor.h"
#include "ast/Literal.h"
#include "ast/Negation.h"
#include "ast/Node.h"
#include "ast/NumericConstant.h"
#include "ast/Program.h"
#include "ast/ProvenanceNegation.h"
#include "ast/QualifiedName.h"
#include "ast/Relation.h"
#include "ast/StringConstant.h"
#include "ast/TranslationUnit.h"
#include "ast/UnnamedVariable.h"
#include "ast/Variable.h"
#include "ast/utility/NodeMapper.h"
#include "ast/utility/Utils.h"
#include "souffle/BinaryConstraintOps.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StreamUtil.h"
#include "souffle/utility/StringUtil.h"
#include "souffle/utility/tinyformat.h"
#include <algorithm>
#include <cassert>
#include <cstddef>
#include <iosfwd>
#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace souffle::ast::transform {

/**
 * Helper functions
 */
inline QualifiedName makeRelationName(const QualifiedName& orig, const std::string& type, int num = -1) {
    QualifiedName newName(toString(orig));
    newName.append(type);
    if (num != -1) {
        newName.append((const std::string&)std::to_string(num));
    }

    return newName;
}

Own<Relation> makeInfoRelation(
        Clause& originalClause, size_t originalClauseNum, TranslationUnit& translationUnit) {
    QualifiedName name =
            makeRelationName(originalClause.getHead()->getQualifiedName(), "@info", originalClauseNum);

    // initialise info relation
    auto infoRelation = new Relation();
    infoRelation->setQualifiedName(name);
    // set qualifier to INFO_RELATION
    infoRelation->setRepresentation(RelationRepresentation::INFO);

    // create new clause containing a single fact
    auto infoClause = new Clause();
    auto infoClauseHead = new Atom();
    infoClauseHead->setQualifiedName(name);

    // (darth_tytus): Can this be unsigned?
    infoRelation->addAttribute(mk<Attribute>("clause_num", QualifiedName("number")));
    infoClauseHead->addArgument(mk<NumericConstant>(originalClauseNum));

    // add head relation as meta info
    std::vector<std::string> headVariables;

    // a method to stringify an Argument, translating functors and aggregates
    // keep a global counter of functor and aggregate numbers, which increment for each unique
    // functor/aggregate
    int functorNumber = 0;
    int aggregateNumber = 0;
    auto getArgInfo = [&](Argument* arg) -> std::string {
        if (auto* var = dynamic_cast<ast::Variable*>(arg)) {
            return toString(*var);
        } else if (auto* constant = dynamic_cast<Constant*>(arg)) {
            return toString(*constant);
        }
        if (isA<UnnamedVariable>(arg)) {
            return "_";
        }
        if (isA<Functor>(arg)) {
            return tfm::format("functor_%d", functorNumber++);
        }
        if (isA<Aggregator>(arg)) {
            return tfm::format("agg_%d", aggregateNumber++);
        }

        fatal("Unhandled argument type");
    };

    // add head arguments
    for (auto& arg : originalClause.getHead()->getArguments()) {
        headVariables.push_back(getArgInfo(arg));
    }

    // join variables in the head with commas
    std::stringstream headVariableString;
    headVariableString << join(headVariables, ",");

    // add an attribute to infoRelation for the head of clause
    infoRelation->addAttribute(mk<Attribute>(std::string("head_vars"), QualifiedName("symbol")));
    infoClauseHead->addArgument(mk<StringConstant>(toString(join(headVariables, ","))));

    // visit all body literals and add to info clause head
    for (size_t i = 0; i < originalClause.getBodyLiterals().size(); i++) {
        auto lit = originalClause.getBodyLiterals()[i];

        const Atom* atom = nullptr;
        if (isA<Atom>(lit)) {
            atom = static_cast<Atom*>(lit);
        } else if (isA<Negation>(lit)) {
            atom = static_cast<Negation*>(lit)->getAtom();
        } else if (isA<ProvenanceNegation>(lit)) {
            atom = static_cast<ProvenanceNegation*>(lit)->getAtom();
        }

        // add an attribute for atoms and binary constraints
        if (atom != nullptr || isA<BinaryConstraint>(lit)) {
            infoRelation->addAttribute(
                    mk<Attribute>(std::string("rel_") + std::to_string(i), QualifiedName("symbol")));
        }

        if (atom != nullptr) {
            std::string relName = toString(atom->getQualifiedName());

            // for an atom, add its name and variables (converting aggregates to variables)
            if (isA<Atom>(lit)) {
                std::string atomDescription = relName;

                for (auto& arg : atom->getArguments()) {
                    atomDescription.append("," + getArgInfo(arg));
                }

                infoClauseHead->addArgument(mk<StringConstant>(atomDescription));
                // for a negation, add a marker with the relation name
            } else if (isA<Negation>(lit)) {
                infoClauseHead->addArgument(mk<StringConstant>("!" + relName));
            }
        }
    }

    // visit all body constraints and add to info clause head
    for (size_t i = 0; i < originalClause.getBodyLiterals().size(); i++) {
        auto lit = originalClause.getBodyLiterals()[i];

        if (auto con = dynamic_cast<BinaryConstraint*>(lit)) {
            // for a constraint, add the constraint symbol and LHS and RHS
            std::string constraintDescription = toBinaryConstraintSymbol(con->getBaseOperator());

            constraintDescription.append("," + getArgInfo(con->getLHS()));
            constraintDescription.append("," + getArgInfo(con->getRHS()));

            infoClauseHead->addArgument(mk<StringConstant>(constraintDescription));
        }
    }

    infoRelation->addAttribute(mk<Attribute>("clause_repr", QualifiedName("symbol")));
    infoClauseHead->addArgument(mk<StringConstant>(toString(originalClause)));

    // set clause head and add clause to info relation
    infoClause->setHead(Own<Atom>(infoClauseHead));
    Program& program = translationUnit.getProgram();
    program.addClause(Own<Clause>(infoClause));

    return Own<Relation>(infoRelation);
}

/** Transform eqrel relations to explicitly define equivalence relations */
void transformEqrelRelation(Program& program, Relation& rel) {
    assert(rel.getRepresentation() == RelationRepresentation::EQREL &&
            "attempting to transform non-eqrel relation");
    assert(rel.getArity() == 2 && "eqrel relation not binary");

    rel.setRepresentation(RelationRepresentation::BTREE);

    // transitivity
    // transitive clause: A(x, z) :- A(x, y), A(y, z).
    auto transitiveClause = new Clause();
    auto transitiveClauseHead = new Atom(rel.getQualifiedName());
    transitiveClauseHead->addArgument(mk<ast::Variable>("x"));
    transitiveClauseHead->addArgument(mk<ast::Variable>("z"));

    auto transitiveClauseBody = new Atom(rel.getQualifiedName());
    transitiveClauseBody->addArgument(mk<ast::Variable>("x"));
    transitiveClauseBody->addArgument(mk<ast::Variable>("y"));

    auto transitiveClauseBody2 = new Atom(rel.getQualifiedName());
    transitiveClauseBody2->addArgument(mk<ast::Variable>("y"));
    transitiveClauseBody2->addArgument(mk<ast::Variable>("z"));

    transitiveClause->setHead(Own<Atom>(transitiveClauseHead));
    transitiveClause->addToBody(Own<Literal>(transitiveClauseBody));
    transitiveClause->addToBody(Own<Literal>(transitiveClauseBody2));
    program.addClause(Own<Clause>(transitiveClause));

    // symmetric
    // symmetric clause: A(x, y) :- A(y, x).
    auto symClause = new Clause();
    auto symClauseHead = new Atom(rel.getQualifiedName());
    symClauseHead->addArgument(mk<ast::Variable>("x"));
    symClauseHead->addArgument(mk<ast::Variable>("y"));

    auto symClauseBody = new Atom(rel.getQualifiedName());
    symClauseBody->addArgument(mk<ast::Variable>("y"));
    symClauseBody->addArgument(mk<ast::Variable>("x"));

    symClause->setHead(Own<Atom>(symClauseHead));
    symClause->addToBody(Own<Literal>(symClauseBody));
    program.addClause(Own<Clause>(symClause));

    // reflexivity
    // reflexive clause: A(x, x) :- A(x, _).
    auto reflexiveClause = new Clause();
    auto reflexiveClauseHead = new Atom(rel.getQualifiedName());
    reflexiveClauseHead->addArgument(mk<ast::Variable>("x"));
    reflexiveClauseHead->addArgument(mk<ast::Variable>("x"));

    auto reflexiveClauseBody = new Atom(rel.getQualifiedName());
    reflexiveClauseBody->addArgument(mk<ast::Variable>("x"));
    reflexiveClauseBody->addArgument(mk<UnnamedVariable>());

    reflexiveClause->setHead(Own<Atom>(reflexiveClauseHead));
    reflexiveClause->addToBody(Own<Literal>(reflexiveClauseBody));
    program.addClause(Own<Clause>(reflexiveClause));
}

namespace {
Own<Argument> getNextLevelNumber(const std::vector<Argument*>& levels) {
    if (levels.empty()) return mk<NumericConstant>(0);

    auto max = levels.size() == 1
                       ? Own<Argument>(levels[0])
                       : mk<IntrinsicFunctor>("max", map(levels, [](auto&& x) { return Own<Argument>(x); }));

    return mk<IntrinsicFunctor>("+", std::move(max), mk<NumericConstant>(1));
}
}  // namespace

bool ProvenanceTransformer::transformMaxHeight(TranslationUnit& translationUnit) {
    Program& program = translationUnit.getProgram();

    for (auto relation : program.getRelations()) {
        if (relation->getRepresentation() == RelationRepresentation::EQREL) {
            // Explicitly expand eqrel relation
            transformEqrelRelation(program, *relation);
        }
    }

    for (auto relation : program.getRelations()) {
        // generate info relations for each clause
        // do this before all other transformations so that we record
        // the original rule without any instrumentation
        for (auto clause : getClauses(program, *relation)) {
            if (!isFact(*clause)) {
                // add info relation
                program.addRelation(
                        makeInfoRelation(*clause, getClauseNum(&program, clause), translationUnit));
                // add prov relation
            }
        }

        relation->addAttribute(mk<Attribute>(std::string("@rule_number"), QualifiedName("number")));
        relation->addAttribute(mk<Attribute>(std::string("@level_number"), QualifiedName("number")));

        for (auto clause : getClauses(program, *relation)) {
            size_t clauseNum = getClauseNum(&program, clause);

            // mapper to add two provenance columns to atoms
            struct M : public NodeMapper {
                using NodeMapper::operator();

                Own<Node> operator()(Own<Node> node) const override {
                    // add provenance columns
                    if (auto atom = dynamic_cast<Atom*>(node.get())) {
                        atom->addArgument(mk<UnnamedVariable>());
                        atom->addArgument(mk<UnnamedVariable>());
                    } else if (auto neg = dynamic_cast<Negation*>(node.get())) {
                        auto atom = neg->getAtom();
                        atom->addArgument(mk<UnnamedVariable>());
                        atom->addArgument(mk<UnnamedVariable>());
                    }

                    // otherwise - apply mapper recursively
                    node->apply(*this);
                    return node;
                }
            };

            // add unnamed vars to each atom nested in arguments of head
            clause->getHead()->apply(M());

            // if fact, level number is 0
            if (isFact(*clause)) {
                clause->getHead()->addArgument(mk<NumericConstant>(0));
                clause->getHead()->addArgument(mk<NumericConstant>(0));
            } else {
                std::vector<Argument*> bodyLevels;

                for (size_t i = 0; i < clause->getBodyLiterals().size(); i++) {
                    auto lit = clause->getBodyLiterals()[i];

                    // add unnamed vars to each atom nested in arguments of lit
                    lit->apply(M());

                    // add two provenance columns to lit; first is rule num, second is level num
                    if (auto atom = dynamic_cast<Atom*>(lit)) {
                        atom->addArgument(mk<UnnamedVariable>());
                        atom->addArgument(mk<ast::Variable>("@level_num_" + std::to_string(i)));
                        bodyLevels.push_back(new ast::Variable("@level_num_" + std::to_string(i)));
                    }
                }

                // add two provenance columns to head lit
                clause->getHead()->addArgument(mk<NumericConstant>(clauseNum));
                clause->getHead()->addArgument(getNextLevelNumber(bodyLevels));
            }
        }
    }
    return true;
}

bool ProvenanceTransformer::transform(TranslationUnit& translationUnit) {
    return ProvenanceTransformer::transformMaxHeight(translationUnit);
}

}  // namespace souffle::ast::transform
