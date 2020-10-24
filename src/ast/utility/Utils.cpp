/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Utils.cpp
 *
 * A collection of utilities operating on AST constructs.
 *
 ***********************************************************************/

#include "ast/utility/Utils.h"
#include "ast/Aggregator.h"
#include "ast/Argument.h"
#include "ast/Atom.h"
#include "ast/BinaryConstraint.h"
#include "ast/BooleanConstraint.h"
#include "ast/Clause.h"
#include "ast/Constraint.h"
#include "ast/Directive.h"
#include "ast/ExecutionPlan.h"
#include "ast/IntrinsicFunctor.h"
#include "ast/Literal.h"
#include "ast/Negation.h"
#include "ast/Node.h"
#include "ast/Program.h"
#include "ast/QualifiedName.h"
#include "ast/Relation.h"
#include "ast/TranslationUnit.h"
#include "ast/analysis/Functor.h"
#include "ast/analysis/RelationDetailCache.h"
#include "ast/analysis/Type.h"
#include "ast/analysis/TypeSystem.h"
#include "ast/utility/NodeMapper.h"
#include "ast/utility/Visitor.h"
#include "souffle/BinaryConstraintOps.h"
#include "souffle/TypeAttribute.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/FunctionalUtil.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StringUtil.h"
#include <algorithm>
#include <cassert>
#include <memory>

namespace souffle::ast {

std::string pprint(const Node& node) {
    return toString(node);
}

std::vector<const Variable*> getVariables(const Node& root) {
    // simply collect the list of all variables by visiting all variables
    std::vector<const Variable*> vars;
    visitDepthFirst(root, [&](const Variable& var) { vars.push_back(&var); });
    return vars;
}

std::vector<const RecordInit*> getRecords(const Node& root) {
    // simply collect the list of all records by visiting all records
    std::vector<const RecordInit*> recs;
    visitDepthFirst(root, [&](const RecordInit& rec) { recs.push_back(&rec); });
    return recs;
}

std::vector<Clause*> getClauses(const Program& program, const QualifiedName& relationName) {
    std::vector<Clause*> clauses;
    for (Clause* clause : program.getClauses()) {
        if (clause->getHead()->getQualifiedName() == relationName) {
            clauses.push_back(clause);
        }
    }
    return clauses;
}

std::vector<Clause*> getClauses(const Program& program, const Relation& rel) {
    return getClauses(program, rel.getQualifiedName());
}

std::vector<Directive*> getDirectives(const Program& program, const QualifiedName& relationName) {
    std::vector<Directive*> directives;
    for (Directive* dir : program.getDirectives()) {
        if (dir->getQualifiedName() == relationName) {
            directives.push_back(dir);
        }
    }
    return directives;
}

Relation* getRelation(const Program& program, const QualifiedName& name) {
    return getIf(program.getRelations(), [&](const Relation* r) { return r->getQualifiedName() == name; });
}

void removeRelation(TranslationUnit& tu, const QualifiedName& name) {
    Program& program = tu.getProgram();
    if (getRelation(program, name) != nullptr) {
        removeRelationClauses(tu, name);
        removeRelationIOs(tu, name);
        program.removeRelationDecl(name);
    }
}

void removeRelationClauses(TranslationUnit& tu, const QualifiedName& name) {
    Program& program = tu.getProgram();
    const auto& relDetail = *tu.getAnalysis<analysis::RelationDetailCacheAnalysis>();
    for (const auto* clause : relDetail.getClauses(name)) {
        program.removeClause(clause);
    }
}

void removeRelationIOs(TranslationUnit& tu, const QualifiedName& name) {
    Program& program = tu.getProgram();
    for (const auto* directive : getDirectives(program, name)) {
        program.removeDirective(directive);
    }
}

const Relation* getAtomRelation(const Atom* atom, const Program* program) {
    return getRelation(*program, atom->getQualifiedName());
}

const Relation* getHeadRelation(const Clause* clause, const Program* program) {
    return getAtomRelation(clause->getHead(), program);
}

std::set<const Relation*> getBodyRelations(const Clause* clause, const Program* program) {
    std::set<const Relation*> bodyRelations;
    for (const auto& lit : clause->getBodyLiterals()) {
        visitDepthFirst(
                *lit, [&](const Atom& atom) { bodyRelations.insert(getAtomRelation(&atom, program)); });
    }
    for (const auto& arg : clause->getHead()->getArguments()) {
        visitDepthFirst(
                *arg, [&](const Atom& atom) { bodyRelations.insert(getAtomRelation(&atom, program)); });
    }
    return bodyRelations;
}

size_t getClauseNum(const Program* program, const Clause* clause) {
    // TODO (azreika): This number might change between the provenance transformer and the AST->RAM
    // translation. Might need a better way to assign IDs to clauses... (see PR #1288).
    const Relation* rel = getRelation(*program, clause->getHead()->getQualifiedName());
    assert(rel != nullptr && "clause relation does not exist");

    size_t clauseNum = 1;
    for (const auto* cur : getClauses(*program, *rel)) {
        bool isFact = cur->getBodyLiterals().empty();
        if (cur == clause) {
            return isFact ? 0 : clauseNum;
        }

        if (!isFact) {
            clauseNum++;
        }
    }

    fatal("clause does not exist");
}

bool hasClauseWithNegatedRelation(const Relation* relation, const Relation* negRelation,
        const Program* program, const Literal*& foundLiteral) {
    for (const Clause* cl : getClauses(*program, *relation)) {
        for (const auto* neg : getBodyLiterals<Negation>(*cl)) {
            if (negRelation == getAtomRelation(neg->getAtom(), program)) {
                foundLiteral = neg;
                return true;
            }
        }
    }
    return false;
}

bool hasClauseWithAggregatedRelation(const Relation* relation, const Relation* aggRelation,
        const Program* program, const Literal*& foundLiteral) {
    for (const Clause* cl : getClauses(*program, *relation)) {
        bool hasAgg = false;
        visitDepthFirst(*cl, [&](const Aggregator& cur) {
            visitDepthFirst(cur, [&](const Atom& atom) {
                if (aggRelation == getAtomRelation(&atom, program)) {
                    foundLiteral = &atom;
                    hasAgg = true;
                }
            });
        });
        if (hasAgg) {
            return true;
        }
    }
    return false;
}

bool isRecursiveClause(const Clause& clause) {
    QualifiedName relationName = clause.getHead()->getQualifiedName();
    bool recursive = false;
    visitDepthFirst(clause.getBodyLiterals(), [&](const Atom& atom) {
        if (atom.getQualifiedName() == relationName) {
            recursive = true;
        }
    });
    return recursive;
}

bool isFact(const Clause& clause) {
    // there must be a head
    if (clause.getHead() == nullptr) {
        return false;
    }
    // there must not be any body clauses
    if (!clause.getBodyLiterals().empty()) {
        return false;
    }

    // and there are no aggregates
    bool hasAggregatesOrMultiResultFunctor = false;
    visitDepthFirst(*clause.getHead(), [&](const Argument& arg) {
        if (isA<Aggregator>(arg)) {
            hasAggregatesOrMultiResultFunctor = true;
        }

        auto* func = as<IntrinsicFunctor>(arg);
        hasAggregatesOrMultiResultFunctor |=
                (func != nullptr) && analysis::FunctorAnalysis::isMultiResult(*func);
    });
    return !hasAggregatesOrMultiResultFunctor;
}

bool isRule(const Clause& clause) {
    return (clause.getHead() != nullptr) && !isFact(clause);
}

bool isProposition(const Atom* atom) {
    return atom->getArguments().empty();
}

bool isDeltaRelation(const QualifiedName& name) {
    const auto& qualifiers = name.getQualifiers();
    if (qualifiers.empty()) {
        return false;
    }
    return isPrefix("@delta_", qualifiers[0]);
}

Clause* cloneHead(const Clause* clause) {
    auto* clone = new Clause();
    clone->setSrcLoc(clause->getSrcLoc());
    clone->setHead(souffle::clone(clause->getHead()));
    if (clause->getExecutionPlan() != nullptr) {
        clone->setExecutionPlan(souffle::clone(clause->getExecutionPlan()));
    }
    return clone;
}

Clause* reorderAtoms(const Clause* clause, const std::vector<unsigned int>& newOrder) {
    // Find all atom positions
    std::vector<unsigned int> atomPositions;
    std::vector<Literal*> bodyLiterals = clause->getBodyLiterals();
    for (unsigned int i = 0; i < bodyLiterals.size(); i++) {
        if (isA<Atom>(bodyLiterals[i])) {
            atomPositions.push_back(i);
        }
    }

    // Validate given order
    assert(newOrder.size() == atomPositions.size());
    std::vector<unsigned int> nopOrder;
    for (unsigned int i = 0; i < atomPositions.size(); i++) {
        nopOrder.push_back(i);
    }
    assert(std::is_permutation(nopOrder.begin(), nopOrder.end(), newOrder.begin()));

    // Create a new clause with the given atom order, leaving the rest unchanged
    Clause* newClause = cloneHead(clause);
    unsigned int currentAtom = 0;
    for (unsigned int currentLiteral = 0; currentLiteral < bodyLiterals.size(); currentLiteral++) {
        Literal* literalToAdd = bodyLiterals[currentLiteral];
        if (isA<Atom>(literalToAdd)) {
            // Atoms should be reordered
            literalToAdd = bodyLiterals[atomPositions[newOrder[currentAtom++]]];
        }
        newClause->addToBody(souffle::clone(literalToAdd));
    }

    return newClause;
}

void negateConstraintInPlace(Constraint& constraint) {
    if (auto* bcstr = dynamic_cast<BooleanConstraint*>(&constraint)) {
        bcstr->set(!bcstr->isTrue());
    } else if (auto* cstr = dynamic_cast<BinaryConstraint*>(&constraint)) {
        cstr->setOperator(souffle::negatedConstraintOp(cstr->getOperator()));
    } else {
        fatal("Unknown ast-constraint type");
    }
}

IntrinsicFunctors validOverloads(const analysis::TypeAnalysis& typing, const ast::IntrinsicFunctor& func) {
    auto typeAttrs = [&](const Argument* arg) -> std::set<TypeAttribute> {
        auto&& types = typing.getTypes(arg);
        if (types.isAll())
            return {TypeAttribute::Signed, TypeAttribute::Unsigned, TypeAttribute::Float,
                    TypeAttribute::Symbol, TypeAttribute::Record};

        std::set<TypeAttribute> tyAttrs;
        for (auto&& ty : types)
            tyAttrs.insert(getTypeAttribute(ty));
        return tyAttrs;
    };
    auto retTys = typeAttrs(&func);
    auto argTys = map(func.getArguments(), typeAttrs);

    auto candidates =
            filterNot(functorBuiltIn(func.getFunction()), [&](const IntrinsicFunctorInfo& x) -> bool {
                if (!x.variadic && argTys.size() != x.params.size()) return true;  // arity mismatch?

                for (size_t i = 0; i < argTys.size(); ++i)
                    if (!contains(argTys[i], x.params[x.variadic ? 0 : i])) return true;

                return !contains(retTys, x.result);
            });

    std::sort(candidates.begin(), candidates.end(),
            [&](const IntrinsicFunctorInfo& a, const IntrinsicFunctorInfo& b) {
                if (a.result != b.result) return a.result < b.result;
                if (a.variadic != b.variadic) return a.variadic < b.variadic;
                return std::lexicographical_compare(
                        a.params.begin(), a.params.end(), b.params.begin(), b.params.end());
            });
    return candidates;
}

bool renameAtoms(Node& node, const std::map<QualifiedName, QualifiedName>& oldToNew) {
    struct rename_atoms : public NodeMapper {
        mutable bool changed{false};
        const std::map<QualifiedName, QualifiedName>& oldToNew;
        rename_atoms(const std::map<QualifiedName, QualifiedName>& oldToNew) : oldToNew(oldToNew) {}
        Own<Node> operator()(Own<Node> node) const override {
            node->apply(*this);
            if (auto* atom = dynamic_cast<Atom*>(node.get())) {
                if (contains(oldToNew, atom->getQualifiedName())) {
                    auto renamedAtom = souffle::clone(atom);
                    renamedAtom->setQualifiedName(oldToNew.at(atom->getQualifiedName()));
                    changed = true;
                    return renamedAtom;
                }
            }
            return node;
        }
    };
    rename_atoms update(oldToNew);
    node.apply(update);
    return update.changed;
}

}  // namespace souffle::ast
