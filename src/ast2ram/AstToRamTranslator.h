/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file AstToRamTranslator.h
 *
 * Translator from AST into RAM
 *
 ***********************************************************************/

#pragma once

#include "ram/Relation.h"
#include "souffle/RamTypes.h"
#include "souffle/utility/ContainerUtil.h"
#include <cassert>
#include <map>
#include <set>
#include <string>
#include <vector>

namespace souffle {
class SymbolTable;
}

namespace souffle::ast {
class Argument;
class Atom;
class Clause;
class Constant;
class Literal;
class Program;
class QualifiedName;
class Relation;
class SipsMetric;
class TranslationUnit;
}  // namespace souffle::ast

namespace souffle::ast::analysis {
class IOTypeAnalysis;
class AuxiliaryArityAnalysis;
class FunctorAnalysis;
class PolymorphicObjectsAnalysis;
class RecursiveClausesAnalysis;
class TypeEnvironment;
}  // namespace souffle::ast::analysis

namespace souffle::ram {
class Condition;
class Expression;
class Relation;
class Statement;
class TranslationUnit;
class TupleElement;
}  // namespace souffle::ram

namespace souffle::ast2ram {

struct Location;
class ValueIndex;

/**
 * Main class for the AST->RAM translator
 */
class AstToRamTranslator {
public:
    AstToRamTranslator();
    ~AstToRamTranslator();

    const ast::analysis::AuxiliaryArityAnalysis* getAuxArityAnalysis() const {
        return auxArityAnalysis;
    }

    const ast::analysis::FunctorAnalysis* getFunctorAnalysis() const {
        return functorAnalysis;
    }

    const ast::analysis::PolymorphicObjectsAnalysis* getPolymorphicObjectsAnalysis() const {
        return polyAnalysis;
    }

    const ast::SipsMetric* getSipsMetric() const {
        return sips.get();
    }

    /** translates AST to translation unit */
    Own<ram::TranslationUnit> translateUnit(ast::TranslationUnit& tu);

    /** translate an AST argument to a RAM value */
    Own<ram::Expression> translateValue(const ast::Argument* arg, const ValueIndex& index);

    /** a utility to translate atoms to relations */
    std::string translateRelation(const ast::Atom* atom);

    /** translate an AST relation to a RAM relation */
    std::string translateRelation(const ast::Relation* rel, const std::string relationNamePrefix = "");

    /** determine the auxiliary for relations */
    size_t getEvaluationArity(const ast::Atom* atom) const;

    /** create a RAM element access node */
    static Own<ram::TupleElement> makeRamTupleElement(const Location& loc);

    /** translate an AST constraint to a RAM condition */
    Own<ram::Condition> translateConstraint(const ast::Literal* arg, const ValueIndex& index);

    /** translate RAM code for a constant value */
    Own<ram::Expression> translateConstant(ast::Constant const& c);

    const ram::Relation* lookupRelation(const std::string& name) const {
        auto it = ramRels.find(name);
        assert(it != ramRels.end() && "relation not found");
        return (*it).second.get();
    }

private:
    /** AST program */
    const ast::Program* program = nullptr;

    /** Type environment */
    const ast::analysis::TypeEnvironment* typeEnv = nullptr;

    /** IO Type */
    const ast::analysis::IOTypeAnalysis* ioType = nullptr;

    /** Functors' analysis */
    const ast::analysis::FunctorAnalysis* functorAnalysis = nullptr;

    /** Auxiliary Arity Analysis */
    const ast::analysis::AuxiliaryArityAnalysis* auxArityAnalysis = nullptr;

    /** Polymorphic Objects Analysis */
    const ast::analysis::PolymorphicObjectsAnalysis* polyAnalysis = nullptr;

    /** SIPS metric for reordering */
    Own<ast::SipsMetric> sips;

    /** RAM program */
    Own<ram::Statement> ramMain;

    /** Subroutines */
    std::map<std::string, Own<ram::Statement>> ramSubs;

    /** RAM relations */
    std::map<std::string, Own<ram::Relation>> ramRels;

    /** translate AST to RAM Program */
    void translateProgram(const ast::TranslationUnit& translationUnit);

    /** replace ADTs with special records */
    static bool removeADTs(const ast::TranslationUnit& translationUnit);

    /**
     * assigns names to unnamed variables such that enclosing
     * constructs may be cloned without losing the variable-identity
     */
    void nameUnnamedVariables(ast::Clause* clause);

    /** converts the given relation identifier into a relation name */
    static std::string getRelationName(const ast::QualifiedName& id);

    // TODO (b-scholz): revisit / refactor so that only one directive is translated
    std::vector<std::map<std::string, std::string>> getInputDirectives(const ast::Relation* rel);

    // TODO (b-scholz): revisit / refactor so that only one directive is translated
    std::vector<std::map<std::string, std::string>> getOutputDirectives(const ast::Relation* rel);

    /** translate a temporary `delta` relation to a RAM relation for semi-naive evaluation */
    std::string translateDeltaRelation(const ast::Relation* rel);

    /** translate a temporary `new` relation to a RAM relation for semi-naive evaluation */
    std::string translateNewRelation(const ast::Relation* rel);

    /** Return a symbol table **/
    SymbolTable& getSymbolTable();

    /** Get ram representation of constant */
    RamDomain getConstantRamRepresentation(const ast::Constant& constant);

    /**
     * translate RAM code for the non-recursive clauses of the given relation.
     *
     * @return a corresponding statement or null if there are no non-recursive clauses.
     */
    Own<ram::Statement> translateNonRecursiveRelation(
            const ast::Relation& rel, const ast::analysis::RecursiveClausesAnalysis* recursiveClauses);

    /** translate RAM code for recursive relations in a strongly-connected component */
    Own<ram::Statement> translateRecursiveRelation(const std::set<const ast::Relation*>& scc,
            const ast::analysis::RecursiveClausesAnalysis* recursiveClauses);

    /** translate RAM code for subroutine to get subproofs */
    Own<ram::Statement> makeSubproofSubroutine(const ast::Clause& clause);

    /** translate RAM code for subroutine to get subproofs for non-existence of a tuple */
    Own<ram::Statement> makeNegationSubproofSubroutine(const ast::Clause& clause);
};

}  // namespace souffle::ast2ram
