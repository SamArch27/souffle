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

#include "ast/Argument.h"
#include "ast/Atom.h"
#include "ast/Clause.h"
#include "ast/Constant.h"
#include "ast/Literal.h"
#include "ast/NilConstant.h"
#include "ast/Node.h"
#include "ast/NumericConstant.h"
#include "ast/Program.h"
#include "ast/QualifiedName.h"
#include "ast/RecordInit.h"
#include "ast/Relation.h"
#include "ast/StringConstant.h"
#include "ast/TranslationUnit.h"
#include "ast/Variable.h"
#include "ast/analysis/AuxArity.h"
#include "ast/analysis/IOType.h"
#include "ast/analysis/RecursiveClauses.h"
#include "ast/analysis/TypeSystem.h"
#include "ast/utility/SipsMetric.h"
#include "ram/Condition.h"
#include "ram/Expression.h"
#include "ram/Operation.h"
#include "ram/Statement.h"
#include "ram/TranslationUnit.h"
#include "ram/TupleElement.h"
#include "souffle/RamTypes.h"
#include "souffle/SymbolTable.h"
#include "souffle/utility/FunctionalUtil.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StreamUtil.h"
#include "souffle/utility/StringUtil.h"
#include <cassert>
#include <cstddef>
#include <map>
#include <memory>
#include <optional>
#include <ostream>
#include <set>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * Main class for AST Translator
 */
class AstToRamTranslator {
public:
    AstToRamTranslator() = default;

    /** translates AST to translation unit  */
    Own<ram::TranslationUnit> translateUnit(ast::TranslationUnit& tu);

private:
    /** AST program */
    const ast::Program* program = nullptr;

    /** Type environment */
    const ast::analysis::TypeEnvironment* typeEnv = nullptr;

    /** IO Type */
    const ast::analysis::IOTypeAnalysis* ioType = nullptr;

    /** RAM program */
    Own<ram::Statement> ramMain;

    /** Subroutines */
    std::map<std::string, Own<ram::Statement>> ramSubs;

    /** RAM relations */
    std::map<std::string, Own<ram::Relation>> ramRels;

    /** Symbol Table **/
    SymbolTable symbolTable;

    /** Auxiliary Arity Analysis */
    const ast::analysis::AuxiliaryArityAnalysis* auxArityAnalysis = nullptr;

    /** SIPS metric for reordering */
    Own<ast::SipsMetric> sips;

    /**
     * Concrete attribute
     */
    struct Location {
        int identifier{};
        int element{};
        Own<ram::RelationReference> relation{nullptr};

        Location() = default;

        Location(int ident, int elem, Own<ram::RelationReference> rel = nullptr)
                : identifier(ident), element(elem), relation(std::move(rel)) {}

        Location(const Location& l) : identifier(l.identifier), element(l.element) {
            if (l.relation != nullptr) {
                relation = souffle::clone(l.relation);
            }
        }

        Location& operator=(Location other) {
            identifier = other.identifier;
            element = other.element;
            relation = std::move(other.relation);
            return *this;
        }

        bool operator==(const Location& loc) const {
            return identifier == loc.identifier && element == loc.element;
        }

        bool operator!=(const Location& loc) const {
            return !(*this == loc);
        }

        bool operator<(const Location& loc) const {
            return identifier < loc.identifier || (identifier == loc.identifier && element < loc.element);
        }

        void print(std::ostream& out) const {
            out << "(" << identifier << "," << element << ")";
        }

        friend std::ostream& operator<<(std::ostream& out, const Location& loc) {
            loc.print(out);
            return out;
        }
    };

    /**
     * A class indexing the location of variables and record
     * references within a loop nest resulting from the conversion
     * of a rule.
     */
    class ValueIndex {
        /**
         * The type mapping variables (referenced by their names) to the
         * locations where they are used.
         */
        using variable_reference_map = std::map<std::string, std::set<Location>>;

        /**
         * The type mapping record init expressions to their definition points,
         * hence the point where they get grounded/bound.
         */
        using record_definition_map = std::map<const ast::RecordInit*, Location>;

        /**
         * A map from generative `ast::Argument`s to storage locations. Note,
         * since in this case ast::Argument are indexed by their values (not their
         * address) no standard map can be utilized.
         * (By-value indexing induces an ad-hoc form of CSE.)
         */
        using generator_location_map = std::vector<std::pair<const ast::Argument*, Location>>;

        /** The index of variable accesses */
        variable_reference_map var_references;

        /** The index of record definition points */
        record_definition_map record_definitions;

        /** The level of a nested ram operation that is handling a generator operation */
        generator_location_map arg_generator_locations;

    public:
        // -- variables --

        void addVarReference(const ast::Variable& var, const Location& l) {
            std::set<Location>& locs = var_references[var.getName()];
            locs.insert(l);
        }

        void addVarReference(
                const ast::Variable& var, int ident, int pos, Own<ram::RelationReference> rel = nullptr) {
            addVarReference(var, Location({ident, pos, std::move(rel)}));
        }

        bool isDefined(const ast::Variable& var) const {
            return var_references.find(var.getName()) != var_references.end();
        }

        const Location& getDefinitionPoint(const ast::Variable& var) const {
            auto pos = var_references.find(var.getName());
            assert(pos != var_references.end() && "Undefined variable referenced!");
            return *pos->second.begin();
        }

        const variable_reference_map& getVariableReferences() const {
            return var_references;
        }

        // -- records --

        // - definition -

        void setRecordDefinition(const ast::RecordInit& init, const Location& l) {
            record_definitions[&init] = l;
        }

        void setRecordDefinition(
                const ast::RecordInit& init, int ident, int pos, Own<ram::RelationReference> rel = nullptr) {
            setRecordDefinition(init, Location({ident, pos, std::move(rel)}));
        }

        const Location& getDefinitionPoint(const ast::RecordInit& init) const {
            auto pos = record_definitions.find(&init);
            if (pos != record_definitions.end()) {
                return pos->second;
            }

            fatal("requested location for undefined record!");
        }

        // -- generators (aggregates & some functors) --

        void setGeneratorLoc(const ast::Argument& agg, const Location& loc) {
            arg_generator_locations.push_back(std::make_pair(&agg, loc));
        }

        const Location& getGeneratorLoc(const ast::Argument& arg) const {
            // search list
            for (const auto& cur : arg_generator_locations) {
                if (*cur.first == arg) {
                    return cur.second;
                }
            }

            fatal("arg `%s` has no generator location", arg);
        }

        // -- others --

        bool isGenerator(const int level) const {
            // check for aggregator definitions
            return any_of(arg_generator_locations,
                    [&level](const auto& location) { return location.second.identifier == level; });
        }

        bool isSomethingDefinedOn(int level) const {
            // check for variable definitions
            for (const auto& cur : var_references) {
                if (cur.second.begin()->identifier == level) {
                    return true;
                }
            }
            // check for record definitions
            for (const auto& cur : record_definitions) {
                if (cur.second.identifier == level) {
                    return true;
                }
            }
            // nothing defined on this level
            return false;
        }

        void print(std::ostream& out) const {
            out << "Variables:\n\t";
            out << join(var_references, "\n\t");
        }

        friend std::ostream& operator<<(std::ostream& out, const ValueIndex& index) __attribute__((unused)) {
            index.print(out);
            return out;
        }
    };

    /** create a RAM element access node */
    static Own<ram::TupleElement> makeRamTupleElement(const Location& loc);

    /** determine the auxiliary for relations */
    size_t getEvaluationArity(const ast::Atom* atom) const;

    /**
     * assigns names to unnamed variables such that enclosing
     * constructs may be cloned without losing the variable-identity
     */
    void nameUnnamedVariables(ast::Clause* clause);

    /** converts the given relation identifier into a relation name */
    std::string getRelationName(const ast::QualifiedName& id) {
        return toString(join(id.getQualifiers(), "."));
    }

    /** translate AST directives to RAM directives */
    // TODO (b-scholz): revisit / refactor
    void translateDirectives(std::map<std::string, std::string>& directives, const ast::Relation* rel);

    // TODO (b-scholz): revisit / refactor so that only one directive is translated
    std::vector<std::map<std::string, std::string>> getInputDirectives(const ast::Relation* rel);

    // TODO (b-scholz): revisit / refactor so that only one directive is translated
    std::vector<std::map<std::string, std::string>> getOutputDirectives(const ast::Relation* rel);

    /** create a reference to a RAM relation */
    Own<ram::RelationReference> createRelationReference(const std::string name);

    /** a utility to translate atoms to relations */
    Own<ram::RelationReference> translateRelation(const ast::Atom* atom);

    /** translate an AST relation to a RAM relation */
    Own<ram::RelationReference> translateRelation(
            const ast::Relation* rel, const std::string relationNamePrefix = "");

    /** translate a temporary `delta` relation to a RAM relation for semi-naive evaluation */
    Own<ram::RelationReference> translateDeltaRelation(const ast::Relation* rel);

    /** translate a temporary `new` relation to a RAM relation for semi-naive evaluation */
    Own<ram::RelationReference> translateNewRelation(const ast::Relation* rel);

    /** translate an AST argument to a RAM value */
    Own<ram::Expression> translateValue(const ast::Argument* arg, const ValueIndex& index);

    /** translate an AST constraint to a RAM condition */
    Own<ram::Condition> translateConstraint(const ast::Literal* arg, const ValueIndex& index);

    /** translate AST clause to RAM code */
    class ClauseTranslator {
        // index nested variables and records
        using arg_list = std::vector<ast::Argument*>;

        std::vector<const ast::Argument*> generators;

        // the order of processed operations
        std::vector<const ast::Node*> op_nesting;

        Own<ast::Clause> getReorderedClause(const ast::Clause& clause, const int version) const;

        arg_list* getArgList(
                const ast::Node* curNode, std::map<const ast::Node*, Own<arg_list>>& nodeArgs) const;

        void indexValues(const ast::Node* curNode, std::map<const ast::Node*, Own<arg_list>>& nodeArgs,
                std::map<const arg_list*, int>& arg_level, ram::RelationReference* relation);

        void createValueIndex(const ast::Clause& clause);

    protected:
        AstToRamTranslator& translator;

        // create value index
        ValueIndex valueIndex;

        // current nesting level
        int level = 0;

        virtual Own<ram::Operation> createOperation(const ast::Clause& clause);
        virtual Own<ram::Condition> createCondition(const ast::Clause& originalClause);

        /** translate RAM code for a constant value */
        Own<ram::Operation> filterByConstraints(size_t level, const std::vector<ast::Argument*>& args,
                Own<ram::Operation> op, bool constrainByFunctors = true);

        const ast::analysis::AuxiliaryArityAnalysis* auxArityAnalysis;

    public:
        ClauseTranslator(AstToRamTranslator& translator)
                : translator(translator), auxArityAnalysis(translator.auxArityAnalysis) {}

        Own<ram::Statement> translateClause(
                const ast::Clause& clause, const ast::Clause& originalClause, const int version = 0);
    };

    class ProvenanceClauseTranslator : public ClauseTranslator {
    protected:
        Own<ram::Operation> createOperation(const ast::Clause& clause) override;
        Own<ram::Condition> createCondition(const ast::Clause& originalClause) override;

    public:
        ProvenanceClauseTranslator(AstToRamTranslator& translator) : ClauseTranslator(translator) {}
    };

    /** Return a symbol table **/
    SymbolTable& getSymbolTable() {
        return symbolTable;
    }

    /**
     *  Get ram representation of constant.
     */
    RamDomain getConstantRamRepresentation(const ast::Constant& constant) {
        if (auto strConstant = dynamic_cast<const ast::StringConstant*>(&constant)) {
            return getSymbolTable().lookup(strConstant->getConstant());
        } else if (isA<ast::NilConstant>(&constant)) {
            return 0;
        } else if (auto* numConstant = dynamic_cast<const ast::NumericConstant*>(&constant)) {
            assert(numConstant->getType().has_value());
            switch (*numConstant->getType()) {
                case ast::NumericConstant::Type::Int:
                    return RamSignedFromString(numConstant->getConstant(), nullptr, 0);
                case ast::NumericConstant::Type::Uint:
                    return RamUnsignedFromString(numConstant->getConstant(), nullptr, 0);
                case ast::NumericConstant::Type::Float: return RamFloatFromString(numConstant->getConstant());
            }
        }

        fatal("unaccounted-for constant");
    }

    /** translate RAM code for a constant value */
    Own<ram::Expression> translateConstant(ast::Constant const& c);

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

    /** translate RAM code for subroutine to get subproofs */
    Own<ram::Statement> makeSubproofSubroutineOpt(const ast::Clause& clause);

    /** translate RAM code for subroutine to get subproofs for non-existence of a tuple */
    Own<ram::Statement> makeNegationSubproofSubroutine(const ast::Clause& clause);

    /** translate AST to RAM Program */
    void translateProgram(const ast::TranslationUnit& translationUnit);
};

}  // end of namespace souffle
