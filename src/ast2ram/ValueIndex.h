/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ValueIndex.h
 *
 * Defines the ValueIndex class, which indexes the location of variables
 * and record references within a loop nest during rule conversion.
 *
 ***********************************************************************/

#pragma once

#include "souffle/utility/ContainerUtil.h"
#include <map>
#include <set>
#include <string>
#include <vector>

namespace souffle::ast {
class Argument;
class RecordInit;
class Variable;
}  // namespace souffle::ast

namespace souffle::ast2ram {

struct Location;

class ValueIndex {
public:
    ValueIndex();
    ~ValueIndex();

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

    // -- variables --

    const variable_reference_map& getVariableReferences() const {
        return var_references;
    }

    void addVarReference(const ast::Variable& var, const Location& l);

    void addVarReference(const ast::Variable& var, int ident, int pos, std::string rel = "");

    bool isDefined(const ast::Variable& var) const;

    const Location& getDefinitionPoint(const ast::Variable& var) const;

    // -- records --

    // - definition -

    void setRecordDefinition(const ast::RecordInit& init, const Location& l);

    void setRecordDefinition(const ast::RecordInit& init, int ident, int pos, std::string rel = "");

    const Location& getDefinitionPoint(const ast::RecordInit& init) const;

    // -- generators (aggregates & some functors) --
    void setGeneratorLoc(const ast::Argument& arg, const Location& loc);

    const Location& getGeneratorLoc(const ast::Argument& arg) const;

    // -- others --

    bool isGenerator(const int level) const;

    bool isSomethingDefinedOn(int level) const;

    void print(std::ostream& out) const;

private:
    /** The index of variable accesses */
    variable_reference_map var_references;

    /** The index of record definition points */
    record_definition_map record_definitions;

    /** The level of a nested ram operation that is handling a generator operation */
    generator_location_map arg_generator_locations;
};

}  // namespace souffle::ast2ram
