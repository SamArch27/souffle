/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Program.h
 *
 * Defines the program class
 *
 * TODO(b-scholz): Remove ast/Utils.h dependency!
 *
 ***********************************************************************/

#pragma once

#include "Clause.h"
#include "Component.h"
#include "ComponentInit.h"
#include "FunctorDeclaration.h"
#include "IO.h"
#include "Node.h"
#include "NodeMapper.h"
#include "Pragma.h"
#include "QualifiedName.h"
#include "Relation.h"
#include "Type.h"
#include "Utils.h"
#include "utility/ContainerUtil.h"
#include "utility/StreamUtil.h"
#include <algorithm>
#include <cassert>
#include <iosfwd>
#include <memory>
#include <ostream>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class AstProgram
 * @brief The program class consists of relations, clauses and types.
 */
class AstProgram : public AstNode {
public:
    /** Return types */
    std::vector<AstType*> getTypes() const {
        return toPtrVector(types);
    }

    /** Return relations */
    std::vector<AstRelation*> getRelations() const {
        return toPtrVector(relations);
    }

    /** Return clauses */
    std::vector<AstClause*> getClauses() const {
        return toPtrVector(clauses);
    }

    /** Return functor declarations */
    std::vector<AstFunctorDeclaration*> getFunctorDeclarations() const {
        return toPtrVector(functors);
    }

    /** Retrun I/O directives */
    std::vector<AstIO*> getIOs() const {
        return toPtrVector(ios);
    }

    /** Add I/O directive */
    void addIO(Own<AstIO> directive) {
        assert(directive && "NULL IO directive");
        ios.push_back(std::move(directive));
    }

    /** Return pragma directives */
    const VecOwn<AstPragma>& getPragmaDirectives() const {
        return pragmaDirectives;
    }

    /* Add relation */
    void addRelation(Own<AstRelation> r) {
        assert(getRelation(*this, r->getQualifiedName()) == nullptr && "Redefinition of relation!");
        relations.push_back(std::move(r));
    }

    /** Remove relation */
    bool removeRelation(const AstQualifiedName& name) {
        for (auto it = relations.begin(); it != relations.end(); it++) {
            const auto& rel = *it;
            if (rel->getQualifiedName() == name) {
                removeRelationClauses(*this, name);
                removeRelationIOs(*this, name);
                relations.erase(it);
                return true;
            }
        }
        return false;
    }

    /** Set clauses */
    void setClauses(VecOwn<AstClause> newClauses) {
        clauses = std::move(newClauses);
    }

    /** Add a clause */
    void addClause(Own<AstClause> clause) {
        assert(clause != nullptr && "Undefined clause");
        assert(clause->getHead() != nullptr && "Undefined head of the clause");
        clauses.push_back(std::move(clause));
    }

    /** Remove a clause */
    bool removeClause(const AstClause* clause) {
        for (auto it = clauses.begin(); it != clauses.end(); it++) {
            if (**it == *clause) {
                clauses.erase(it);
                return true;
            }
        }
        return false;
    }

    /** Remove an I/O directive */
    bool removeIO(const AstIO* io) {
        for (auto it = ios.begin(); it != ios.end(); it++) {
            if (**it == *io) {
                ios.erase(it);
                return true;
            }
        }
        return false;
    }

    /** Return components */
    std::vector<AstComponent*> getComponents() const {
        return toPtrVector(components);
    }

    /** Return component instantiation */
    std::vector<AstComponentInit*> getComponentInstantiations() const {
        return toPtrVector(instantiations);
    }

    AstProgram* clone() const override {
        auto res = new AstProgram();
        res->pragmaDirectives = souffle::clone(pragmaDirectives);
        res->components = souffle::clone(components);
        res->instantiations = souffle::clone(instantiations);
        res->types = souffle::clone(types);
        res->functors = souffle::clone(functors);
        res->relations = souffle::clone(relations);
        res->clauses = souffle::clone(clauses);
        res->ios = souffle::clone(ios);
        return res;
    }

    void apply(const AstNodeMapper& map) override {
        for (auto& cur : pragmaDirectives) {
            cur = map(std::move(cur));
        }
        for (auto& cur : components) {
            cur = map(std::move(cur));
        }
        for (auto& cur : instantiations) {
            cur = map(std::move(cur));
        }
        for (auto& cur : functors) {
            cur = map(std::move(cur));
        }
        for (auto& cur : types) {
            cur = map(std::move(cur));
        }
        for (auto& cur : relations) {
            cur = map(std::move(cur));
        }
        for (auto& cur : clauses) {
            cur = map(std::move(cur));
        }
        for (auto& cur : ios) {
            cur = map(std::move(cur));
        }
    }

    std::vector<const AstNode*> getChildNodes() const override {
        std::vector<const AstNode*> res;
        for (const auto& cur : pragmaDirectives) {
            res.push_back(cur.get());
        }
        for (const auto& cur : components) {
            res.push_back(cur.get());
        }
        for (const auto& cur : instantiations) {
            res.push_back(cur.get());
        }
        for (const auto& cur : functors) {
            res.push_back(cur.get());
        }
        for (const auto& cur : types) {
            res.push_back(cur.get());
        }
        for (const auto& cur : relations) {
            res.push_back(cur.get());
        }
        for (const auto& cur : clauses) {
            res.push_back(cur.get());
        }
        for (const auto& cur : ios) {
            res.push_back(cur.get());
        }
        return res;
    }

protected:
    void print(std::ostream& os) const override {
        auto show = [&](auto&& xs, char const* sep = "\n") {
            if (!xs.empty()) os << join(xs, sep) << "\n";
        };

        show(pragmaDirectives, "\n\n");
        show(components);
        show(instantiations);
        show(types);
        show(functors);
        show(relations);
        show(clauses, "\n\n");
        show(ios, "\n\n");
    }

    bool equal(const AstNode& node) const override {
        const auto& other = static_cast<const AstProgram&>(node);
        if (!equal_targets(pragmaDirectives, other.pragmaDirectives)) {
            return false;
        }
        if (!equal_targets(components, other.components)) {
            return false;
        }
        if (!equal_targets(instantiations, other.instantiations)) {
            return false;
        }
        if (!equal_targets(functors, other.functors)) {
            return false;
        }
        if (!equal_targets(types, other.types)) {
            return false;
        }
        if (!equal_targets(relations, other.relations)) {
            return false;
        }
        if (!equal_targets(clauses, other.clauses)) {
            return false;
        }
        if (!equal_targets(ios, other.ios)) {
            return false;
        }
        return true;
    }

protected:
    friend class ComponentInstantiationTransformer;
    friend class ParserDriver;

    /* Add type */
    void addType(Own<AstType> type) {
        assert(getType(*this, type->getQualifiedName()) == nullptr && "Redefinition of type!");
        types.push_back(std::move(type));
    }

    /** Add a pragma */
    void addPragma(Own<AstPragma> pragma) {
        assert(pragma && "NULL IO directive");
        pragmaDirectives.push_back(std::move(pragma));
    }

    /** Add functor */
    void addFunctorDeclaration(Own<souffle::AstFunctorDeclaration> f) {
        assert(getFunctorDeclaration(*this, f->getName()) == nullptr && "Redefinition of functor!");
        functors.push_back(std::move(f));
    }

    /** Add component */
    void addComponent(Own<AstComponent> c) {
        components.push_back(std::move(c));
    }

    /** Add component instantiation */
    void addInstantiation(Own<AstComponentInit> i) {
        instantiations.push_back(std::move(i));
    }

    /** Program types  */
    VecOwn<AstType> types;

    /** Program relations */
    VecOwn<AstRelation> relations;

    /** External Functors */
    VecOwn<AstFunctorDeclaration> functors;

    /** Program clauses */
    VecOwn<AstClause> clauses;

    /** I/O directives */
    VecOwn<AstIO> ios;

    /** Component definitions */
    VecOwn<AstComponent> components;

    /** Component instantiations */
    VecOwn<AstComponentInit> instantiations;

    /** Pragmas */
    VecOwn<AstPragma> pragmaDirectives;
};

}  // namespace souffle
