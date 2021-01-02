/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Relation.h
 *
 * Defines the relation class and helper its classes
 *
 ***********************************************************************/

#pragma once

#include "RelationTag.h"
#include "ast/Attribute.h"
#include "ast/FunctionalConstraint.h"
#include "ast/Node.h"
#include "ast/QualifiedName.h"
#include "ast/utility/NodeMapper.h"
#include "parser/SrcLocation.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <algorithm>
#include <cassert>
#include <cstddef>
#include <memory>
#include <ostream>
#include <set>
#include <string>
#include <utility>
#include <vector>

namespace souffle::ast {

/**
 * @class Relation
 * @brief Defines a relation with a name, attributes, qualifiers, and internal representation.
 */
class Relation : public Node {
public:
    Relation() = default;
    Relation(QualifiedName name, SrcLocation loc = {}) : name(std::move(name)) {
        setSrcLoc(std::move(loc));
    }

    /** Get qualified relation name */
    const QualifiedName& getQualifiedName() const {
        return name;
    }

    /** Set name for this relation */
    void setQualifiedName(QualifiedName n) {
        name = std::move(n);
    }

    /** Add a new used type to this relation */
    void addAttribute(Own<Attribute> attr) {
        assert(attr && "Undefined attribute");
        attributes.push_back(std::move(attr));
    }

    /** Return the arity of this relation */
    size_t getArity() const {
        return attributes.size();
    }

    /** Set relation attributes */
    void setAttributes(VecOwn<Attribute> attrs) {
        attributes = std::move(attrs);
    }

    /** Get relation attributes */
    std::vector<Attribute*> getAttributes() const {
        return toPtrVector(attributes);
    }

    /** Get relation qualifiers */
    const std::set<RelationQualifier>& getQualifiers() const {
        return qualifiers;
    }

    /** Add qualifier to this relation */
    void addQualifier(RelationQualifier q) {
        qualifiers.insert(q);
    }

    /** Remove qualifier from this relation */
    void removeQualifier(RelationQualifier q) {
        qualifiers.erase(q);
    }

    /** Get relation representation */
    RelationRepresentation getRepresentation() const {
        return representation;
    }

    /** Set relation representation */
    void setRepresentation(RelationRepresentation representation) {
        this->representation = representation;
    }

    /** Check for a relation qualifier */
    bool hasQualifier(RelationQualifier q) const {
        return qualifiers.find(q) != qualifiers.end();
    }

    /** Add functional dependency to this relation */
    void addDependency(Own<FunctionalConstraint> fd) {
        functionalDependencies.push_back(std::move(fd));
    }

    std::vector<FunctionalConstraint*> getFunctionalDependencies() const {
        return toPtrVector(functionalDependencies);
    }

    Relation* clone() const override {
        auto res = new Relation(name, getSrcLoc());
        res->attributes = souffle::clone(attributes);
        res->qualifiers = qualifiers;
        res->representation = representation;
        return res;
    }

    void apply(const NodeMapper& map) override {
        for (auto& cur : attributes) {
            cur = map(std::move(cur));
        }
    }

    std::vector<const Node*> getChildNodes() const override {
        std::vector<const Node*> res;
        for (const auto& cur : attributes) {
            res.push_back(cur.get());
        }
        return res;
    }

protected:
    void print(std::ostream& os) const override {
        os << ".decl " << getQualifiedName() << "(" << join(attributes, ", ") << ")" << join(qualifiers, " ")
           << " " << representation;
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const Relation&>(node);
        return name == other.name && equal_targets(attributes, other.attributes);
    }

    /** Name of relation */
    QualifiedName name;

    /** Attributes of the relation */
    VecOwn<Attribute> attributes;

    /** Qualifiers of relation */
    std::set<RelationQualifier> qualifiers;

    /** Functional dependencies of the relation */
    VecOwn<FunctionalConstraint> functionalDependencies;

    /** Datastructure to use for this relation */
    RelationRepresentation representation{RelationRepresentation::DEFAULT};
};

/**
 * @class NameComparison
 * @brief Comparator for relations
 *
 * Lexicographical order for Relation
 * using the qualified name as an ordering criteria.
 */
struct NameComparison {
    bool operator()(const Relation* x, const Relation* y) const {
        if (x != nullptr && y != nullptr) {
            return x->getQualifiedName() < y->getQualifiedName();
        }
        return y != nullptr;
    }
};

/** Relation set */
using RelationSet = std::set<const Relation*, NameComparison>;

}  // namespace souffle::ast
