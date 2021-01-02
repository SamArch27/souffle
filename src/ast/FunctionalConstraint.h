/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file FunctionalConstraint.h
 *
 * Defines the functional constraint class
 *
 ***********************************************************************/

#pragma once

#include "ast/Argument.h"
#include "ast/Constraint.h"
#include "ast/Node.h"
#include "ast/Variable.h"
#include "ast/utility/NodeMapper.h"
#include "parser/SrcLocation.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <cassert>
#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace souffle::ast {

/**
 * @class FunctionalConstraint
 * @brief Functional constraint (choice construct) class
 *
 * Representing a functional dependency
 * Example:
 * .decl rel(x:symbol, y:symbol, z:number) keys x
 * The functional constraint "x" makes sure every x in the rel uniquely defines an element.
 *
 * .decl rel(x:symbol, y:symbol, z:number) keys x, y
 * A relation can have more then one key, each key uniquely defines an element in the relation.
 *
 * .decl rel(x:symbol, y:symbol, z:number) keys (x, y)
 * Multiple attributes can serve as a single key, the pair (x,y) uniquely defines an element in the relation.
 */
class FunctionalConstraint : public Constraint {
public:
    FunctionalConstraint(VecOwn<Variable> keys, SrcLocation loc = {})
            : Constraint(std::move(loc)), keys(std::move(keys)) {}

    FunctionalConstraint(Own<Variable> key, SrcLocation loc = {}) : Constraint(std::move(loc)) {
        keys.push_back(std::move(key));
    }

    /** get keys */
    std::vector<Variable*> getKeys() const {
        return toPtrVector(keys);
    }

    /** get arity of the keys (i.e. number of source nodes: (x,y)->z has an arity of 2) */
    size_t getArity() const {
        return keys.size();
    }

    std::vector<const Node*> getChildNodes() const override {
        std::vector<const Node*> res;
        for (auto& cur : keys) {
            res.push_back(cur.get());
        }
        /* res.push_back(rhs.get()); */
        return res;
    }

    FunctionalConstraint* clone() const override {
        VecOwn<Variable> newKeys;
        for (const auto& key : keys) {
            newKeys.push_back(Own<Variable>(key->clone()));
        }
        auto* res = new FunctionalConstraint(std::move(newKeys));
        res->setSrcLoc(getSrcLoc());
        return res;
    }

public:
    void print(std::ostream& os) const override {
        os << "keys ";
        if (keys.size() > 1) {
            os << "(";
        }
        os << join(keys, ",", print_deref<Own<ast::Variable>>());
        if (keys.size() > 1) {
            os << ")";
        }
    }

    bool equal(const Node& node) const override {
        assert(nullptr != dynamic_cast<const FunctionalConstraint*>(&node));
        const auto& other = static_cast<const FunctionalConstraint&>(node);
        if (keys.size() != other.keys.size()) {
            return false;
        }
        for (size_t i = 0; i < keys.size(); i++) {
            if (!equal_ptr(keys.at(i), other.keys.at(i))) {
                return false;
            }
        }
        return true;
    }

    bool equivalentConstraint(const FunctionalConstraint& other) const {
        if (this->getArity() != other.getArity()) {
            return false;
        }
        std::set<std::string> keyNames;
        for (const auto& key : keys) {
            keyNames.insert(key->getName());
        }
        for (const auto& key : other.keys) {
            if (keyNames.find(key->getName()) == keyNames.end()) {
                return false;
            }
        }
        return true;
    }

    /* Functional constraint */
    VecOwn<Variable> keys;
};

}  // namespace souffle::ast
