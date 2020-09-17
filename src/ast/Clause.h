/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Clause.h
 *
 * Defines the clause class
 *
 ***********************************************************************/

#pragma once

#include "ast/Atom.h"
#include "ast/ExecutionPlan.h"
#include "ast/Literal.h"
#include "ast/Node.h"
#include "ast/utility/NodeMapper.h"
#include "parser/SrcLocation.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <algorithm>
#include <memory>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle::ast {

/**
 * @class Clause
 * @brief Intermediate representation of a horn clause
 *
 *  A clause can either be:
 *      - a fact  - a clause with no body (e.g., X(a,b))
 *      - a rule  - a clause with a head and a body (e.g., Y(a,b) -: X(a,b))
 */
class Clause : public Node {
public:
    Clause(Own<Atom> head = {}, VecOwn<Literal> bodyLiterals = {}, Own<ExecutionPlan> plan = {},
            SrcLocation loc = {})
            : Node(std::move(loc)), head(std::move(head)), bodyLiterals(std::move(bodyLiterals)),
              plan(std::move(plan)) {}

    /** Add a literal to the body of the clause */
    void addToBody(Own<Literal> literal) {
        bodyLiterals.push_back(std::move(literal));
    }

    /** Set the head of clause to @p h */
    void setHead(Own<Atom> h) {
        head = std::move(h);
    }

    /** Set the bodyLiterals of clause to @p body */
    void setBodyLiterals(VecOwn<Literal> body) {
        bodyLiterals = std::move(body);
    }

    /** Return the atom that represents the head of the clause */
    Atom* getHead() const {
        return head.get();
    }

    /** Obtains a copy of the internally maintained body literals */
    std::vector<Literal*> getBodyLiterals() const {
        return toPtrVector(bodyLiterals);
    }

    /** Obtains the execution plan associated to this clause or null if there is none */
    const ExecutionPlan* getExecutionPlan() const {
        return plan.get();
    }

    /** Updates the execution plan associated to this clause */
    void setExecutionPlan(Own<ExecutionPlan> plan) {
        this->plan = std::move(plan);
    }

    /** Resets the execution plan */
    void clearExecutionPlan() {
        plan = nullptr;
    }

    Clause* clone() const override {
        return new Clause(
                souffle::clone(head), souffle::clone(bodyLiterals), souffle::clone(plan), getSrcLoc());
    }

    void apply(const NodeMapper& map) override {
        head = map(std::move(head));
        for (auto& lit : bodyLiterals) {
            lit = map(std::move(lit));
        }
    }

    std::vector<const Node*> getChildNodes() const override {
        std::vector<const Node*> res = {head.get()};
        for (auto& cur : bodyLiterals) {
            res.push_back(cur.get());
        }
        return res;
    }

protected:
    void print(std::ostream& os) const override {
        if (head != nullptr) {
            os << *head;
        }
        if (!bodyLiterals.empty()) {
            os << " :- \n   " << join(bodyLiterals, ",\n   ");
        }
        os << ".";
        if (plan != nullptr) {
            os << *plan;
        }
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const Clause&>(node);
        return equal_ptr(head, other.head) && equal_targets(bodyLiterals, other.bodyLiterals) &&
               equal_ptr(plan, other.plan);
    }

    /** Head of the clause */
    Own<Atom> head;

    /** Body literals of clause */
    VecOwn<Literal> bodyLiterals;

    /** User defined execution plan (if not defined, plan is null) */
    Own<ExecutionPlan> plan;
};

}  // namespace souffle::ast
