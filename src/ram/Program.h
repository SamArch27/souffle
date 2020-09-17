/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2017, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Program.h
 *
 * Defines a Program of a relational algebra query
 *
 ***********************************************************************/

#pragma once

#include "ram/LambdaNodeMapper.h"
#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "ram/Relation.h"
#include "ram/Statement.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/MiscUtil.h"
#include <cassert>
#include <map>
#include <memory>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle::ram {

/**
 * @class Program
 * @brief RAM program relation declaration and functions
 *
 * A typical example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * PROGRAM
 *   DECLARATION
 *     A(x:i:number)
 *   END DECLARATION
 *   BEGIN MAIN
 *     ...
 *   END MAIN
 * END PROGRAM
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class Program : public Node {
private:
    Program() = default;

public:
    Program(VecOwn<Relation> rels, Own<Statement> main, std::map<std::string, Own<Statement>> subs)
            : relations(std::move(rels)), main(std::move(main)), subroutines(std::move(subs)) {
        assert(this->main != nullptr && "Main program is a null-pointer");
        for (const auto& rel : relations) {
            assert(rel != nullptr && "Relation is a null-pointer");
        }
        for (const auto& sub : subroutines) {
            assert(sub.second != nullptr && "Subroutine is a null-pointer");
        }
    }

    std::vector<const Node*> getChildNodes() const override {
        std::vector<const Node*> children;
        children = main->getChildNodes();
        for (auto& rel : relations) {
            children.push_back(rel.get());
        }
        for (auto& sub : subroutines) {
            children.push_back(sub.second.get());
        }
        return children;
    }

    /** @brief Get main program */
    Statement& getMain() const {
        return *main;
    }

    /** @brief Get all relations of RAM program  */
    std::vector<Relation*> getRelations() const {
        return toPtrVector(relations);
    }

    /** @brief Get all subroutines of a RAM program */
    const std::map<std::string, Statement*> getSubroutines() const {
        std::map<std::string, Statement*> subroutineRefs;
        for (auto& sub : subroutines) {
            subroutineRefs.insert({sub.first, sub.second.get()});
        }
        return subroutineRefs;
    }

    /** @brief Get a specific subroutine */
    const Statement& getSubroutine(const std::string& name) const {
        return *subroutines.at(name);
    }

    Program* clone() const override {
        auto* res = new Program();
        res->main = souffle::clone(main);
        for (auto& rel : relations) {
            res->relations.push_back(souffle::clone(rel));
        }
        for (auto& sub : subroutines) {
            res->subroutines[sub.first] = souffle::clone(sub.second);
        }
        std::map<const Relation*, const Relation*> refMap;
        res->apply(makeLambdaRamMapper([&](Own<Node> node) -> Own<Node> {
            // rewire relation references to newly cloned relations
            if (const RelationReference* relRef = dynamic_cast<RelationReference*>(node.get())) {
                const Relation* rel = refMap[relRef->get()];
                assert(rel != nullptr && "dangling RAM relation reference");
                return mk<RelationReference>(rel);
            } else {
                return node;
            }
        }));
        return res;
    }

    void apply(const NodeMapper& map) override {
        main = map(std::move(main));
        for (auto& rel : relations) {
            rel = map(std::move(rel));
        }
        for (auto& sub : subroutines) {
            sub.second = map(std::move(sub.second));
        }
    }

protected:
    void print(std::ostream& out) const override {
        out << "PROGRAM" << std::endl;
        out << " DECLARATION" << std::endl;
        for (const auto& rel : relations) {
            out << "  " << *rel << std::endl;
        }
        out << " END DECLARATION" << std::endl;
        for (const auto& sub : subroutines) {
            out << " SUBROUTINE " << sub.first << std::endl;
            sub.second->print(out, 2);
            out << " END SUBROUTINE" << std::endl;
        }
        out << " BEGIN MAIN" << std::endl;
        main->print(out, 2);
        out << " END MAIN" << std::endl;
        out << "END PROGRAM" << std::endl;
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const Program&>(node);

        return equal_targets(relations, other.relations) && equal_ptr(main, other.main) &&
               equal_targets(subroutines, other.subroutines);
    }

protected:
    /** Relations of RAM program */
    VecOwn<Relation> relations;

    /** Main program */
    Own<Statement> main;

    /** Subroutines for provenance system */
    std::map<std::string, Own<Statement>> subroutines;
};

}  // namespace souffle::ram
