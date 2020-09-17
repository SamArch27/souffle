/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020, The Souffle Developers. All rights reserved.
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Directive.h
 *
 * Defines a directive for a relation
 *
 ***********************************************************************/

#pragma once

#include "ast/Node.h"
#include "ast/QualifiedName.h"
#include "parser/SrcLocation.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <map>
#include <ostream>
#include <string>
#include <utility>

namespace souffle::ast {

enum class DirectiveType { input, output, printsize, limitsize };

// FIXME: I'm going crazy defining these. There has to be a library that does this boilerplate for us.
inline std::ostream& operator<<(std::ostream& os, DirectiveType e) {
    switch (e) {
        case DirectiveType::input: return os << "input";
        case DirectiveType::output: return os << "output";
        case DirectiveType::printsize: return os << "printsize";
        case DirectiveType::limitsize: return os << "limitsize";
    }

    UNREACHABLE_BAD_CASE_ANALYSIS
}

/**
 * @class Directive
 * @brief a directive has a type (e.g. input/output/printsize/limitsize), qualified relation name, and a key
 * value map for storing parameters of the directive.
 */
class Directive : public Node {
public:
    Directive(DirectiveType type, QualifiedName name, SrcLocation loc = {})
            : Node(std::move(loc)), type(type), name(std::move(name)) {}

    /** Get directive type */
    DirectiveType getType() const {
        return type;
    }

    /** Set directive  type */
    void setType(DirectiveType type) {
        this->type = type;
    }

    /** Get relation name */
    const QualifiedName& getQualifiedName() const {
        return name;
    }

    /** Set relation name */
    void setQualifiedName(QualifiedName name) {
        this->name = std::move(name);
    }

    /** Get parameter */
    const std::string& getDirective(const std::string& key) const {
        return directives.at(key);
    }

    /** Add new parameter */
    void addDirective(const std::string& key, std::string value) {
        directives[key] = std::move(value);
    }

    /** Check for a parameter */
    bool hasDirective(const std::string& key) const {
        return directives.find(key) != directives.end();
    }

    /** Get parameters */
    const std::map<std::string, std::string>& getDirectives() const {
        return directives;
    }

    Directive* clone() const override {
        auto res = new Directive(type, name, getSrcLoc());
        res->directives = directives;
        return res;
    }

protected:
    void print(std::ostream& os) const override {
        os << "." << type << " " << name;
        if (!directives.empty()) {
            os << "(" << join(directives, ",", [](std::ostream& out, const auto& arg) {
                out << arg.first << "=\"" << arg.second << "\"";
            }) << ")";
        }
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const Directive&>(node);
        return other.type == type && other.name == name && other.directives == directives;
    }

    /** Type of directive */
    DirectiveType type;

    /** Relation name of the directive */
    QualifiedName name;

    /** Parameters of directive */
    std::map<std::string, std::string> directives;
};

}  // namespace souffle::ast
