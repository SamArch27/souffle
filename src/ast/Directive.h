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

namespace souffle {

enum class AstDirectiveType { input, output, printsize, limitsize };

// FIXME: I'm going crazy defining these. There has to be a library that does this boilerplate for us.
inline std::ostream& operator<<(std::ostream& os, AstDirectiveType e) {
    switch (e) {
        case AstDirectiveType::input: return os << "input";
        case AstDirectiveType::output: return os << "output";
        case AstDirectiveType::printsize: return os << "printsize";
        case AstDirectiveType::limitsize: return os << "limitsize";
    }

    UNREACHABLE_BAD_CASE_ANALYSIS
}

/**
 * @class AstDirective
 * @brief a directive has a type (e.g. input/output/printsize/limitsize), qualified relation name, and a key
 * value map for storing parameters of the directive.
 */
class AstDirective : public AstNode {
public:
    AstDirective(AstDirectiveType type, AstQualifiedName name, SrcLocation loc = {})
            : AstNode(std::move(loc)), type(type), name(std::move(name)) {}

    /** Get directive type */
    AstDirectiveType getType() const {
        return type;
    }

    /** Set directive  type */
    void setType(AstDirectiveType type) {
        this->type = type;
    }

    /** Get relation name */
    const AstQualifiedName& getQualifiedName() const {
        return name;
    }

    /** Set relation name */
    void setQualifiedName(AstQualifiedName name) {
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

    AstDirective* clone() const override {
        auto res = new AstDirective(type, name, getSrcLoc());
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

    bool equal(const AstNode& node) const override {
        const auto& other = static_cast<const AstDirective&>(node);
        return other.type == type && other.name == name && other.directives == directives;
    }

    /** Type of directive */
    AstDirectiveType type;

    /** Relation name of the directive */
    AstQualifiedName name;

    /** Parameters of directive */
    std::map<std::string, std::string> directives;
};

}  // end of namespace souffle
