/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2017, The Souffle Developers. All rights reserved.
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Pragma.h
 *
 * Defines the pragma class
 *
 ***********************************************************************/

#pragma once

#include "ast/Node.h"
#include "parser/SrcLocation.h"
#include <ostream>
#include <string>
#include <utility>

namespace souffle::ast {

/**
 * @class Pragma
 * @brief Representation of a global option
 */
class Pragma : public Node {
public:
    Pragma(std::string key, std::string value, SrcLocation loc = {})
            : Node(std::move(loc)), key(std::move(key)), value(std::move(value)) {}

    Pragma* clone() const override {
        return new Pragma(key, value, getSrcLoc());
    }

    /* Get kvp */
    std::pair<std::string, std::string> getkvp() const {
        return std::pair<std::string, std::string>(key, value);
    }

protected:
    void print(std::ostream& os) const override {
        os << ".pragma " << key << " " << value << "\n";
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const Pragma&>(node);
        return other.key == key && other.value == value;
    }

    /** Name of the key */
    std::string key;

    /** Value */
    std::string value;
};

}  // namespace souffle::ast
