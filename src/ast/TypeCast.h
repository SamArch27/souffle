/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file TypeCast.h
 *
 * Defines the type cast class
 *
 ***********************************************************************/

#pragma once

#include "ast/Argument.h"
#include "ast/Node.h"
#include "ast/QualifiedName.h"
#include "ast/utility/NodeMapper.h"
#include "parser/SrcLocation.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/tinyformat.h"
#include <memory>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle::ast {

/**
 * @class TypeCast
 * @brief Defines a type cast class for expressions
 */

class TypeCast : public Argument {
public:
    TypeCast(Own<Argument> value, QualifiedName type, SrcLocation loc = {})
            : Argument(std::move(loc)), value(std::move(value)), type(std::move(type)) {}

    /** Return value */
    Argument* getValue() const {
        return value.get();
    }

    /** Return cast type */
    const QualifiedName& getType() const {
        return type;
    }

    /** Set cast type */
    void setType(const QualifiedName& type) {
        this->type = type;
    }

    std::vector<const Node*> getChildNodes() const override {
        auto res = Argument::getChildNodes();
        res.push_back(value.get());
        return res;
    }

    TypeCast* clone() const override {
        return new TypeCast(souffle::clone(value), type, getSrcLoc());
    }

    void apply(const NodeMapper& map) override {
        value = map(std::move(value));
    }

protected:
    void print(std::ostream& os) const override {
        os << tfm::format("as(%s, %s)", *value, type);
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const TypeCast&>(node);
        return type == other.type && equal_ptr(value, other.value);
    }

    /** Casted value */
    Own<Argument> value;

    /** Cast type */
    QualifiedName type;
};

}  // namespace souffle::ast
