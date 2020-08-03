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
 ***********************************************************************/

#pragma once

#include "SrcLocation.h"
#include "ast/Argument.h"
#include "ast/Node.h"
#include "ast/NodeMapper.h"
#include "ast/QualifiedName.h"
#include "utility/ContainerUtil.h"
#include "utility/MiscUtil.h"
#include <memory>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * An argument capable of casting a value of one type into another.
 */
class AstTypeCast : public AstArgument {
public:
    AstTypeCast(Own<AstArgument> value, AstQualifiedName type, SrcLocation loc = {})
            : AstArgument(std::move(loc)), value(std::move(value)), type(std::move(type)) {}

    /** Get value */
    AstArgument* getValue() const {
        return value.get();
    }

    /** Get type */
    const AstQualifiedName& getType() const {
        return type;
    }

    /** Set type */
    void setType(const AstQualifiedName& type) {
        this->type = type;
    }

    std::vector<const AstNode*> getChildNodes() const override {
        auto res = AstArgument::getChildNodes();
        res.push_back(value.get());
        return res;
    }

    AstTypeCast* clone() const override {
        return new AstTypeCast(souffle::clone(value), type, getSrcLoc());
    }

    void apply(const AstNodeMapper& map) override {
        value = map(std::move(value));
    }

protected:
    void print(std::ostream& os) const override {
        os << "as(" << *value << "," << type << ")";
    }

    bool equal(const AstNode& node) const override {
        const auto& other = static_cast<const AstTypeCast&>(node);
        return type == other.type && equal_ptr(value, other.value);
    }

    /** The value to be casted */
    Own<AstArgument> value;

    /** The target type name */
    AstQualifiedName type;
};

}  // end of namespace souffle
