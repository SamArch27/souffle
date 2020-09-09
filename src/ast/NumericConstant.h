/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file NumericConstant.h
 *
 * Defines the numeric constant class
 *
 ***********************************************************************/

#pragma once

#include "ast/Constant.h"
#include "ast/Node.h"
#include "parser/SrcLocation.h"
#include "souffle/RamTypes.h"
#include <optional>
#include <string>
#include <utility>

namespace souffle {

/**
 * Numeric Constant
 *
 * The constant can be initialized with type.
 * If this is the case, the typesystem will be forced to use it.
 * Otherwise the type is inferred from context.
 */
class AstNumericConstant : public AstConstant {
public:
    enum class Type { Int, Uint, Float };

    AstNumericConstant(RamSigned value) : AstConstant(std::to_string(value)), type(Type::Int) {}

    AstNumericConstant(std::string constant, SrcLocation loc) : AstConstant(std::move(constant)) {
        setSrcLoc(std::move(loc));
    }

    AstNumericConstant(std::string constant, std::optional<Type> type = std::nullopt, SrcLocation loc = {})
            : AstConstant(std::move(constant)), type(type) {
        setSrcLoc(std::move(loc));
    }

    AstNumericConstant* clone() const override {
        auto* copy = new AstNumericConstant(getConstant(), getType());
        copy->setSrcLoc(getSrcLoc());
        return copy;
    }

    const std::optional<Type>& getType() const {
        return type;
    }

    void setType(Type newType) {
        type = newType;
    }

protected:
    bool equal(const AstNode& node) const override {
        const auto& other = static_cast<const AstNumericConstant&>(node);
        return AstConstant::equal(node) && type == other.type;
    }

private:
    std::optional<Type> type;
};

}  // end of namespace souffle
