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
#include <cassert>
#include <optional>
#include <string>
#include <utility>

namespace souffle::ast {

/**
 * Numeric Constant
 *
 * The constant can be initialized with type.
 * If this is the case, the typesystem will be forced to use it.
 * Otherwise the type is inferred from context.
 */
class NumericConstant : public Constant {
public:
    enum class Type { Int, Uint, Float };

    NumericConstant(RamSigned value) : Constant(std::to_string(value)), fixedType(Type::Int) {}

    NumericConstant(std::string constant, SrcLocation loc) : Constant(std::move(constant)) {
        setSrcLoc(std::move(loc));
    }

    NumericConstant(std::string constant, std::optional<Type> fixedType = std::nullopt, SrcLocation loc = {})
            : Constant(std::move(constant)), fixedType(fixedType) {
        setSrcLoc(std::move(loc));
    }

    NumericConstant* clone() const override {
        auto* copy = new NumericConstant(getConstant(), getFixedType());
        copy->setSrcLoc(getSrcLoc());
        return copy;
    }

    const std::optional<Type>& getFixedType() const {
        return fixedType;
    }

protected:
    bool equal(const Node& node) const override {
        const auto& other = static_cast<const NumericConstant&>(node);
        return Constant::equal(node) && fixedType == other.fixedType;
    }

private:
    std::optional<Type> fixedType;
};

}  // namespace souffle::ast
