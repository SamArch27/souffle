/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file IntrinsicFunctor.h
 *
 * Defines the intrinsic functor class
 *
 ***********************************************************************/

#pragma once

#include "FunctorOps.h"
#include "ast/Argument.h"
#include "ast/Functor.h"
#include "ast/Node.h"
#include "parser/SrcLocation.h"
#include "souffle/TypeAttribute.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <cassert>
#include <cstddef>
#include <optional>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle::ast {

/**
 * @class IntrinsicFunctor
 * @brief Intrinsic Functor class for functors are in-built.
 */
class IntrinsicFunctor : public Functor {
public:
    template <typename... Operands>
    IntrinsicFunctor(std::string op, Operands&&... operands)
            : Functor(std::forward<Operands>(operands)...), function(std::move(op)) {}

    template <typename... Operands>
    IntrinsicFunctor(SrcLocation loc, std::string op, Operands&&... operands)
            : Functor(std::move(loc), std::forward<Operands>(operands)...), function(std::move(op)) {}

    IntrinsicFunctor(std::string op, VecOwn<Argument> args, SrcLocation loc = {})
            : Functor(std::move(args), std::move(loc)), function(std::move(op)) {}

    /** Get (base type) function */
    const std::string& getBaseFunctionOp() const {
        return function;
    }

    /** Set function */
    void setFunction(std::string functor) {
        function = std::move(functor);
    }

    IntrinsicFunctor* clone() const override {
        return new IntrinsicFunctor(function, souffle::clone(args), getSrcLoc());
    }

protected:
    void print(std::ostream& os) const override {
        if (isInfixFunctorOp(function)) {
            os << "(" << join(args, function) << ")";
        } else {
            // Negation is handled differently to all other functors so we need a special case.
            if (function == FUNCTOR_INTRINSIC_PREFIX_NEGATE_NAME) {
                os << "-";
            } else {
                os << function;
            }
            os << "(" << join(args) << ")";
        }
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const IntrinsicFunctor&>(node);
        return function == other.function && Functor::equal(node);
    }

    /** Function */
    std::string function;
};

}  // namespace souffle::ast
