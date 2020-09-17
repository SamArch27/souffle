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

    /** Get function */
    const std::string& getFunction() const {
        return function;
    }

    /** Set function */
    void setFunction(std::string functor) {
        function = std::move(functor);
    }

    /** Get function information */
    const IntrinsicFunctorInfo* getFunctionInfo() const {
        return info;
    }

    /** Set function information */
    void setFunctionInfo(const IntrinsicFunctorInfo& info) {
        this->info = &info;
    }

    /** Get the return type of the functor. */
    TypeAttribute getReturnType() const override {
        assert(info && "functor info not yet available");
        return info->result;
    }

    /** Get type of the functor argument*/
    TypeAttribute getArgType(const size_t arg) const override {
        assert(info && "functor info not yet available");
        return info->params.at(info->variadic ? 0 : arg);
    }

    IntrinsicFunctor* clone() const override {
        return new IntrinsicFunctor(function, info, souffle::clone(args), getSrcLoc());
    }

protected:
    IntrinsicFunctor(
            std::string op, const IntrinsicFunctorInfo* info, VecOwn<Argument> args, SrcLocation loc = {})
            : Functor(std::move(args), std::move(loc)), function(std::move(op)), info(info) {
        assert((!info || info->symbol == function) && "functor info must match symbol");
    }

    void print(std::ostream& os) const override {
        if (isInfixFunctorOp(function)) {
            os << "(" << join(args, function) << ")";
        } else {
            os << function;
            os << "(" << join(args) << ")";
        }
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const IntrinsicFunctor&>(node);
        return function == other.function && info == other.info && Functor::equal(node);
    }

    /** Function */
    std::string function;

    /** Functor information */
    const IntrinsicFunctorInfo* info = nullptr;
};

}  // namespace souffle::ast
