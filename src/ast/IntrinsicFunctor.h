/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file IntrinsicFunctor.h
 *
 ***********************************************************************/

#pragma once

#include "FunctorOps.h"
#include "RamTypes.h"
#include "SrcLocation.h"
#include "ast/Functor.h"
#include "ast/Node.h"
#include "utility/ContainerUtil.h"
#include "utility/StreamUtil.h"
#include <cassert>
#include <cstddef>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle {
class AstArgument;

/**
 * Intrinsic Functor
 */
class AstIntrinsicFunctor : public AstFunctor {
public:
    template <typename... Operands>
    AstIntrinsicFunctor(std::string op, Operands&&... operands)
            : AstFunctor(std::forward<Operands>(operands)...), function(std::move(op)) {}

    template <typename... Operands>
    AstIntrinsicFunctor(SrcLocation loc, std::string op, Operands&&... operands)
            : AstFunctor(std::move(loc), std::forward<Operands>(operands)...), function(std::move(op)) {}

    AstIntrinsicFunctor(std::string op, VecOwn<AstArgument> args, SrcLocation loc = {})
            : AstFunctor(std::move(args), std::move(loc)), function(std::move(op)) {}

    /** get function */
    const std::string& getFunction() const {
        return function;
    }

    /** set function */
    void setFunction(std::string functor) {
        function = std::move(functor);
    }

    const IntrinsicFunctor* getFunctionInfo() const {
        return info;
    }

    void setFunctionInfo(const IntrinsicFunctor& info) {
        this->info = &info;
    }

    /** get the return type of the functor. */
    TypeAttribute getReturnType() const override {
        assert(info && "functor info not yet available");
        return info->result;
    }

    /** get type of the functor argument*/
    TypeAttribute getArgType(const size_t arg) const override {
        assert(info && "functor info not yet available");
        return info->params.at(info->variadic ? 0 : arg);
    }

    AstIntrinsicFunctor* clone() const override {
        return new AstIntrinsicFunctor(function, info, souffle::clone(args), getSrcLoc());
    }

protected:
    AstIntrinsicFunctor(
            std::string op, const IntrinsicFunctor* info, VecOwn<AstArgument> args, SrcLocation loc = {})
            : AstFunctor(std::move(args), std::move(loc)), function(std::move(op)), info(info) {
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

    bool equal(const AstNode& node) const override {
        const auto& other = static_cast<const AstIntrinsicFunctor&>(node);
        return function == other.function && info == other.info && AstFunctor::equal(node);
    }

    /** Function */
    std::string function;
    const IntrinsicFunctor* info = nullptr;
};

}  // end of namespace souffle
