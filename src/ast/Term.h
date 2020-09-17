/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Term.h
 *
 * Defines the abstract term class
 *
 ***********************************************************************/

#pragma once

#include "ast/Argument.h"
#include "ast/Node.h"
#include "ast/utility/NodeMapper.h"
#include "parser/SrcLocation.h"
#include "souffle/utility/ContainerUtil.h"
#include <algorithm>
#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace souffle::ast {

/**
 * @class Term
 * @brief Defines an abstract term class used for functors and other constructors
 */
class Term : public Argument {
protected:
    template <typename... Operands>
    Term(Operands&&... operands) : Term(asVec(std::forward<Operands>(operands)...)) {}

    template <typename... Operands>
    Term(SrcLocation loc, Operands&&... operands)
            : Term(asVec(std::forward<Operands>(operands)...), std::move(loc)) {}

    Term(VecOwn<Argument> operands, SrcLocation loc = {})
            : Argument(std::move(loc)), args(std::move(operands)) {}

public:
    /** Get arguments */
    std::vector<Argument*> getArguments() const {
        return toPtrVector(args);
    }

    /** Add argument to argument list */
    void addArgument(Own<Argument> arg) {
        args.push_back(std::move(arg));
    }

    std::vector<const Node*> getChildNodes() const override {
        auto res = Argument::getChildNodes();
        for (auto& cur : args) {
            res.push_back(cur.get());
        }
        return res;
    }

    void apply(const NodeMapper& map) override {
        for (auto& arg : args) {
            arg = map(std::move(arg));
        }
    }

protected:
    bool equal(const Node& node) const override {
        const auto& other = static_cast<const Term&>(node);
        return equal_targets(args, other.args);
    }

    /** Arguments */
    VecOwn<Argument> args;

private:
    template <typename... Operands>
    static VecOwn<Argument> asVec(Operands... ops) {
        Own<Argument> ary[] = {std::move(ops)...};
        VecOwn<Argument> xs;
        for (auto&& x : ary) {
            xs.push_back(std::move(x));
        }
        return xs;
    }
};

}  // namespace souffle::ast
