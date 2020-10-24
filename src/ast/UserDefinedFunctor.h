/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file UserDefinedFunctor.h
 *
 * Defines the user-defined functor class
 *
 ***********************************************************************/

#pragma once

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
 * @class UserDefinedFunctor
 * @brief User-Defined functor class
 */
class UserDefinedFunctor : public Functor {
public:
    explicit UserDefinedFunctor(std::string name) : Functor({}, {}), name(std::move(name)){};

    UserDefinedFunctor(std::string name, VecOwn<Argument> args, SrcLocation loc = {})
            : Functor(std::move(args), std::move(loc)), name(std::move(name)){};

    /** return the name */
    const std::string& getName() const {
        return name;
    }

    UserDefinedFunctor* clone() const override {
        auto res = new UserDefinedFunctor(name, souffle::clone(args), getSrcLoc());
        return res;
    }

protected:
    void print(std::ostream& os) const override {
        os << '@' << name << "(" << join(args) << ")";
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const UserDefinedFunctor&>(node);
        return name == other.name && Functor::equal(node);
    }

    /** Name */
    const std::string name;
};

}  // namespace souffle::ast
