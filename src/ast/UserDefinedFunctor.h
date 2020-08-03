/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file UserDefinedFunctor.h
 *
 ***********************************************************************/

#pragma once

#include "RamTypes.h"
#include "SrcLocation.h"
#include "ast/Functor.h"
#include "ast/Node.h"
#include "utility/ContainerUtil.h"
#include "utility/MiscUtil.h"
#include "utility/StreamUtil.h"
#include <algorithm>
#include <cassert>
#include <cstddef>
#include <optional>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle {
class AstArgument;

/**
 * User-Defined Functor
 */
class AstUserDefinedFunctor : public AstFunctor {
public:
    explicit AstUserDefinedFunctor(std::string name) : AstFunctor({}, {}), name(std::move(name)){};

    AstUserDefinedFunctor(std::string name, VecOwn<AstArgument> args, SrcLocation loc = {})
            : AstFunctor(std::move(args), std::move(loc)), name(std::move(name)){};

    /** get name */
    const std::string& getName() const {
        return name;
    }

    /** get type of the functor argument*/
    TypeAttribute getArgType(const size_t arg) const override {
        return argTypes->at(arg);
    }

    /** get type of the functor argument*/
    TypeAttribute getReturnType() const override {
        return returnType.value();
    }

    void setTypes(std::vector<TypeAttribute> argumentsTypes, TypeAttribute retType) {
        assert(argumentsTypes.size() == args.size() && "Size of types must match size of arguments");
        argTypes = std::move(argumentsTypes);
        returnType = retType;
    }

    const std::vector<TypeAttribute>& getArgsTypes() const {
        return argTypes.value();
    }

    AstUserDefinedFunctor* clone() const override {
        auto res = new AstUserDefinedFunctor(name, souffle::clone(args), getSrcLoc());
        // Only copy types if they have already been set.
        if (returnType.has_value()) {
            res->setTypes(argTypes.value(), returnType.value());
        }
        return res;
    }

protected:
    void print(std::ostream& os) const override {
        os << '@' << name << "(" << join(args) << ")";
    }

    bool equal(const AstNode& node) const override {
        const auto& other = static_cast<const AstUserDefinedFunctor&>(node);
        return name == other.name && AstFunctor::equal(node);
    }

    std::optional<std::vector<TypeAttribute>> argTypes;
    std::optional<TypeAttribute> returnType;

    /** name of user-defined functor */
    const std::string name;
};

}  // end of namespace souffle
