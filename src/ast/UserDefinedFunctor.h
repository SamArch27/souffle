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

#include "ast/Functor.h"
#include "ast/Node.h"
#include "parser/SrcLocation.h"
#include "souffle/RamTypes.h"
#include "souffle/TypeAttribute.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <algorithm>
#include <cassert>
#include <cstddef>
#include <optional>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class AstUserDefinedFunctor
 * @brief User-Defined functor class
 */
class AstUserDefinedFunctor : public AstFunctor {
public:
    explicit AstUserDefinedFunctor(std::string name) : AstFunctor({}, {}), name(std::move(name)){};

    AstUserDefinedFunctor(std::string name, VecOwn<AstArgument> args, SrcLocation loc = {})
            : AstFunctor(std::move(args), std::move(loc)), name(std::move(name)){};

    /** return the name */
    const std::string& getName() const {
        return name;
    }

    /** return an argument type */
    TypeAttribute getArgType(const size_t arg) const override {
        return argTypes->at(arg);
    }

    /** get the return type of the functor */
    TypeAttribute getReturnType() const override {
        return returnType.value();
    }

    /** set types of functor */
    void setTypes(std::vector<TypeAttribute> argumentsTypes, TypeAttribute retType, bool state) {
        assert(argumentsTypes.size() == args.size() && "Size of types must match size of arguments");
        argTypes = std::move(argumentsTypes);
        returnType = retType;
        stateful = state;
    }

    /** get argument types */
    const std::vector<TypeAttribute>& getArgsTypes() const {
        return argTypes.value();
    }

    /** is stateful */
    bool isStateful() const {
        return stateful;
    }

    AstUserDefinedFunctor* clone() const override {
        auto res = new AstUserDefinedFunctor(name, souffle::clone(args), getSrcLoc());
        // Only copy types if they have already been set.
        if (returnType.has_value()) {
            res->setTypes(argTypes.value(), returnType.value(), stateful);
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

    /** Argument types */
    std::optional<std::vector<TypeAttribute>> argTypes;

    /** Return type */
    std::optional<TypeAttribute> returnType;

    /** stateful */
    bool stateful;

    /** Name */
    const std::string name;
};

}  // end of namespace souffle
