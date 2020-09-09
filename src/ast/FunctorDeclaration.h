/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file FunctorDeclaration.h
 *
 * Defines the external functor class
 *
 ***********************************************************************/

#pragma once

#include "ast/Node.h"
#include "parser/SrcLocation.h"
#include "souffle/RamTypes.h"
#include "souffle/TypeAttribute.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StreamUtil.h"
#include "souffle/utility/tinyformat.h"
#include <cassert>
#include <cstdlib>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class AstFunctorDeclaration
 * @brief User-defined functor declaration
 *
 * Example:
 *    .declfun foo(x:number, y:number):number
 */

class AstFunctorDeclaration : public AstNode {
public:
    AstFunctorDeclaration(std::string name, std::vector<TypeAttribute> argsTypes, TypeAttribute returnType,
            bool stateful, SrcLocation loc = {})
            : AstNode(std::move(loc)), name(std::move(name)), argsTypes(std::move(argsTypes)),
              returnType(returnType), stateful(stateful) {
        assert(this->name.length() > 0 && "functor name is empty");
    }

    /** Return name */
    const std::string& getName() const {
        return name;
    }

    /** Return type */
    const std::vector<TypeAttribute>& getArgsTypes() const {
        return argsTypes;
    }

    /** Get return type */
    TypeAttribute getReturnType() const {
        return returnType;
    }

    /** Return number of arguments */
    size_t getArity() const {
        return argsTypes.size();
    }

    /** Check whether functor is stateful */
    bool isStateful() const {
        return stateful;
    }

    AstFunctorDeclaration* clone() const override {
        return new AstFunctorDeclaration(name, argsTypes, returnType, stateful, getSrcLoc());
    }

protected:
    void print(std::ostream& out) const override {
        auto convert = [&](TypeAttribute type) {
            switch (type) {
                case TypeAttribute::Signed: return "number";
                case TypeAttribute::Symbol: return "symbol";
                case TypeAttribute::Float: return "float";
                case TypeAttribute::Unsigned: return "unsigned";
                case TypeAttribute::Record: break;
                case TypeAttribute::ADT: break;
            }
            fatal("unhandled `TypeAttribute`");
        };

        tfm::format(
                out, ".declfun %s(%s): %s", name, join(map(argsTypes, convert), ","), convert(returnType));
        if (stateful) {
            out << " stateful";
        }
        out << std::endl;
    }

    bool equal(const AstNode& node) const override {
        const auto& other = static_cast<const AstFunctorDeclaration&>(node);
        return name == other.name && argsTypes == other.argsTypes && returnType == other.returnType &&
               stateful == other.stateful;
    }

    /** Name of functor */
    const std::string name;

    /** Types of arguments */
    const std::vector<TypeAttribute> argsTypes;

    /** Type of the return value */
    const TypeAttribute returnType;

    /** Stateful flag */
    const bool stateful;
};

}  // end of namespace souffle
