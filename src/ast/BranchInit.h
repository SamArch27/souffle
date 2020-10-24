/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file BranchInit.h
 *
 * Defines an argument covering the branch initialization of ADTs.
 *
 ***********************************************************************/

#pragma once

#include "ast/Argument.h"
#include "ast/Node.h"
#include "ast/Term.h"
#include "parser/SrcLocation.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/StreamUtil.h"
#include "souffle/utility/tinyformat.h"
#include <iosfwd>
#include <string>
#include <utility>
#include <vector>

namespace souffle::ast {

/**
 * @class BranchInit
 * @brief Initialization of ADT instance.
 *
 * @param constructor An entity used to create a variant type. Can be though of as a name of the branch.
 *
 * Initializes one of the branches of ADT. The syntax for branches initialization is
 * $Constructor(args...)
 * In case of the branch with no arguments it is simplified to $Constructor.
 */
class BranchInit : public Term {
public:
    BranchInit(std::string constructor, VecOwn<Argument> args, SrcLocation loc = {})
            : Term(std::move(args), std::move(loc)), constructor(std::move(constructor)) {}

    const std::string& getConstructor() const {
        return constructor;
    }

    BranchInit* clone() const override {
        return new BranchInit(constructor, souffle::clone(args), getSrcLoc());
    }

protected:
    void print(std::ostream& os) const override {
        os << tfm::format("$%s(%s)", constructor, join(args, ", "));
    }

    /** Implements the node comparison for this node type */
    bool equal(const Node& node) const override {
        const auto& other = dynamic_cast<const BranchInit&>(node);
        return (constructor == other.constructor) && equal_targets(args, other.args);
    }

private:
    /** The adt branch constructor */
    std::string constructor;
};

}  // namespace souffle::ast
