/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file NestedOperation.h
 *
 ***********************************************************************/

#pragma once

#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "ram/Operation.h"
#include "souffle/utility/MiscUtil.h"
#include <cassert>
#include <iosfwd>
#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class RamNestedOperation
 * @brief Abstract class for a nesting operations in a loop-nest
 *
 * In the following example, the nested operation
 * of "IF C1" is "IF C2":
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *  QUERY
 *   ...
 *    IF C1
 *     IF C2
 *      ...
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *
 * TODO (b-scholz): profile text is awkward; perhaps there is a better way of
 *                  storing profile information for RAM operations since
 *                  it is not always used for all RAM operations.
 */
class RamNestedOperation : public RamOperation {
public:
    RamNestedOperation(std::unique_ptr<RamOperation> nested, std::string profileText = "")
            : nestedOperation(std::move(nested)), profileText(std::move(profileText)) {
        assert(nestedOperation != nullptr);
    }

    RamNestedOperation* clone() const override = 0;

    /** @brief Get nested operation */
    RamOperation& getOperation() const {
        return *nestedOperation;
    }

    /** @brief Get profile text */
    const std::string& getProfileText() const {
        return profileText;
    }

    std::vector<const RamNode*> getChildNodes() const override {
        return {nestedOperation.get()};
    }

    void apply(const RamNodeMapper& map) override {
        nestedOperation = map(std::move(nestedOperation));
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        RamOperation::print(nestedOperation.get(), os, tabpos);
    }

    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamNestedOperation&>(node);
        return equal_ptr(nestedOperation, other.nestedOperation) && profileText == other.profileText;
    }

    /** Nested operation */
    std::unique_ptr<RamOperation> nestedOperation;

    /** Text used by the profiler */
    const std::string profileText;
};

}  // namespace souffle
