/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file TupleOperation.h
 *
 ***********************************************************************/

#pragma once

#include "ram/NestedOperation.h"
#include "ram/Node.h"
#include "ram/Operation.h"
#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class RamTupleOperation
 * @brief Abstract class for relation searches and lookups
 */
class RamTupleOperation : public RamNestedOperation {
public:
    RamTupleOperation(int ident, std::unique_ptr<RamOperation> nested, std::string profileText = "")
            : RamNestedOperation(std::move(nested), std::move(profileText)), identifier(ident) {}

    RamTupleOperation* clone() const override = 0;

    /** @brief Get identifier */
    int getTupleId() const {
        return identifier;
    }

    /** @brief Set identifier */
    void setTupleId(int id) {
        identifier = id;
    }

    std::vector<const RamNode*> getChildNodes() const override {
        return RamNestedOperation::getChildNodes();
    }

protected:
    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamTupleOperation&>(node);
        return RamNestedOperation::equal(other) && identifier == other.identifier;
    }

    /**
     * Identifier for the tuple, corresponding to
     * its position in the loop nest
     */
    int identifier;
};

}  // namespace souffle
