/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Loop.h
 *
 ***********************************************************************/

#pragma once

#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "ram/Statement.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StreamUtil.h"
#include <cassert>
#include <memory>
#include <ostream>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class RamLoop
 * @brief Execute statement until statement terminates loop via an exit statement
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * LOOP
 *   PARALLEL
 *     ...
 *   END PARALLEL
 * END LOOP
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamLoop : public RamStatement {
public:
    RamLoop(std::unique_ptr<RamStatement> b) : body(std::move(b)) {
        assert(body != nullptr && "Loop body is a null-pointer");
    }

    /** @brief Get loop body */
    const RamStatement& getBody() const {
        return *body;
    }

    std::vector<const RamNode*> getChildNodes() const override {
        return {body.get()};
    }

    RamLoop* clone() const override {
        return new RamLoop(souffle::clone(body));
    }

    void apply(const RamNodeMapper& map) override {
        body = map(std::move(body));
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos) << "LOOP" << std::endl;
        RamStatement::print(body.get(), os, tabpos + 1);
        os << times(" ", tabpos) << "END LOOP" << std::endl;
    }

    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamLoop&>(node);
        return equal_ptr(body, other.body);
    }

    /** loop body */
    std::unique_ptr<RamStatement> body;
};

}  // end of namespace souffle
