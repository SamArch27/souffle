/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file BinRelationStatement.h
 *
 ***********************************************************************/

#pragma once

#include "ram/Node.h"
#include "ram/NodeMapper.h"
#include "ram/Relation.h"
#include "ram/Statement.h"
#include "souffle/utility/ContainerUtil.h"
#include <cassert>
#include <cstddef>
#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class RamBinRelationStatement
 * @brief Abstract class for a binary relation
 *
 * Comprises two RamRelations
 */
class RamBinRelationStatement : public RamStatement {
public:
    RamBinRelationStatement(std::unique_ptr<RamRelationReference> f, std::unique_ptr<RamRelationReference> s)
            : first(std::move(f)), second(std::move(s)) {
        assert(first->get()->getArity() == second->get()->getArity() && "mismatching arities");

        assert(first != nullptr && "First relation is a null-pointer");
        assert(second != nullptr && "Second relation is a null-pointer");
        const auto& type1 = first->get()->getAttributeTypes();
        const auto& type2 = first->get()->getAttributeTypes();
        for (size_t i = 0; i < first->get()->getArity(); i++) {
            assert(type1[i] == type2[i] && "mismatching type");
        }
    }

    /** @brief Get first relation */
    const RamRelation& getFirstRelation() const {
        return *first->get();
    }

    /** @brief Get second relation */
    const RamRelation& getSecondRelation() const {
        return *second->get();
    }

    std::vector<const RamNode*> getChildNodes() const override {
        return {first.get(), second.get()};
    }

    void apply(const RamNodeMapper& map) override {
        first = map(std::move(first));
        second = map(std::move(second));
    }

protected:
    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamBinRelationStatement&>(node);
        return equal_ptr(first, other.first) && equal_ptr(second, other.second);
    }

protected:
    /** first argument of binary statement */
    std::unique_ptr<RamRelationReference> first;

    /** second argument of binary statement */
    std::unique_ptr<RamRelationReference> second;
};

}  // end of namespace souffle
