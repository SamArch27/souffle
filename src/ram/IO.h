/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file IO.h
 *
 ***********************************************************************/

#pragma once

#include "ram/Node.h"
#include "ram/Relation.h"
#include "ram/RelationStatement.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/StreamUtil.h"
#include "souffle/utility/StringUtil.h"
#include <algorithm>
#include <map>
#include <memory>
#include <ostream>
#include <string>
#include <utility>

namespace souffle {

/**
 * @class RamIO
 * @brief I/O statement for a relation
 *
 * I/O operation for a relation, e.g., input/output/printsize
 */
class RamIO : public RamRelationStatement {
public:
    RamIO(std::unique_ptr<RamRelationReference> relRef, std::map<std::string, std::string> directives)
            : RamRelationStatement(std::move(relRef)), directives(std::move(directives)) {}

    /** @brief get I/O directives */
    const std::map<std::string, std::string>& getDirectives() const {
        return directives;
    }

    /** @get value of I/O directive */
    const std::string get(const std::string& key) const {
        return directives.at(key);
    }

    RamIO* clone() const override {
        return new RamIO(souffle::clone(relationRef), directives);
    }

protected:
    void print(std::ostream& os, int tabpos) const override {
        const RamRelation& rel = getRelation();
        os << times(" ", tabpos);
        os << "IO " << rel.getName() << " (";
        os << join(directives, ",", [](std::ostream& out, const auto& arg) {
            out << arg.first << "=\"" << escape(arg.second) << "\"";
        });
        os << ")" << std::endl;
    };

    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamIO&>(node);
        return RamRelationStatement::equal(other) && directives == other.directives;
    }

    /** IO directives */
    std::map<std::string, std::string> directives;
};

}  // end of namespace souffle
