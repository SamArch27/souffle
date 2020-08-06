/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file RecordType.h
 *
 * Defines the record type class
 *
 ***********************************************************************/

#pragma once

#include "Attribute.h"
#include "Node.h"
#include "QualifiedName.h"
#include "SrcLocation.h"
#include "Type.h"
#include "utility/ContainerUtil.h"
#include "utility/StreamUtil.h"
#include <algorithm>
#include <cstddef>
#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class AstRecordType
 * @brief Record type class for record type declarations
 *
 * A record type aggregates a list of fields (i.e. name & type) into a new type.
 * Each record type has a name making the record type unique.
 */
class AstRecordType : public AstType {
public:
    AstRecordType(AstQualifiedName name, VecOwn<AstAttribute> fields, SrcLocation loc = {})
            : AstType(std::move(name), std::move(loc)), fields(std::move(fields)) {}

    /** Add field to record type */
    void add(std::string name, AstQualifiedName type) {
        fields.push_back(mk<AstAttribute>(std::move(name), std::move(type)));
    }

    /** Get fields of record */
    std::vector<AstAttribute*> getFields() const {
        return toPtrVector(fields);
    }

    /** Set field type */
    void setFieldType(size_t idx, AstQualifiedName type) {
        fields.at(idx)->setTypeName(std::move(type));
    }

    AstRecordType* clone() const override {
        return new AstRecordType(getQualifiedName(), souffle::clone(fields), getSrcLoc());
    }

protected:
    void print(std::ostream& os) const override {
        os << ".type " << getQualifiedName() << "= [" << join(fields, ", ") << "]";
    }

    bool equal(const AstNode& node) const override {
        const auto& other = dynamic_cast<const AstRecordType&>(node);
        return getQualifiedName() == other.getQualifiedName() && equal_targets(fields, other.fields);
    }

private:
    /** record fields */
    VecOwn<AstAttribute> fields;
};

}  // end of namespace souffle
