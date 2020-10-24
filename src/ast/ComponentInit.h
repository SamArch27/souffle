/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ComponentInit.h
 *
 * Defines the component-initialization class
 *
 ***********************************************************************/

#pragma once

#include "ast/ComponentType.h"
#include "ast/Node.h"
#include "ast/utility/NodeMapper.h"
#include "parser/SrcLocation.h"
#include "souffle/utility/MiscUtil.h"
#include <memory>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle::ast {

/**
 * @class ComponentInit
 * @brief Component initialization class
 *
 * Example:
 *  .init X=B<T1,T2>
 *
 * Intialization of a component with type parameters
 */
class ComponentInit : public Node {
public:
    ComponentInit(std::string name, Own<ComponentType> type, SrcLocation loc = {})
            : Node(std::move(loc)), instanceName(std::move(name)), componentType(std::move(type)) {}

    /** Return instance name */
    const std::string& getInstanceName() const {
        return instanceName;
    }

    /** Set instance name */
    void setInstanceName(std::string name) {
        instanceName = std::move(name);
    }

    /** Return component type */
    const ComponentType* getComponentType() const {
        return componentType.get();
    }

    /** Set component type */
    void setComponentType(Own<ComponentType> type) {
        componentType = std::move(type);
    }

    ComponentInit* clone() const override {
        return new ComponentInit(instanceName, souffle::clone(componentType), getSrcLoc());
    }

    void apply(const NodeMapper& mapper) override {
        componentType = mapper(std::move(componentType));
    }

    std::vector<const Node*> getChildNodes() const override {
        return {componentType.get()};
    }

protected:
    void print(std::ostream& os) const override {
        os << ".init " << instanceName << " = " << *componentType;
    }

    bool equal(const Node& node) const override {
        const auto& other = static_cast<const ComponentInit&>(node);
        return instanceName == other.instanceName && *componentType == *other.componentType;
    }

    /** Instance name */
    std::string instanceName;

    /** Actual component arguments for instantiation */
    Own<ComponentType> componentType;
};

}  // namespace souffle::ast
