/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Conditional.h
 *
 * Defines the interface for RAM transformation passes.
 *
 ***********************************************************************/

#pragma once

#include "ram/transform/Meta.h"
#include "ram/transform/Transformer.h"
#include <functional>
#include <memory>
#include <string>
#include <utility>

namespace souffle {

class RamTranslationUnit;

/**
 * @Class RamConditionalTransformer
 * @Brief Composite conditional transformer
 *
 * A transformation is invoked if a condition holds.
 */
class RamConditionalTransformer : public RamMetaTransformer {
public:
    RamConditionalTransformer(std::function<bool()> fn, std::unique_ptr<RamTransformer> tb)
            : func(std::move(fn)), body(std::move(tb)) {}
    std::string getName() const override {
        return "RamConditionalTransformer";
    }
    bool transform(RamTranslationUnit& tU) override {
        if (func()) {
            return body->apply(tU);
        } else {
            return false;
        }
    }

protected:
    std::function<bool()> func;
    std::unique_ptr<RamTransformer> body;
};

}  // end of namespace souffle
