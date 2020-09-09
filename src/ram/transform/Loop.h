/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Loop.h
 *
 * Defines the interface for RAM transformation passes.
 *
 ***********************************************************************/

#pragma once

#include "ram/transform/Meta.h"
#include <memory>
#include <string>
#include <utility>

namespace souffle {

class RamTranslationUnit;

/**
 * @Class RamLoopTransformer
 * @Brief Composite loop transformer
 *
 * A transformation is invoked iteratively until no further change
 * is made.
 */
class RamLoopTransformer : public RamMetaTransformer {
public:
    RamLoopTransformer(std::unique_ptr<RamTransformer> tLoop) : loop(std::move(tLoop)) {}
    std::string getName() const override {
        return "RamLoopTransformer";
    }
    bool transform(RamTranslationUnit& tU) override {
        int ctr = 0;
        while (loop->apply(tU)) {
            ctr++;
        }
        return ctr > 0;
    }

protected:
    /** transformer of the loop */
    std::unique_ptr<RamTransformer> loop;
};

}  // end of namespace souffle
