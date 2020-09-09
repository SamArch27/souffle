/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Sequence.h
 *
 * Defines the interface for RAM transformation passes.
 *
 ***********************************************************************/

#pragma once

#include "ram/transform/Meta.h"
#include <cassert>
#include <memory>
#include <string>
#include <vector>

namespace souffle {

class RamTranslationUnit;

/**
 * @Class RamTransformerSequence
 * @Brief Composite sequence transformer
 *
 * A sequence of transformations is applied to a translation unit
 * sequentially. The last transformation decides the outcome whether
 * the code has been changed.
 *
 */
class RamTransformerSequence : public RamMetaTransformer {
public:
    template <typename... Tfs>
    RamTransformerSequence(std::unique_ptr<Tfs>&&... tf) : RamTransformerSequence() {
        std::unique_ptr<RamTransformer> tmp[] = {std::move(tf)...};
        for (auto& cur : tmp) {
            transformers.emplace_back(std::move(cur));
        }
        for (const auto& cur : transformers) {
            (void)cur;
            assert(cur);
        }
    }
    RamTransformerSequence() = default;
    std::string getName() const override {
        return "RamTransformerSequence";
    }
    bool transform(RamTranslationUnit& tU) override {
        bool changed = false;
        // The last transformer decides the status
        // of the change flag.
        // Note that for other semantics, new transformer
        // sequence class needs to be introduced.
        for (auto const& cur : transformers) {
            changed = cur->apply(tU);
        }
        return changed;
    }

protected:
    /** sequence of transformers */
    std::vector<std::unique_ptr<RamTransformer>> transformers;
};

}  // end of namespace souffle
