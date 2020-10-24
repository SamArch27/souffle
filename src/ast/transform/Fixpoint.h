/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Fixpoint.h
 *
 * Transformer that repeatedly executes a sub-transformer until no changes are made
 *
 ***********************************************************************/

#pragma once

#include "ast/TranslationUnit.h"
#include "ast/transform/DebugReporter.h"
#include "ast/transform/Meta.h"
#include "ast/transform/Null.h"
#include "ast/transform/Transformer.h"
#include "souffle/utility/MiscUtil.h"
#include <memory>
#include <set>
#include <string>
#include <utility>
#include <vector>

namespace souffle::ast::transform {

/**
 * Transformer that repeatedly executes a sub-transformer until no changes are made
 */
class FixpointTransformer : public MetaTransformer {
public:
    FixpointTransformer(Own<Transformer> transformer) : transformer(std::move(transformer)) {}

    void setDebugReport() override {
        if (auto* mt = dynamic_cast<MetaTransformer*>(transformer.get())) {
            mt->setDebugReport();
        } else {
            transformer = mk<DebugReporter>(std::move(transformer));
        }
    }

    std::vector<Transformer*> getSubtransformers() const override {
        return {transformer.get()};
    }

    void setVerbosity(bool verbose) override {
        this->verbose = verbose;
        if (auto* mt = dynamic_cast<MetaTransformer*>(transformer.get())) {
            mt->setVerbosity(verbose);
        }
    }

    void disableTransformers(const std::set<std::string>& transforms) override {
        if (auto* mt = dynamic_cast<MetaTransformer*>(transformer.get())) {
            mt->disableTransformers(transforms);
        } else if (transforms.find(transformer->getName()) != transforms.end()) {
            transformer = mk<NullTransformer>();
        }
    }

    std::string getName() const override {
        return "FixpointTransformer";
    }

    FixpointTransformer* clone() const override {
        return new FixpointTransformer(souffle::clone(transformer));
    }

private:
    Own<Transformer> transformer;
    bool transform(TranslationUnit& translationUnit) override {
        bool changed = false;
        while (applySubtransformer(translationUnit, transformer.get())) {
            changed = true;
        }
        return changed;
    }
};

}  // namespace souffle::ast::transform
