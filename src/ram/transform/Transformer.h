/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Transformer.h
 *
 * Defines the interface for RAM transformation passes.
 *
 ***********************************************************************/

#pragma once

#include <string>

namespace souffle {

class RamTranslationUnit;

/**
 * @Class RamTransformer
 * @Brief abstract transformer class for a translation unit
 *
 * This is an abstract class to implement transformers. A
 * transformer takes a translation unit and changes its
 * state.
 *
 * Transformers can be composed using other transformers.
 *
 * For debugging purposes, a transformer has a name
 * (this will show up in the debug report) and a
 * protected method transform(), that performs the
 * actual transformation.
 *
 * The method apply is used to call transform() and
 * does the reporting of the debug information.
 *
 */

class RamTransformer {
public:
    virtual ~RamTransformer() = default;

    /**
     * @Brief apply the transformer to a translation unit
     * @Param translationUnit that will be transformed.
     * @Return flag reporting whether the RAM program has changed
     */
    bool apply(RamTranslationUnit& translationUnit);

    /**
     * @Brief get name of the transformer
     */
    virtual std::string getName() const = 0;

protected:
    /**
     * @Brief transform the translation unit / used by apply
     * @Param translationUnit that will be transformed.
     * @Return flag reporting whether the RAM program has changed
     */
    virtual bool transform(RamTranslationUnit& translationUnit) = 0;
};

}  // end of namespace souffle
