/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Functor.h
 *
 * Analysis that provides type information for functors
 *
 ***********************************************************************/

#pragma once

#include "ast/IntrinsicFunctor.h"
#include "ast/Program.h"
#include "ast/UserDefinedFunctor.h"
#include "ast/analysis/Analysis.h"
#include "ast/utility/Visitor.h"
#include <memory>
#include <ostream>
#include <string>
#include <vector>

namespace souffle::ast::analysis {

class TypeAnalysis;

class FunctorAnalysis : public Analysis {
public:
    static constexpr const char* name = "functor-analysis";

    FunctorAnalysis() : Analysis(name) {}

    void run(const TranslationUnit& translationUnit) override;

    void print(std::ostream& /* os */) const override {}

    /** Return return type of functor */
    TypeAttribute getReturnType(const Functor* functor) const;

    /** Return argument type of functor */
    TypeAttribute getArgType(const Functor* functor, const size_t idx) const;

    static bool isMultiResult(const Functor& functor);

    const std::vector<TypeAttribute>& getArgTypes(const UserDefinedFunctor& udf) const;

    /** Return whether a UDF is stateful */
    bool isStateful(const UserDefinedFunctor* udf) const;

private:
    const TypeAnalysis* typeAnalysis = nullptr;
};

}  // namespace souffle::ast::analysis
