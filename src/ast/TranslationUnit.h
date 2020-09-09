/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file TranslationUnit.h
 *
 * Defines the translation unit class
 *
 ***********************************************************************/

#pragma once

#include "Global.h"
#include "ast/Program.h"
#include "ast/analysis/Analysis.h"
#include "ast/analysis/PrecedenceGraph.h"
#include "ast/analysis/SCCGraph.h"
#include "ast/analysis/SumTypeBranches.h"
#include "ast/analysis/Type.h"
#include "reports/DebugReport.h"
#include <map>
#include <memory>
#include <sstream>
#include <string>
#include <utility>

namespace souffle {
class ErrorReport;

/**
 * @class AstTranslationUnit
 * @brief Translation unit class for the translation pipeline
 *
 * The translation unit class consisting of
 * an symbol table, AST program, error reports, and
 * cached analysis results.
 */

class AstTranslationUnit {
public:
    AstTranslationUnit(std::unique_ptr<AstProgram> program, ErrorReport& e, DebugReport& d)
            : program(std::move(program)), errorReport(e), debugReport(d) {}

    virtual ~AstTranslationUnit() = default;

    /** get analysis: analysis is generated on the fly if not present */
    template <class Analysis>
    Analysis* getAnalysis() const {
        static const bool debug = Global::config().has("debug-report");
        std::string name = Analysis::name;
        auto it = analyses.find(name);
        if (it == analyses.end()) {
            // analysis does not exist yet, create instance and run it.
            analyses[name] = std::make_unique<Analysis>();
            analyses[name]->run(*this);
            if (debug) {
                std::stringstream ss;
                analyses[name]->print(ss);
                if (!isA<PrecedenceGraphAnalysis>(analyses[name].get()) &&
                        !isA<SCCGraphAnalysis>(analyses[name].get())) {
                    debugReport.addSection(name, "Ast Analysis [" + name + "]", ss.str());
                } else {
                    debugReport.addSection(
                            DebugReportSection(name, "Ast Analysis [" + name + "]", {}, ss.str()));
                }
            }
        }
        return dynamic_cast<Analysis*>(analyses[name].get());
    }

    /** Return the program */
    AstProgram* getProgram() {
        return program.get();
    }

    /** Return the program */
    const AstProgram* getProgram() const {
        return program.get();
    }

    /** Return error report */
    ErrorReport& getErrorReport() {
        return errorReport;
    }

    /** Return error report */
    const ErrorReport& getErrorReport() const {
        return errorReport;
    }

    /** Destroy all cached analyses of translation unit */
    void invalidateAnalyses() {
        analyses.clear();
    }

    /** Return debug report */
    DebugReport& getDebugReport() {
        return debugReport;
    }

    /** Return debug report */
    const DebugReport& getDebugReport() const {
        return debugReport;
    }

private:
    /** Cached analyses */
    mutable std::map<std::string, std::unique_ptr<AstAnalysis>> analyses;

    /** AST program */
    std::unique_ptr<AstProgram> program;

    /** Error report capturing errors while compiling */
    ErrorReport& errorReport;

    /** HTML debug report */
    DebugReport& debugReport;
};

}  // end of namespace souffle
