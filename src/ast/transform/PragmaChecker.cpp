/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2017, The Souffle Developers. All rights reserved.
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file PragmaChecker.cpp
 *
 * Defines a transformer that applies pragmas found in parsed input.
 *
 ***********************************************************************/

#include "PragmaChecker.h"
#include "../Pragma.h"
#include "../Program.h"
#include "../TranslationUnit.h"
#include "../Visitor.h"
#include "Global.h"
#include <utility>
#include <vector>

namespace souffle {
bool AstPragmaChecker::transform(AstTranslationUnit& translationUnit) {
    bool changed = false;
    AstProgram* program = translationUnit.getProgram();

    // Take in pragma options from the datalog file
    visitDepthFirst(*program, [&](const AstPragma& pragma) {
        std::pair<std::string, std::string> kvp = pragma.getkvp();

        // Command line options take precedence
        if (!Global::config().has(kvp.first)) {
            changed = true;
            Global::config().set(kvp.first, kvp.second);
        }
    });

    return changed;
}
}  // end of namespace souffle
