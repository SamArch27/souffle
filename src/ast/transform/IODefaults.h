/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file IODefaults.h
 *
 * Defines AST transformation to set defaults for IO operations.
 *
 ***********************************************************************/

#pragma once

#include "Global.h"
#include "ast/Directive.h"
#include "ast/Program.h"
#include "ast/QualifiedName.h"
#include "ast/TranslationUnit.h"
#include "ast/transform/Transformer.h"
#include "souffle/utility/StreamUtil.h"
#include "souffle/utility/StringUtil.h"
#include <string>
#include <vector>

namespace souffle::ast::transform {

/**
 * Transformation pass to set defaults for IO operations.
 */
class IODefaultsTransformer : public Transformer {
public:
    std::string getName() const override {
        return "IODefaultsTransformer";
    }

    IODefaultsTransformer* clone() const override {
        return new IODefaultsTransformer();
    }

private:
    bool transform(TranslationUnit& translationUnit) override {
        bool changed = false;

        changed |= setDefaults(translationUnit);

        return changed;
    }

    /**
     * Set IO defaults.
     *
     * If no IO type is specified, use 'file'
     * If no name is set, use the relation name.
     * Add the operation type to the directives list.
     * If a global fact directory is specified, add to the directives list.
     * If a global output directory is specified, add to the directives list.
     * If stdout is requested at the command line ('-D-'), change all output to stdout.
     * If a printsize operation is requested, set IO type and operation accordingly.
     *
     * @param translationUnit
     * @return true if any changes were made
     */
    bool setDefaults(TranslationUnit& translationUnit) {
        bool changed = false;
        Program* program = translationUnit.getProgram();
        for (Directive* io : program->getDirectives()) {
            // Don't do anything for a directive which
            // is not an I/O directive
            if (io->getType() == ast::DirectiveType::limitsize) continue;

            // Set a default IO of file
            if (!io->hasDirective("IO")) {
                io->addDirective("IO", "file");
                changed = true;
            }

            // Set the relation name
            if (!io->hasDirective("name")) {
                io->addDirective("name", getRelationName(io));
                changed = true;
            }

            // Set the operation type (input/output/printsize)
            if (!io->hasDirective("operation")) {
                if (io->getType() == ast::DirectiveType::input) {
                    io->addDirective("operation", "input");
                    changed = true;
                    // Configure input directory
                    if (Global::config().has("fact-dir")) {
                        io->addDirective("fact-dir", Global::config().get("fact-dir"));
                    }
                } else if (io->getType() == ast::DirectiveType::output) {
                    io->addDirective("operation", "output");
                    changed = true;
                    // Configure output directory
                    if (Global::config().has("output-dir")) {
                        if (Global::config().has("output-dir", "-")) {
                            io->addDirective("IO", "stdout");
                            io->addDirective("headers", "true");
                        } else {
                            io->addDirective("output-dir", Global::config().get("output-dir"));
                        }
                    }
                } else if (io->getType() == ast::DirectiveType::printsize) {
                    io->addDirective("operation", "printsize");
                    io->addDirective("IO", "stdoutprintsize");
                    changed = true;
                }
            }
        }

        return changed;
    }

    /**
     * Get the relation name from the qualified name.
     *
     * @return Valid relation name from the concatenated qualified name.
     */
    std::string getRelationName(const Directive* node) {
        return toString(join(node->getQualifiedName().getQualifiers(), "."));
    }
};

}  // namespace souffle::ast::transform
