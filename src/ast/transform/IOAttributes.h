/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file IOAttributes.h
 *
 * Defines AST transformation to set attribute names and types in IO
 * operations.
 *
 ***********************************************************************/

#pragma once

#include "../IO.h"
#include "../Program.h"
#include "../RecordType.h"
#include "../TranslationUnit.h"
#include "../analysis/AuxArity.h"
#include "../analysis/TypeEnvironment.h"
#include "Global.h"
#include "Transformer.h"
#include "json11.h"
#include "utility/StringUtil.h"
#include <string>
#include <vector>

namespace souffle {

/**
 * Transformation pass to set attribute names and types in IO operations.
 */
class IOAttributesTransformer : public AstTransformer {
public:
    std::string getName() const override {
        return "IOAttributesTransformer";
    }

    IOAttributesTransformer* clone() const override {
        return new IOAttributesTransformer();
    }

private:
    bool transform(AstTranslationUnit& translationUnit) override {
        bool changed = false;

        changed |= setAttributeNames(translationUnit);
        changed |= setAttributeTypes(translationUnit);
        changed |= setAttributeParams(translationUnit);

        return changed;
    }

    bool setAttributeParams(AstTranslationUnit& translationUnit) {
        bool changed = false;
        AstProgram* program = translationUnit.getProgram();
        auto auxArityAnalysis = translationUnit.getAnalysis<AuxiliaryArity>();

        for (AstIO* io : program->getIOs()) {
            AstRelation* rel = getRelation(*translationUnit.getProgram(), io->getQualifiedName());
            // Prepare type system information.
            std::vector<std::string> attributesParams;

            for (const auto* attribute : rel->getAttributes()) {
                attributesParams.push_back(attribute->getName());
            }

            // Casting due to json11.h type requirements.
            long long arity{static_cast<long long>(rel->getArity() - auxArityAnalysis->getArity(rel))};
            long long auxArity{static_cast<long long>(auxArityAnalysis->getArity(rel))};

            json11::Json relJson = json11::Json::object{{"arity", arity}, {"auxArity", auxArity},
                    {"params", json11::Json::array(attributesParams.begin(), attributesParams.end())}};

            json11::Json params = json11::Json::object{
                    {"relation", relJson}, {"records", getRecordsParams(translationUnit)}};

            io->addDirective("params", params.dump());
            changed = true;
        }
        return changed;
    }

    bool setAttributeNames(AstTranslationUnit& translationUnit) {
        bool changed = false;
        AstProgram* program = translationUnit.getProgram();
        for (AstIO* io : program->getIOs()) {
            if (io->hasDirective("attributeNames")) {
                continue;
            }
            AstRelation* rel = getRelation(*translationUnit.getProgram(), io->getQualifiedName());
            std::string delimiter("\t");
            if (io->hasDirective("delimiter")) {
                delimiter = io->getDirective("delimiter");
            }

            std::vector<std::string> attributeNames;
            for (const auto* attribute : rel->getAttributes()) {
                attributeNames.push_back(attribute->getName());
            }

            if (Global::config().has("provenance")) {
                auto auxArityAnalysis = translationUnit.getAnalysis<AuxiliaryArity>();
                std::vector<std::string> originalAttributeNames(
                        attributeNames.begin(), attributeNames.end() - auxArityAnalysis->getArity(rel));
                io->addDirective("attributeNames", toString(join(originalAttributeNames, delimiter)));
            } else {
                io->addDirective("attributeNames", toString(join(attributeNames, delimiter)));
            }
            changed = true;
        }
        return changed;
    }

    bool setAttributeTypes(AstTranslationUnit& translationUnit) {
        bool changed = false;
        AstProgram* program = translationUnit.getProgram();
        auto auxArityAnalysis = translationUnit.getAnalysis<AuxiliaryArity>();
        auto typeEnv = &translationUnit.getAnalysis<TypeEnvironmentAnalysis>()->getTypeEnvironment();

        for (AstIO* io : program->getIOs()) {
            AstRelation* rel = getRelation(*translationUnit.getProgram(), io->getQualifiedName());
            // Prepare type system information.
            std::vector<std::string> attributesTypes;

            for (const auto* attribute : rel->getAttributes()) {
                auto typeName = attribute->getTypeName();
                auto type = getTypeQualifier(typeEnv->getType(typeName));
                attributesTypes.push_back(type);
            }

            // Casting due to json11.h type requirements.
            long long arity{static_cast<long long>(rel->getArity() - auxArityAnalysis->getArity(rel))};
            long long auxArity{static_cast<long long>(auxArityAnalysis->getArity(rel))};

            json11::Json relJson = json11::Json::object{{"arity", arity}, {"auxArity", auxArity},
                    {"types", json11::Json::array(attributesTypes.begin(), attributesTypes.end())}};

            json11::Json types = json11::Json::object{
                    {"relation", relJson}, {"records", getRecordsTypes(translationUnit)}};

            io->addDirective("types", types.dump());
            changed = true;
        }
        return changed;
    }

    std::string getRelationName(const AstIO* node) {
        return toString(join(node->getQualifiedName().getQualifiers(), "."));
    }

    json11::Json getRecordsTypes(AstTranslationUnit& translationUnit) const {
        static json11::Json ramRecordTypes;
        // Check if the types where already constructed
        if (!ramRecordTypes.is_null()) {
            return ramRecordTypes;
        }

        AstProgram* program = translationUnit.getProgram();
        auto typeEnv = &translationUnit.getAnalysis<TypeEnvironmentAnalysis>()->getTypeEnvironment();
        std::vector<std::string> elementTypes;
        std::map<std::string, json11::Json> records;

        // Iterate over all record types in the program populating the records map.
        for (auto* astType : program->getTypes()) {
            const auto& type = typeEnv->getType(astType->getQualifiedName());
            if (isA<RecordType>(type)) {
                elementTypes.clear();

                for (const Type* field : as<RecordType>(type)->getFields()) {
                    elementTypes.push_back(getTypeQualifier(*field));
                }
                const size_t recordArity = elementTypes.size();
                json11::Json recordInfo = json11::Json::object{
                        {"types", std::move(elementTypes)}, {"arity", static_cast<long long>(recordArity)}};
                records.emplace(getTypeQualifier(type), std::move(recordInfo));
            }
        }

        ramRecordTypes = json11::Json(records);
        return ramRecordTypes;
    }

    json11::Json getRecordsParams(AstTranslationUnit& translationUnit) const {
        static json11::Json ramRecordParams;
        // Check if the types where already constructed
        if (!ramRecordParams.is_null()) {
            return ramRecordParams;
        }

        AstProgram* program = translationUnit.getProgram();
        std::vector<std::string> elementParams;
        std::map<std::string, json11::Json> records;

        // Iterate over all record types in the program populating the records map.
        for (auto* astType : program->getTypes()) {
            if (isA<AstRecordType>(astType)) {
                elementParams.clear();

                for (const auto field : as<AstRecordType>(astType)->getFields()) {
                    elementParams.push_back(field->getName());
                }
                const size_t recordArity = elementParams.size();
                json11::Json recordInfo = json11::Json::object{
                        {"params", std::move(elementParams)}, {"arity", static_cast<long long>(recordArity)}};
                records.emplace(astType->getQualifiedName().toString(), std::move(recordInfo));
            }
        }

        ramRecordParams = json11::Json(records);
        return ramRecordParams;
    }
};

}  // namespace souffle
