/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file TypeChecker.cpp
 *
 * Implementation of the type checker pass.
 *
 ***********************************************************************/

#include "ast/transform/TypeChecker.h"
#include "ast/Aggregator.h"
#include "ast/AlgebraicDataType.h"
#include "ast/Argument.h"
#include "ast/Atom.h"
#include "ast/Attribute.h"
#include "ast/BinaryConstraint.h"
#include "ast/BranchDeclaration.h"
#include "ast/BranchInit.h"
#include "ast/Clause.h"
#include "ast/Constant.h"
#include "ast/Counter.h"
#include "ast/Functor.h"
#include "ast/IntrinsicFunctor.h"
#include "ast/analysis/Functor.h"
#include "ast/analysis/PolymorphicObjects.h"
#include "ast/analysis/Type.h"
#include "ast/analysis/TypeEnvironment.h"
#include "ast/analysis/TypeSystem.h"
#include "ast/utility/Utils.h"
#include "ast/utility/Visitor.h"
#include "souffle/utility/StringUtil.h"
#include <map>
#include <sstream>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>
namespace souffle::ast::transform {

using namespace analysis;

class TypeDeclarationChecker {
public:
    TypeDeclarationChecker(TranslationUnit& tu) : tu(tu){};
    void run();

private:
    TranslationUnit& tu;
    ErrorReport& report = tu.getErrorReport();
    const Program& program = tu.getProgram();
    const TypeEnvironmentAnalysis& typeEnvAnalysis = *tu.getAnalysis<TypeEnvironmentAnalysis>();
    const TypeEnvironment& typeEnv = typeEnvAnalysis.getTypeEnvironment();

    void checkRecordType(const ast::RecordType& type);
    void checkSubsetType(const ast::SubsetType& type);
    void checkUnionType(const ast::UnionType& type);
    void checkADT(const ast::AlgebraicDataType& type);
};

class TypeCheckerImpl : Visitor<void> {
public:
    TypeCheckerImpl(TranslationUnit& tu) : tu(tu){};

    /** Analyse types, clause by clause */
    void run() {
        const Program& program = tu.getProgram();
        for (auto* clause : program.getClauses()) {
            visitDepthFirstPreOrder(*clause, *this);
        }
    }

private:
    TranslationUnit& tu;
    ErrorReport& report = tu.getErrorReport();
    const TypeAnalysis& typeAnalysis = *tu.getAnalysis<TypeAnalysis>();
    const TypeEnvironment& typeEnv = tu.getAnalysis<TypeEnvironmentAnalysis>()->getTypeEnvironment();
    const FunctorAnalysis& functorAnalysis = *tu.getAnalysis<FunctorAnalysis>();
    const PolymorphicObjectsAnalysis& polyAnalysis = *tu.getAnalysis<PolymorphicObjectsAnalysis>();
    const Program& program = tu.getProgram();

    std::unordered_set<const Atom*> negatedAtoms;

    /** Collect negated atoms */
    void visitNegation(const Negation& neg) override;

    /* Type checks */
    /** Check if declared types of the relation match deduced types. */
    void visitAtom(const Atom& atom) override;
    void visitVariable(const Variable& var) override;
    void visitStringConstant(const StringConstant& constant) override;
    void visitNumericConstant(const NumericConstant& constant) override;
    void visitNilConstant(const NilConstant& constant) override;
    void visitRecordInit(const RecordInit& rec) override;
    void visitBranchInit(const BranchInit& adt) override;
    void visitTypeCast(const ast::TypeCast& cast) override;
    void visitIntrinsicFunctor(const IntrinsicFunctor& fun) override;
    void visitUserDefinedFunctor(const UserDefinedFunctor& fun) override;
    void visitBinaryConstraint(const BinaryConstraint& constraint) override;
    void visitAggregator(const Aggregator& aggregator) override;
};

void TypeChecker::verify(TranslationUnit& tu) {
    auto& report = tu.getErrorReport();
    auto errorsBeforeDeclarationsCheck = report.getNumErrors();

    TypeDeclarationChecker{tu}.run();

    // Run type checker only if type declarations are valid.
    if (report.getNumErrors() == errorsBeforeDeclarationsCheck) {
        TypeCheckerImpl{tu}.run();
    }
}

void TypeDeclarationChecker::checkUnionType(const ast::UnionType& type) {
    // check presence of all the element types and that all element types are based off a primitive
    for (const QualifiedName& sub : type.getTypes()) {
        if (typeEnv.isPrimitiveType(sub)) {
            continue;
        }
        const ast::Type* subtype = getIf(
                program.getTypes(), [&](const ast::Type* type) { return type->getQualifiedName() == sub; });
        if (subtype == nullptr) {
            report.addError(tfm::format("Undefined type %s in definition of union type %s", sub,
                                    type.getQualifiedName()),
                    type.getSrcLoc());
        } else if (!isA<ast::UnionType>(subtype) && !isA<ast::SubsetType>(subtype)) {
            report.addError(tfm::format("Union type %s contains the non-primitive type %s",
                                    type.getQualifiedName(), sub),
                    type.getSrcLoc());
        }
    }

    // Check if the union is recursive.
    if (typeEnvAnalysis.isCyclic(type.getQualifiedName())) {
        report.addError("Infinite descent in the definition of type " + toString(type.getQualifiedName()),
                type.getSrcLoc());
    }

    /* check that union types do not mix different primitive types */
    for (const auto* type : program.getTypes()) {
        // We are only interested in unions here.
        if (!isA<ast::UnionType>(type)) {
            continue;
        }

        const auto& name = type->getQualifiedName();

        const auto& predefinedTypesInUnion = typeEnvAnalysis.getPrimitiveTypesInUnion(name);

        // Report error (if size == 0, then the union is cyclic)
        if (predefinedTypesInUnion.size() > 1) {
            report.addError(
                    tfm::format("Union type %s is defined over {%s} (multiple primitive types in union)",
                            name, join(predefinedTypesInUnion, ", ")),
                    type->getSrcLoc());
        }
    }
}

void TypeDeclarationChecker::checkRecordType(const ast::RecordType& type) {
    auto&& fields = type.getFields();
    // check proper definition of all field types
    for (auto&& field : fields) {
        if (!typeEnv.isType(field->getTypeName())) {
            report.addError(tfm::format("Undefined type %s in definition of field %s", field->getTypeName(),
                                    field->getName()),
                    field->getSrcLoc());
        }
    }

    // check that field names are unique
    for (std::size_t i = 0; i < fields.size(); i++) {
        auto&& cur_name = fields[i]->getName();
        for (std::size_t j = 0; j < i; j++) {
            if (fields[j]->getName() == cur_name) {
                report.addError(tfm::format("Doubly defined field name %s in definition of type %s", cur_name,
                                        type.getQualifiedName()),
                        fields[i]->getSrcLoc());
            }
        }
    }
}

void TypeDeclarationChecker::checkADT(const ast::AlgebraicDataType& type) {
    // check if all branches contain properly defined types.
    for (auto* branch : type.getBranches()) {
        for (auto* field : branch->getFields()) {
            if (!typeEnv.isType(field->getTypeName())) {
                report.addError(tfm::format("Undefined type %s in definition of branch %s",
                                        field->getTypeName(), branch->getConstructor()),
                        field->getSrcLoc());
            }
        }
    }
}

void TypeDeclarationChecker::checkSubsetType(const ast::SubsetType& astType) {
    if (typeEnvAnalysis.isCyclic(astType.getQualifiedName())) {
        report.addError(
                tfm::format("Infinite descent in the definition of type %s", astType.getQualifiedName()),
                astType.getSrcLoc());
        return;
    }

    if (!typeEnv.isType(astType.getBaseType())) {
        report.addError(tfm::format("Undefined base type %s in definition of type %s", astType.getBaseType(),
                                astType.getQualifiedName()),
                astType.getSrcLoc());
        return;
    }

    auto& rootType = typeEnv.getType(astType.getBaseType());

    if (isA<analysis::UnionType>(rootType)) {
        report.addError(tfm::format("Subset type %s can't be derived from union %s",
                                astType.getQualifiedName(), rootType.getName()),
                astType.getSrcLoc());
    }

    if (isA<analysis::RecordType>(rootType)) {
        report.addError(tfm::format("Subset type %s can't be derived from record type %s",
                                astType.getQualifiedName(), rootType.getName()),
                astType.getSrcLoc());
    }
}

void TypeDeclarationChecker::run() {
    // The redefinitions of types is checked by checkNamespaces in SemanticChecker
    for (auto* type : program.getTypes()) {
        if (typeEnv.isPrimitiveType(type->getQualifiedName())) {
            report.addError("Redefinition of the predefined type", type->getSrcLoc());
            continue;
        }

        if (isA<ast::UnionType>(type)) {
            checkUnionType(*as<ast::UnionType>(type));
        } else if (isA<ast::RecordType>(type)) {
            checkRecordType(*as<ast::RecordType>(type));
        } else if (isA<ast::SubsetType>(type)) {
            checkSubsetType(*as<ast::SubsetType>(type));
        } else if (isA<ast::AlgebraicDataType>(type)) {
            checkADT(*as<ast::AlgebraicDataType>(type));
        } else {
            fatal("unsupported type construct: %s", typeid(type).name());
        }
    }

    // Check if all the branch names are unique in sum types.
    std::map<std::string, std::vector<SrcLocation>> branchToLocation;
    visitDepthFirst(program.getTypes(), [&](const ast::AlgebraicDataType& type) {
        for (auto* branch : type.getBranches()) {
            branchToLocation[branch->getConstructor()].push_back(branch->getSrcLoc());
        }
    });

    for (auto& branchLocs : branchToLocation) {
        auto& branch = branchLocs.first;
        auto& locs = branchLocs.second;

        // If a branch is used only once, then everything is fine.
        if (locs.size() == 1) continue;

        auto primaryDiagnostic =
                DiagnosticMessage(tfm::format("Branch %s is defined multiple times", branch));

        std::vector<DiagnosticMessage> branchDeclarations;
        for (auto& loc : locs) {
            branchDeclarations.push_back(DiagnosticMessage(tfm::format("Branch %s defined", branch), loc));
        }

        report.addDiagnostic(Diagnostic(
                Diagnostic::Type::ERROR, std::move(primaryDiagnostic), std::move(branchDeclarations)));
    }
}

void TypeCheckerImpl::visitAtom(const Atom& atom) {
    auto relation = getAtomRelation(&atom, &program);
    if (relation == nullptr) {
        return;  // error unrelated to types.
    }

    auto attributes = relation->getAttributes();
    auto arguments = atom.getArguments();
    if (attributes.size() != arguments.size()) {
        return;  // error in input program
    }

    for (size_t i = 0; i < attributes.size(); ++i) {
        auto& typeName = attributes[i]->getTypeName();
        if (!typeEnv.isType(typeName)) {
            continue;
        }

        auto argTypes = typeAnalysis.getTypes(arguments[i]);
        auto& attributeType = typeEnv.getType(typeName);

        if (argTypes.isAll() || argTypes.empty()) {
            continue;  // This will be reported later.
        }

        // We consider two cases: negated and not negated atoms.
        // Negated atom have to agree in kind, non-negated atom need to follow source/sink rules.
        if (negatedAtoms.count(&atom) == 0) {
            // Attribute and argument type agree if, argument type is a subtype of declared type
            // or is of the appropriate constant type or the (constant) record type.
            bool validAttribute = all_of(argTypes, [&attributeType](const analysis::Type& type) {
                if (isSubtypeOf(type, attributeType)) return true;
                if (!isSubtypeOf(attributeType, type)) return false;
                if (isA<ConstantType>(type)) return true;
                return isA<analysis::RecordType>(type) && !isA<analysis::SubsetType>(type);
            });

            if (!validAttribute && !Global::config().has("legacy")) {
                auto primaryDiagnostic =
                        DiagnosticMessage("Atom's argument type is not a subtype of its declared type",
                                arguments[i]->getSrcLoc());

                auto declaredTypeInfo =
                        DiagnosticMessage(tfm::format("The argument's declared type is %s", typeName),
                                attributes[i]->getSrcLoc());

                report.addDiagnostic(Diagnostic(Diagnostic::Type::ERROR, std::move(primaryDiagnostic),
                        {std::move(declaredTypeInfo)}));
            }
        } else {  // negation case.
            // Declared attribute and deduced type agree if:
            // They are the same type, or
            // They are derived from the same constant type.
            bool validAttribute = all_of(argTypes, [&](const analysis::Type& type) {
                return type == attributeType || any_of(typeEnv.getConstantTypes(), [&](auto& constantType) {
                    return isSubtypeOf(attributeType, constantType) && isSubtypeOf(type, constantType);
                });
            });

            if (!validAttribute) {
                auto primaryDiagnostic =
                        DiagnosticMessage("The kind of atom's argument doesn't match the declared type kind",
                                arguments[i]->getSrcLoc());
                auto declaredTypeInfo =
                        DiagnosticMessage(tfm::format("The argument's declared type is %s", typeName),
                                attributes[i]->getSrcLoc());
                report.addDiagnostic(Diagnostic(Diagnostic::Type::ERROR, std::move(primaryDiagnostic),
                        {std::move(declaredTypeInfo)}));
            }
        }
    }
}

void TypeCheckerImpl::visitVariable(const ast::Variable& var) {
    if (typeAnalysis.getTypes(&var).empty()) {
        report.addError("Unable to deduce type for variable " + var.getName(), var.getSrcLoc());
    }
}

void TypeCheckerImpl::visitStringConstant(const StringConstant& constant) {
    TypeSet types = typeAnalysis.getTypes(&constant);
    if (!isOfKind(types, TypeAttribute::Symbol)) {
        report.addError("Symbol constant (type mismatch)", constant.getSrcLoc());
    }
}

void TypeCheckerImpl::visitNumericConstant(const NumericConstant& constant) {
    TypeSet types = typeAnalysis.getTypes(&constant);

    // No type could be assigned.
    if (polyAnalysis.hasInvalidType(&constant)) {
        report.addError("Ambiguous constant (unable to deduce type)", constant.getSrcLoc());
        return;
    }

    switch (polyAnalysis.getInferredType(&constant)) {
        case NumericConstant::Type::Int:
            if (!isOfKind(types, TypeAttribute::Signed)) {
                report.addError("Number constant (type mismatch)", constant.getSrcLoc());
            }
            break;
        case NumericConstant::Type::Uint:
            if (!isOfKind(types, TypeAttribute::Unsigned)) {
                report.addError("Unsigned constant (type mismatch)", constant.getSrcLoc());
            }
            break;
        case NumericConstant::Type::Float:
            if (!isOfKind(types, TypeAttribute::Float)) {
                report.addError("Float constant (type mismatch)", constant.getSrcLoc());
            }
            break;
    }
}

void TypeCheckerImpl::visitNilConstant(const NilConstant& constant) {
    TypeSet types = typeAnalysis.getTypes(&constant);
    if (!isOfKind(types, TypeAttribute::Record)) {
        report.addError("Nil constant used as a non-record", constant.getSrcLoc());
        return;
    }
}

void TypeCheckerImpl::visitRecordInit(const RecordInit& rec) {
    TypeSet types = typeAnalysis.getTypes(&rec);

    if (!isOfKind(types, TypeAttribute::Record) || types.size() != 1) {
        report.addError("Ambiguous record", rec.getSrcLoc());
        return;
    }

    // At this point we know that there is exactly one type in set, so we can take it.
    auto& recordType = *as<analysis::RecordType>(*types.begin());

    if (recordType.getFields().size() != rec.getArguments().size()) {
        report.addError("Wrong number of arguments given to record", rec.getSrcLoc());
        return;
    }
}

void TypeCheckerImpl::visitBranchInit(const BranchInit& adt) {
    TypeSet types = typeAnalysis.getTypes(&adt);

    if (!isOfKind(types, TypeAttribute::ADT) || types.isAll() || types.size() != 1) {
        report.addError("Ambiguous branch", adt.getSrcLoc());
        return;
    }

    // We know now that the set "types" is a singleton
    auto& sumType = *as<analysis::AlgebraicDataType>(*types.begin());

    auto& argsDeclaredTypes = sumType.getBranchTypes(adt.getConstructor());
    auto args = adt.getArguments();

    if (argsDeclaredTypes.size() != args.size()) {
        // Invalid branchInit arity, handled by checkBranchInits.
        return;
    }

    for (size_t i = 0; i < args.size(); ++i) {
        auto argTypes = typeAnalysis.getTypes(args[i]);
        bool correctType = all_of(
                argTypes, [&](const analysis::Type& t) { return isSubtypeOf(t, *argsDeclaredTypes[i]); });
        if (!correctType) {
            // TODO (darth_tytus): Give better error
            report.addError("Branch argument's type doesn't match its declared type", args[i]->getSrcLoc());
        }
    }
}

void TypeCheckerImpl::visitTypeCast(const ast::TypeCast& cast) {
    if (!typeEnv.isType(cast.getType())) {
        report.addError(
                tfm::format("Type cast to the undeclared type \"%s\"", cast.getType()), cast.getSrcLoc());
        return;
    }

    auto& castTypes = typeAnalysis.getTypes(&cast);
    auto& argTypes = typeAnalysis.getTypes(cast.getValue());

    if (castTypes.isAll() || castTypes.size() != 1) {
        report.addError("Unable to deduce type of the argument (cast)", cast.getSrcLoc());
        return;
    }

    // This should be reported elsewhere
    if (argTypes.isAll() || castTypes.size() != 1 || argTypes.isAll() || argTypes.size() != 1) {
        return;
    }
}

void TypeCheckerImpl::visitIntrinsicFunctor(const IntrinsicFunctor& fun) {
    if (!typeAnalysis.hasValidTypeInfo(&fun)) {
        auto args = fun.getArguments();
        if (!isValidFunctorOpArity(fun.getBaseFunctionOp(), args.size())) {
            report.addError("invalid overload (arity mismatch)", fun.getSrcLoc());
            return;
        }
        assert(typeAnalysis.getValidIntrinsicFunctorOverloads(fun).empty() &&
                "unexpected type analysis result");
        report.addError("no valid overloads", fun.getSrcLoc());
    }
}

void TypeCheckerImpl::visitUserDefinedFunctor(const UserDefinedFunctor& fun) {
    // check type of result
    const TypeSet& resultType = typeAnalysis.getTypes(&fun);

    TypeAttribute returnType;
    try {
        returnType = functorAnalysis.getReturnType(&fun);
    } catch (...) {
        report.addError("Undeclared user functor", fun.getSrcLoc());
        return;
    }

    if (!isOfKind(resultType, returnType)) {
        switch (returnType) {
            case TypeAttribute::Signed:
                report.addError("Non-numeric use for numeric functor", fun.getSrcLoc());
                break;
            case TypeAttribute::Unsigned:
                report.addError("Non-unsigned use for unsigned functor", fun.getSrcLoc());
                break;
            case TypeAttribute::Float:
                report.addError("Non-float use for float functor", fun.getSrcLoc());
                break;
            case TypeAttribute::Symbol:
                report.addError("Non-symbolic use for symbolic functor", fun.getSrcLoc());
                break;
            case TypeAttribute::Record: fatal("Invalid return type");
            case TypeAttribute::ADT: fatal("Invalid return type");
        }
    }

    size_t i = 0;
    for (auto arg : fun.getArguments()) {
        TypeAttribute argType = functorAnalysis.getArgType(&fun, i);
        if (!isOfKind(typeAnalysis.getTypes(arg), argType)) {
            switch (argType) {
                case TypeAttribute::Signed:
                    report.addError("Non-numeric argument for functor", arg->getSrcLoc());
                    break;
                case TypeAttribute::Symbol:
                    report.addError("Non-symbolic argument for functor", arg->getSrcLoc());
                    break;
                case TypeAttribute::Unsigned:
                    report.addError("Non-unsigned argument for functor", arg->getSrcLoc());
                    break;
                case TypeAttribute::Float:
                    report.addError("Non-float argument for functor", arg->getSrcLoc());
                    break;
                case TypeAttribute::Record: fatal("Invalid argument type");
                case TypeAttribute::ADT: fatal("Invalid argument type");
            }
        }
        ++i;
    }
}

void TypeCheckerImpl::visitBinaryConstraint(const BinaryConstraint& constraint) {
    auto op = polyAnalysis.getOverloadedOperator(&constraint);
    auto left = constraint.getLHS();
    auto right = constraint.getRHS();
    auto opTypesAttrs = getBinaryConstraintTypes(op);

    auto leftTypes = typeAnalysis.getTypes(left);
    auto rightTypes = typeAnalysis.getTypes(right);

    // Skip checks if either side could not be fully deduced
    // The unable-to-deduce-type checker will point out the issue.
    if (leftTypes.isAll() || leftTypes.size() != 1) return;
    if (rightTypes.isAll() || rightTypes.size() != 1) return;

    // Extract types from singleton sets.
    auto& leftType = *typeAnalysis.getTypes(left).begin();
    auto& rightType = *typeAnalysis.getTypes(right).begin();

    // give them a slightly nicer error
    if (isOrderedBinaryConstraintOp(op) && !areEquivalentTypes(leftType, rightType)) {
        report.addError("Cannot compare different types", constraint.getSrcLoc());
    } else {
        auto checkTyAttr = [&](Argument const& side) {
            auto opMatchesType = any_of(opTypesAttrs,
                    [&](auto& typeAttr) { return isOfKind(typeAnalysis.getTypes(&side), typeAttr); });

            if (!opMatchesType) {
                std::stringstream ss;
                ss << "Constraint requires an operand of type "
                   << join(opTypesAttrs, " or ", [&](auto& out, auto& typeAttr) {
                          switch (typeAttr) {
                              case TypeAttribute::Signed: out << "`number`"; break;
                              case TypeAttribute::Symbol: out << "`symbol`"; break;
                              case TypeAttribute::Unsigned: out << "`unsigned`"; break;
                              case TypeAttribute::Float: out << "`float`"; break;
                              case TypeAttribute::Record: out << "a record"; break;
                              case TypeAttribute::ADT: out << "a sum"; break;
                          }
                      });
                report.addError(ss.str(), side.getSrcLoc());
            }
        };

        checkTyAttr(*left);
        checkTyAttr(*right);
    }
}

void TypeCheckerImpl::visitAggregator(const Aggregator& aggregator) {
    auto op = polyAnalysis.getOverloadedOperator(&aggregator);

    auto aggregatorType = typeAnalysis.getTypes(&aggregator);

    TypeAttribute opType = getTypeAttributeAggregate(op);

    // Check if operation type and return type agree.
    if (!isOfKind(aggregatorType, opType)) {
        report.addError("Couldn't assign types to the aggregator", aggregator.getSrcLoc());
    }
}

void TypeCheckerImpl::visitNegation(const Negation& neg) {
    negatedAtoms.insert(neg.getAtom());
}

}  // namespace souffle::ast::transform
