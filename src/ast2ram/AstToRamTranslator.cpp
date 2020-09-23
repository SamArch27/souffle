/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file AstToRamTranslator.cpp
 *
 * Translator from AST to RAM structures.
 *
 ***********************************************************************/

#include "ast2ram/AstToRamTranslator.h"
#include "FunctorOps.h"
#include "Global.h"
#include "LogStatement.h"
#include "RelationTag.h"
#include "ast/Aggregator.h"
#include "ast/Argument.h"
#include "ast/Atom.h"
#include "ast/Attribute.h"
#include "ast/BinaryConstraint.h"
#include "ast/Clause.h"
#include "ast/Constant.h"
#include "ast/Constraint.h"
#include "ast/Counter.h"
#include "ast/Directive.h"
#include "ast/ExecutionOrder.h"
#include "ast/ExecutionPlan.h"
#include "ast/Functor.h"
#include "ast/IntrinsicFunctor.h"
#include "ast/Literal.h"
#include "ast/Negation.h"
#include "ast/NilConstant.h"
#include "ast/Node.h"
#include "ast/NumericConstant.h"
#include "ast/Program.h"
#include "ast/ProvenanceNegation.h"
#include "ast/QualifiedName.h"
#include "ast/RecordInit.h"
#include "ast/Relation.h"
#include "ast/StringConstant.h"
#include "ast/SubroutineArgument.h"
#include "ast/TranslationUnit.h"
#include "ast/UnnamedVariable.h"
#include "ast/UserDefinedFunctor.h"
#include "ast/Variable.h"
#include "ast/analysis/AuxArity.h"
#include "ast/analysis/IOType.h"
#include "ast/analysis/RecursiveClauses.h"
#include "ast/analysis/RelationDetailCache.h"
#include "ast/analysis/RelationSchedule.h"
#include "ast/analysis/SCCGraph.h"
#include "ast/analysis/TopologicallySortedSCCGraph.h"
#include "ast/analysis/TypeEnvironment.h"
#include "ast/analysis/TypeSystem.h"
#include "ast/transform/ReorderLiterals.h"
#include "ast/utility/NodeMapper.h"
#include "ast/utility/Utils.h"
#include "ast/utility/Visitor.h"
#include "parser/SrcLocation.h"
#include "ram/Aggregate.h"
#include "ram/AutoIncrement.h"
#include "ram/Break.h"
#include "ram/Call.h"
#include "ram/Clear.h"
#include "ram/Condition.h"
#include "ram/Conjunction.h"
#include "ram/Constraint.h"
#include "ram/DebugInfo.h"
#include "ram/EmptinessCheck.h"
#include "ram/ExistenceCheck.h"
#include "ram/Exit.h"
#include "ram/Expression.h"
#include "ram/Extend.h"
#include "ram/Filter.h"
#include "ram/FloatConstant.h"
#include "ram/IO.h"
#include "ram/IntrinsicOperator.h"
#include "ram/LogRelationTimer.h"
#include "ram/LogSize.h"
#include "ram/LogTimer.h"
#include "ram/Loop.h"
#include "ram/Negation.h"
#include "ram/NestedIntrinsicOperator.h"
#include "ram/Node.h"
#include "ram/Operation.h"
#include "ram/PackRecord.h"
#include "ram/Parallel.h"
#include "ram/Program.h"
#include "ram/Project.h"
#include "ram/ProvenanceExistenceCheck.h"
#include "ram/Query.h"
#include "ram/Relation.h"
#include "ram/RelationSize.h"
#include "ram/Scan.h"
#include "ram/Sequence.h"
#include "ram/SignedConstant.h"
#include "ram/Statement.h"
#include "ram/SubroutineArgument.h"
#include "ram/SubroutineReturn.h"
#include "ram/Swap.h"
#include "ram/TranslationUnit.h"
#include "ram/True.h"
#include "ram/TupleElement.h"
#include "ram/UndefValue.h"
#include "ram/UnpackRecord.h"
#include "ram/UnsignedConstant.h"
#include "ram/UserDefinedOperator.h"
#include "ram/Utils.h"
#include "reports/DebugReport.h"
#include "reports/ErrorReport.h"
#include "souffle/BinaryConstraintOps.h"
#include "souffle/TypeAttribute.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/FunctionalUtil.h"
#include <algorithm>
#include <cassert>
#include <chrono>
#include <cstddef>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <sstream>
#include <vector>

namespace souffle {

/** append statement to a list of statements */
inline void appendStmt(VecOwn<ram::Statement>& stmtList, Own<ram::Statement> stmt) {
    if (stmt) {
        stmtList.push_back(std::move(stmt));
    }
}

Own<ram::TupleElement> AstToRamTranslator::makeRamTupleElement(const Location& loc) {
    return mk<ram::TupleElement>(loc.identifier, loc.element);
}

size_t AstToRamTranslator::getEvaluationArity(const ast::Atom* atom) const {
    if (atom->getQualifiedName().toString().find("@delta_") == 0) {
        const ast::QualifiedName& originalRel =
                ast::QualifiedName(atom->getQualifiedName().toString().substr(7));
        return auxArityAnalysis->getArity(getRelation(*program, originalRel));
    } else if (atom->getQualifiedName().toString().find("@new_") == 0) {
        const ast::QualifiedName& originalRel =
                ast::QualifiedName(atom->getQualifiedName().toString().substr(5));
        return auxArityAnalysis->getArity(getRelation(*program, originalRel));
    } else if (atom->getQualifiedName().toString().find("@info_") == 0) {
        return 0;
    } else {
        return auxArityAnalysis->getArity(atom);
    }
}

std::vector<std::map<std::string, std::string>> AstToRamTranslator::getInputDirectives(
        const ast::Relation* rel) {
    std::vector<std::map<std::string, std::string>> inputDirectives;

    for (const auto* load : program->getDirectives()) {
        if (load->getQualifiedName() != rel->getQualifiedName() ||
                load->getType() != ast::DirectiveType::input) {
            continue;
        }

        std::map<std::string, std::string> directives;
        for (const auto& currentPair : load->getParameters()) {
            directives.insert(std::make_pair(currentPair.first, unescape(currentPair.second)));
        }
        inputDirectives.push_back(directives);
    }

    if (inputDirectives.empty()) {
        inputDirectives.emplace_back();
    }

    return inputDirectives;
}

std::vector<std::map<std::string, std::string>> AstToRamTranslator::getOutputDirectives(
        const ast::Relation* rel) {
    std::vector<std::map<std::string, std::string>> outputDirectives;

    for (const auto* store : program->getDirectives()) {
        if (store->getQualifiedName() != rel->getQualifiedName() ||
                (store->getType() != ast::DirectiveType::printsize &&
                        store->getType() != ast::DirectiveType::output)) {
            continue;
        }

        std::map<std::string, std::string> directives;
        for (const auto& currentPair : store->getParameters()) {
            directives.insert(std::make_pair(currentPair.first, unescape(currentPair.second)));
        }
        outputDirectives.push_back(directives);
    }

    if (outputDirectives.empty()) {
        outputDirectives.emplace_back();
    }

    return outputDirectives;
}

Own<ram::RelationReference> AstToRamTranslator::createRelationReference(const std::string name) {
    auto it = ramRels.find(name);
    assert(it != ramRels.end() && "relation name not found");

    const ram::Relation* relation = it->second.get();
    return mk<ram::RelationReference>(relation);
}

Own<ram::RelationReference> AstToRamTranslator::translateRelation(const ast::Atom* atom) {
    return createRelationReference(getRelationName(atom->getQualifiedName()));
}

Own<ram::RelationReference> AstToRamTranslator::translateRelation(
        const ast::Relation* rel, const std::string relationNamePrefix) {
    return createRelationReference(relationNamePrefix + getRelationName(rel->getQualifiedName()));
}

Own<ram::RelationReference> AstToRamTranslator::translateDeltaRelation(const ast::Relation* rel) {
    return translateRelation(rel, "@delta_");
}

Own<ram::RelationReference> AstToRamTranslator::translateNewRelation(const ast::Relation* rel) {
    return translateRelation(rel, "@new_");
}

Own<ram::Expression> AstToRamTranslator::translateValue(const ast::Argument* arg, const ValueIndex& index) {
    if (arg == nullptr) {
        return nullptr;
    }

    class ValueTranslator : public ast::Visitor<Own<ram::Expression>> {
        AstToRamTranslator& translator;
        const ValueIndex& index;

    public:
        ValueTranslator(AstToRamTranslator& translator, const ValueIndex& index)
                : translator(translator), index(index) {}

        Own<ram::Expression> visitVariable(const ast::Variable& var) override {
            assert(index.isDefined(var) && "variable not grounded");
            return makeRamTupleElement(index.getDefinitionPoint(var));
        }

        Own<ram::Expression> visitUnnamedVariable(const ast::UnnamedVariable&) override {
            return mk<ram::UndefValue>();
        }

        Own<ram::Expression> visitNumericConstant(const ast::NumericConstant& c) override {
            assert(c.getType().has_value() && "At this points all constants should have type.");

            switch (*c.getType()) {
                case ast::NumericConstant::Type::Int:
                    return mk<ram::SignedConstant>(RamSignedFromString(c.getConstant(), nullptr, 0));
                case ast::NumericConstant::Type::Uint:
                    return mk<ram::UnsignedConstant>(RamUnsignedFromString(c.getConstant(), nullptr, 0));
                case ast::NumericConstant::Type::Float:
                    return mk<ram::FloatConstant>(RamFloatFromString(c.getConstant()));
            }

            fatal("unexpected numeric constant type");
        }

        Own<ram::Expression> visitStringConstant(const ast::StringConstant& c) override {
            return mk<ram::SignedConstant>(translator.getSymbolTable().lookup(c.getConstant()));
        }

        Own<ram::Expression> visitNilConstant(const ast::NilConstant&) override {
            return mk<ram::SignedConstant>(0);
        }

        Own<ram::Expression> visitIntrinsicFunctor(const ast::IntrinsicFunctor& inf) override {
            VecOwn<ram::Expression> values;
            for (const auto& cur : inf.getArguments()) {
                values.push_back(translator.translateValue(cur, index));
            }

            auto* info = inf.getFunctionInfo();
            assert(info && "no overload picked for instrinsic; missing transform pass?");
            if (info->multipleResults) {
                return translator.makeRamTupleElement(index.getGeneratorLoc(inf));
            } else {
                return mk<ram::IntrinsicOperator>(info->op, std::move(values));
            }
        }

        Own<ram::Expression> visitUserDefinedFunctor(const ast::UserDefinedFunctor& udf) override {
            // Sanity check.
            assert(udf.getArguments().size() == udf.getArgsTypes().size());

            VecOwn<ram::Expression> values;
            for (const auto& cur : udf.getArguments()) {
                values.push_back(translator.translateValue(cur, index));
            }

            return mk<ram::UserDefinedOperator>(udf.getName(), udf.getArgsTypes(), udf.getReturnType(),
                    udf.isStateful(), std::move(values));
        }

        Own<ram::Expression> visitCounter(const ast::Counter&) override {
            return mk<ram::AutoIncrement>();
        }

        Own<ram::Expression> visitRecordInit(const ast::RecordInit& init) override {
            VecOwn<ram::Expression> values;
            for (const auto& cur : init.getArguments()) {
                values.push_back(translator.translateValue(cur, index));
            }
            return mk<ram::PackRecord>(std::move(values));
        }

        Own<ram::Expression> visitAggregator(const ast::Aggregator& agg) override {
            // here we look up the location the aggregation result gets bound
            return translator.makeRamTupleElement(index.getGeneratorLoc(agg));
        }

        Own<ram::Expression> visitSubroutineArgument(const ast::SubroutineArgument& subArg) override {
            return mk<ram::SubroutineArgument>(subArg.getNumber());
        }
    };

    return ValueTranslator(*this, index)(*arg);
}

Own<ram::Condition> AstToRamTranslator::translateConstraint(
        const ast::Literal* lit, const ValueIndex& index) {
    class ConstraintTranslator : public ast::Visitor<Own<ram::Condition>> {
        AstToRamTranslator& translator;
        const ValueIndex& index;

    public:
        ConstraintTranslator(AstToRamTranslator& translator, const ValueIndex& index)
                : translator(translator), index(index) {}

        /** for atoms */
        Own<ram::Condition> visitAtom(const ast::Atom&) override {
            return nullptr;  // covered already within the scan/lookup generation step
        }

        /** for binary relations */
        Own<ram::Condition> visitBinaryConstraint(const ast::BinaryConstraint& binRel) override {
            auto valLHS = translator.translateValue(binRel.getLHS(), index);
            auto valRHS = translator.translateValue(binRel.getRHS(), index);
            return mk<ram::Constraint>(binRel.getOperator(), std::move(valLHS), std::move(valRHS));
        }

        /** for provenance negation */
        Own<ram::Condition> visitProvenanceNegation(const ast::ProvenanceNegation& neg) override {
            const auto* atom = neg.getAtom();
            size_t auxiliaryArity = translator.getEvaluationArity(atom);
            assert(auxiliaryArity <= atom->getArity() && "auxiliary arity out of bounds");
            size_t arity = atom->getArity() - auxiliaryArity;
            VecOwn<ram::Expression> values;

            auto args = atom->getArguments();
            for (size_t i = 0; i < arity; i++) {
                values.push_back(translator.translateValue(args[i], index));
            }
            // we don't care about the provenance columns when doing the existence check
            if (Global::config().has("provenance")) {
                // undefined value for rule number
                values.push_back(mk<ram::UndefValue>());
                // add the height annotation for provenanceNotExists
                for (size_t height = 1; height < auxiliaryArity; height++) {
                    values.push_back(translator.translateValue(args[arity + height], index));
                }
            }
            return mk<ram::Negation>(
                    mk<ram::ProvenanceExistenceCheck>(translator.translateRelation(atom), std::move(values)));
        }

        /** for negations */
        Own<ram::Condition> visitNegation(const ast::Negation& neg) override {
            const auto* atom = neg.getAtom();
            size_t auxiliaryArity = translator.getEvaluationArity(atom);
            assert(auxiliaryArity <= atom->getArity() && "auxiliary arity out of bounds");
            size_t arity = atom->getArity() - auxiliaryArity;

            if (arity == 0) {
                // for a nullary, negation is a simple emptiness check
                return mk<ram::EmptinessCheck>(translator.translateRelation(atom));
            }

            // else, we construct the atom and create a negation
            VecOwn<ram::Expression> values;
            auto args = atom->getArguments();
            for (size_t i = 0; i < arity; i++) {
                values.push_back(translator.translateValue(args[i], index));
            }
            for (size_t i = 0; i < auxiliaryArity; i++) {
                values.push_back(mk<ram::UndefValue>());
            }
            return mk<ram::Negation>(
                    mk<ram::ExistenceCheck>(translator.translateRelation(atom), std::move(values)));
        }
    };
    return ConstraintTranslator(*this, index)(*lit);
}

Own<ast::Clause> AstToRamTranslator::ClauseTranslator::getReorderedClause(
        const ast::Clause& clause, const int version) const {
    const auto plan = clause.getExecutionPlan();

    // check whether there is an imposed order constraint
    if (plan == nullptr) {
        // no plan, so reorder it according to the internal heuristic
        if (auto* reorderedClause = ast::transform::ReorderLiteralsTransformer::reorderClauseWithSips(
                    *translator.sips, &clause)) {
            return Own<ast::Clause>(reorderedClause);
        }
        return nullptr;
    }
    auto orders = plan->getOrders();
    if (orders.find(version) == orders.end()) {
        return nullptr;
    }

    // get the imposed order
    const auto& order = orders[version];

    // create a copy and fix order
    Own<ast::Clause> reorderedClause(clause.clone());

    // Change order to start at zero
    std::vector<unsigned int> newOrder(order->getOrder().size());
    std::transform(order->getOrder().begin(), order->getOrder().end(), newOrder.begin(),
            [](unsigned int i) -> unsigned int { return i - 1; });

    // re-order atoms
    reorderedClause.reset(reorderAtoms(reorderedClause.get(), newOrder));

    // clear other order and fix plan
    reorderedClause->clearExecutionPlan();

    return reorderedClause;
}

AstToRamTranslator::ClauseTranslator::arg_list* AstToRamTranslator::ClauseTranslator::getArgList(
        const ast::Node* curNode, std::map<const ast::Node*, Own<arg_list>>& nodeArgs) const {
    if (nodeArgs.count(curNode) == 0u) {
        if (auto rec = dynamic_cast<const ast::RecordInit*>(curNode)) {
            nodeArgs[curNode] = mk<arg_list>(rec->getArguments());
        } else if (auto atom = dynamic_cast<const ast::Atom*>(curNode)) {
            nodeArgs[curNode] = mk<arg_list>(atom->getArguments());
        } else {
            fatal("node type doesn't have arguments!");
        }
    }
    return nodeArgs[curNode].get();
}

void AstToRamTranslator::ClauseTranslator::indexValues(const ast::Node* curNode,
        std::map<const ast::Node*, Own<arg_list>>& nodeArgs, std::map<const arg_list*, int>& arg_level,
        ram::RelationReference* relation) {
    arg_list* cur = getArgList(curNode, nodeArgs);
    for (size_t pos = 0; pos < cur->size(); ++pos) {
        // get argument
        auto& arg = (*cur)[pos];

        // check for variable references
        if (auto var = dynamic_cast<const ast::Variable*>(arg)) {
            if (pos < relation->get()->getArity()) {
                valueIndex.addVarReference(*var, arg_level[cur], pos, souffle::clone(relation));
            } else {
                valueIndex.addVarReference(*var, arg_level[cur], pos);
            }
        }

        // check for nested records
        if (auto rec = dynamic_cast<const ast::RecordInit*>(arg)) {
            // introduce new nesting level for unpack
            op_nesting.push_back(rec);
            arg_level[getArgList(rec, nodeArgs)] = level++;

            // register location of record
            valueIndex.setRecordDefinition(*rec, arg_level[cur], pos);

            // resolve nested components
            indexValues(rec, nodeArgs, arg_level, relation);
        }
    }
}

/** index values in rule */
void AstToRamTranslator::ClauseTranslator::createValueIndex(const ast::Clause& clause) {
    for (const auto* atom : ast::getBodyLiterals<ast::Atom>(clause)) {
        // std::map<const arg_list*, int> arg_level;
        std::map<const ast::Node*, Own<arg_list>> nodeArgs;

        std::map<const arg_list*, int> arg_level;
        nodeArgs[atom] = mk<arg_list>(atom->getArguments());
        // the atom is obtained at the current level
        // increment nesting level for the atom
        arg_level[nodeArgs[atom].get()] = level++;
        op_nesting.push_back(atom);

        indexValues(atom, nodeArgs, arg_level, translator.translateRelation(atom).get());
    }

    // add aggregation functions
    visitDepthFirstPostOrder(clause, [&](const ast::Argument& arg) {
        // returns the write-location for this generator (or none if an equiv arg was already seen)
        auto addGenerator = [&]() -> std::optional<int> {
            // The by-value compare means that we're effectively doing CSE for any
            // generator args during code-gen. This is a weird place to do this.
            if (any_of(generators, [&](auto* x) { return *x == arg; })) return {};
            generators.push_back(&arg);

            int aggLoc = level++;
            valueIndex.setGeneratorLoc(arg, Location({aggLoc, 0}));
            return aggLoc;
        };

        if (auto agg = dynamic_cast<const ast::Aggregator*>(&arg)) {
            if (auto aggLoc = addGenerator()) {
                // bind aggregator variables to locations
                const ast::Atom* atom = nullptr;
                for (auto lit : agg->getBodyLiterals()) {
                    if (atom == nullptr) {
                        atom = dynamic_cast<const ast::Atom*>(lit);
                    } else {
                        break;
                    }
                }
                if (atom != nullptr) {
                    size_t pos = 0;
                    for (auto* arg : atom->getArguments()) {
                        if (const auto* var = dynamic_cast<const ast::Variable*>(arg)) {
                            valueIndex.addVarReference(
                                    *var, *aggLoc, (int)pos, translator.translateRelation(atom));
                        }
                        ++pos;
                    }
                }
            }
        }

        auto func = dynamic_cast<const ast::IntrinsicFunctor*>(&arg);
        if (func && func->getFunctionInfo()->multipleResults) {
            addGenerator();
        }
    });
}

Own<ram::Operation> AstToRamTranslator::ClauseTranslator::createOperation(const ast::Clause& clause) {
    const auto head = clause.getHead();

    VecOwn<ram::Expression> values;
    for (ast::Argument* arg : head->getArguments()) {
        values.push_back(translator.translateValue(arg, valueIndex));
    }

    Own<ram::Operation> project = mk<ram::Project>(translator.translateRelation(head), std::move(values));

    if (head->getArity() == 0) {
        project = mk<ram::Filter>(
                mk<ram::EmptinessCheck>(translator.translateRelation(head)), std::move(project));
    }

    // build up insertion call
    return project;  // start with innermost
}

Own<ram::Operation> AstToRamTranslator::ProvenanceClauseTranslator::createOperation(
        const ast::Clause& clause) {
    VecOwn<ram::Expression> values;

    // get all values in the body
    for (ast::Literal* lit : clause.getBodyLiterals()) {
        if (auto atom = dynamic_cast<ast::Atom*>(lit)) {
            for (ast::Argument* arg : atom->getArguments()) {
                values.push_back(translator.translateValue(arg, valueIndex));
            }
        } else if (auto neg = dynamic_cast<ast::ProvenanceNegation*>(lit)) {
            size_t auxiliaryArity = translator.getEvaluationArity(neg->getAtom());
            for (size_t i = 0; i < neg->getAtom()->getArguments().size() - auxiliaryArity; ++i) {
                auto arg = neg->getAtom()->getArguments()[i];
                values.push_back(translator.translateValue(arg, valueIndex));
            }
            for (size_t i = 0; i < auxiliaryArity; ++i) {
                values.push_back(mk<ram::SignedConstant>(-1));
            }
        } else if (auto neg = dynamic_cast<ast::Negation*>(lit)) {
            for (ast::Argument* arg : neg->getAtom()->getArguments()) {
                values.push_back(translator.translateValue(arg, valueIndex));
            }
        } else if (auto con = dynamic_cast<ast::BinaryConstraint*>(lit)) {
            values.push_back(translator.translateValue(con->getLHS(), valueIndex));
            values.push_back(translator.translateValue(con->getRHS(), valueIndex));
        }
    }

    return mk<ram::SubroutineReturn>(std::move(values));
}

Own<ram::Condition> AstToRamTranslator::ClauseTranslator::createCondition(const ast::Clause& originalClause) {
    const auto head = originalClause.getHead();

    // add stopping criteria for nullary relations
    // (if it contains already the null tuple, don't re-compute)
    if (head->getArity() == 0) {
        return mk<ram::EmptinessCheck>(translator.translateRelation(head));
    }
    return nullptr;
}

Own<ram::Condition> AstToRamTranslator::ProvenanceClauseTranslator::createCondition(
        const ast::Clause& /* originalClause */) {
    return nullptr;
}

Own<ram::Operation> AstToRamTranslator::ClauseTranslator::filterByConstraints(size_t const level,
        const std::vector<ast::Argument*>& args, Own<ram::Operation> op, bool constrainByFunctors) {
    size_t pos = 0;

    auto mkFilter = [&](bool isFloatArg, Own<ram::Expression> rhs) {
        return mk<ram::Filter>(
                mk<ram::Constraint>(isFloatArg ? BinaryConstraintOp::FEQ : BinaryConstraintOp::EQ,
                        mk<ram::TupleElement>(level, pos), std::move(rhs)),
                std::move(op));
    };

    for (auto* a : args) {
        if (auto* c = dynamic_cast<const ast::Constant*>(a)) {
            auto* const c_num = dynamic_cast<const ast::NumericConstant*>(c);
            assert((!c_num || c_num->getType()) && "numeric constant wasn't bound to a type");
            op = mkFilter(c_num && *c_num->getType() == ast::NumericConstant::Type::Float,
                    translator.translateConstant(*c));
        } else if (auto* func = dynamic_cast<const ast::Functor*>(a)) {
            if (constrainByFunctors) {
                op = mkFilter(func->getReturnType() == TypeAttribute::Float,
                        translator.translateValue(func, valueIndex));
            }
        }

        ++pos;
    }

    return op;
}

/** generate RAM code for a clause */
Own<ram::Statement> AstToRamTranslator::ClauseTranslator::translateClause(
        const ast::Clause& clause, const ast::Clause& originalClause, const int version) {
    if (auto reorderedClause = getReorderedClause(clause, version)) {
        // translate reordered clause
        return translateClause(*reorderedClause, originalClause, version);
    }

    // get extract some details
    const ast::Atom* head = clause.getHead();

    // handle facts
    if (isFact(clause)) {
        // translate arguments
        VecOwn<ram::Expression> values;
        for (auto& arg : head->getArguments()) {
            values.push_back(translator.translateValue(arg, ValueIndex()));
        }

        // create a fact statement
        return mk<ram::Query>(mk<ram::Project>(translator.translateRelation(head), std::move(values)));
    }

    // the rest should be rules
    assert(isRule(clause));

    createValueIndex(clause);

    // -- create RAM statement --

    Own<ram::Operation> op = createOperation(clause);

    /* add equivalence constraints imposed by variable binding */
    for (const auto& cur : valueIndex.getVariableReferences()) {
        // the first appearance
        const Location& first = *cur.second.begin();
        // all other appearances
        for (const Location& loc : cur.second) {
            if (first != loc && !valueIndex.isGenerator(loc.identifier)) {
                // FIXME: equiv' for float types (`FEQ`)
                op = mk<ram::Filter>(mk<ram::Constraint>(BinaryConstraintOp::EQ, makeRamTupleElement(first),
                                             makeRamTupleElement(loc)),
                        std::move(op));
            }
        }
    }

    /* add conditions caused by atoms, negations, and binary relations */
    for (const auto& lit : clause.getBodyLiterals()) {
        if (auto condition = translator.translateConstraint(lit, valueIndex)) {
            op = mk<ram::Filter>(std::move(condition), std::move(op));
        }
    }

    // add aggregator conditions
    size_t curLevel = op_nesting.size() - 1;
    for (auto it = op_nesting.rbegin(); it != op_nesting.rend(); ++it, --curLevel) {
        const ast::Node* cur = *it;

        if (const auto* atom = dynamic_cast<const ast::Atom*>(cur)) {
            // add constraints
            size_t pos = 0;
            for (auto arg : atom->getArguments()) {
                if (auto* agg = dynamic_cast<ast::Aggregator*>(arg)) {
                    auto loc = valueIndex.getGeneratorLoc(*agg);
                    // FIXME: equiv' for float types (`FEQ`)
                    op = mk<ram::Filter>(
                            mk<ram::Constraint>(BinaryConstraintOp::EQ, mk<ram::TupleElement>(curLevel, pos),
                                    makeRamTupleElement(loc)),
                            std::move(op));
                }
                ++pos;
            }
        }
    }

    // add generator levels
    --level;
    for (auto* cur : reverse(generators)) {
        if (auto agg = dynamic_cast<const ast::Aggregator*>(cur)) {
            // condition for aggregate and helper function to add terms
            Own<ram::Condition> aggCond;
            auto addAggCondition = [&](Own<ram::Condition> arg) {
                aggCond = aggCond ? mk<ram::Conjunction>(std::move(aggCond), std::move(arg)) : std::move(arg);
            };

            // translate constraints of sub-clause
            for (auto&& lit : agg->getBodyLiterals()) {
                if (auto newCondition = translator.translateConstraint(lit, valueIndex)) {
                    addAggCondition(std::move(newCondition));
                }
            }

            // get the first predicate of the sub-clause
            // NB: at most one atom is permitted in a sub-clause
            const ast::Atom* atom = nullptr;
            for (auto&& lit : agg->getBodyLiterals()) {
                if (atom == nullptr) {
                    atom = dynamic_cast<const ast::Atom*>(lit);
                } else {
                    assert(!isA<ast::Atom>(lit) && "Unsupported complex aggregation body encountered!");
                }
            }

            // translate arguments's of atom (if exists) to conditions
            if (atom != nullptr) {
                size_t pos = 0;
                auto addAggEqCondition = [&](Own<ram::Expression> value) {
                    if (isUndefValue(value.get())) return;

                    // FIXME: equiv' for float types (`FEQ`)
                    addAggCondition(mk<ram::Constraint>(
                            BinaryConstraintOp::EQ, mk<ram::TupleElement>(level, pos), std::move(value)));
                };
                for (auto* arg : atom->getArguments()) {
                    // variable bindings are issued differently since we don't want self
                    // referential variable bindings
                    if (auto* var = dynamic_cast<const ast::Variable*>(arg)) {
                        for (auto&& loc : valueIndex.getVariableReferences().find(var->getName())->second) {
                            if (level != loc.identifier || (int)pos != loc.element) {
                                addAggEqCondition(makeRamTupleElement(loc));
                                break;
                            }
                        }
                    } else if (auto value = translator.translateValue(arg, valueIndex)) {
                        addAggEqCondition(std::move(value));
                    }
                    ++pos;
                }
            }

            // translate aggregate expression
            auto expr = translator.translateValue(agg->getTargetExpression(), valueIndex);

            // add Ram-Aggregation layer
            op = mk<ram::Aggregate>(std::move(op), agg->getOperator(), translator.translateRelation(atom),
                    expr ? std::move(expr) : mk<ram::UndefValue>(),
                    aggCond ? std::move(aggCond) : mk<ram::True>(), level);
        } else if (const auto* func = dynamic_cast<const ast::IntrinsicFunctor*>(cur)) {
            VecOwn<ram::Expression> args;
            for (auto&& x : func->getArguments()) {
                args.push_back(translator.translateValue(x, valueIndex));
            }

            auto func_op = [&]() -> ram::NestedIntrinsicOp {
                switch (func->getFunctionInfo()->op) {
                    case FunctorOp::RANGE: return ram::NestedIntrinsicOp::RANGE;
                    case FunctorOp::URANGE: return ram::NestedIntrinsicOp::URANGE;
                    case FunctorOp::FRANGE: return ram::NestedIntrinsicOp::FRANGE;

                    default:
                        assert(func->getFunctionInfo()->multipleResults);
                        fatal("missing case handler or bad code-gen");
                }
            };

            op = mk<ram::NestedIntrinsicOperator>(func_op(), std::move(args), std::move(op), level);
        }

        --level;
    }

    // build operation bottom-up
    while (!op_nesting.empty()) {
        // get next operator
        const ast::Node* cur = op_nesting.back();
        op_nesting.pop_back();

        // get current nesting level
        auto level = op_nesting.size();

        if (const auto* atom = dynamic_cast<const ast::Atom*>(cur)) {
            // add constraints
            // TODO: do we wish to enable constraints by header functor? record inits do so...
            op = filterByConstraints(level, atom->getArguments(), std::move(op), false);

            // check whether all arguments are unnamed variables
            bool isAllArgsUnnamed = true;
            for (auto* argument : atom->getArguments()) {
                if (!isA<ast::UnnamedVariable>(argument)) {
                    isAllArgsUnnamed = false;
                }
            }

            // add check for emptiness for an atom
            op = mk<ram::Filter>(
                    mk<ram::Negation>(mk<ram::EmptinessCheck>(translator.translateRelation(atom))),
                    std::move(op));

            // add a scan level
            if (atom->getArity() != 0 && !isAllArgsUnnamed) {
                if (head->getArity() == 0) {
                    op = mk<ram::Break>(
                            mk<ram::Negation>(mk<ram::EmptinessCheck>(translator.translateRelation(head))),
                            std::move(op));
                }
                if (Global::config().has("profile")) {
                    std::stringstream ss;
                    ss << head->getQualifiedName();
                    ss.str("");
                    ss << "@frequency-atom" << ';';
                    ss << originalClause.getHead()->getQualifiedName() << ';';
                    ss << version << ';';
                    ss << stringify(toString(clause)) << ';';
                    ss << stringify(toString(*atom)) << ';';
                    ss << stringify(toString(originalClause)) << ';';
                    ss << level << ';';
                    op = mk<ram::Scan>(translator.translateRelation(atom), level, std::move(op), ss.str());
                } else {
                    op = mk<ram::Scan>(translator.translateRelation(atom), level, std::move(op));
                }
            }

            // TODO: support constants in nested records!
        } else if (const auto* rec = dynamic_cast<const ast::RecordInit*>(cur)) {
            // add constant constraints
            op = filterByConstraints(level, rec->getArguments(), std::move(op));

            // add an unpack level
            const Location& loc = valueIndex.getDefinitionPoint(*rec);
            op = mk<ram::UnpackRecord>(
                    std::move(op), level, makeRamTupleElement(loc), rec->getArguments().size());
        } else {
            fatal("Unsupported AST node for creation of scan-level!");
        }
    }

    /* generate the final RAM Insert statement */
    Own<ram::Condition> cond = createCondition(originalClause);
    if (cond != nullptr) {
        return mk<ram::Query>(mk<ram::Filter>(std::move(cond), std::move(op)));
    } else {
        return mk<ram::Query>(std::move(op));
    }
}

Own<ram::Expression> AstToRamTranslator::translateConstant(ast::Constant const& c) {
    auto const rawConstant = getConstantRamRepresentation(c);

    if (auto* const c_num = dynamic_cast<const ast::NumericConstant*>(&c)) {
        switch (*c_num->getType()) {
            case ast::NumericConstant::Type::Int: return mk<ram::SignedConstant>(rawConstant);
            case ast::NumericConstant::Type::Uint: return mk<ram::UnsignedConstant>(rawConstant);
            case ast::NumericConstant::Type::Float: return mk<ram::FloatConstant>(rawConstant);
        }
    }

    return mk<ram::SignedConstant>(rawConstant);
}

/** generate RAM code for a non-recursive relation */
Own<ram::Statement> AstToRamTranslator::translateNonRecursiveRelation(
        const ast::Relation& rel, const ast::analysis::RecursiveClausesAnalysis* recursiveClauses) {
    /* start with an empty sequence */
    VecOwn<ram::Statement> res;

    // the ram table reference
    Own<ram::RelationReference> rrel = translateRelation(&rel);

    /* iterate over all clauses that belong to the relation */
    for (ast::Clause* clause : getClauses(*program, rel)) {
        // skip recursive rules
        if (recursiveClauses->recursive(clause)) {
            continue;
        }

        // translate clause
        Own<ram::Statement> rule = ClauseTranslator(*this).translateClause(*clause, *clause);

        // add logging
        if (Global::config().has("profile")) {
            const std::string& relationName = toString(rel.getQualifiedName());
            const SrcLocation& srcLocation = clause->getSrcLoc();
            const std::string clauseText = stringify(toString(*clause));
            const std::string logTimerStatement =
                    LogStatement::tNonrecursiveRule(relationName, srcLocation, clauseText);
            const std::string logSizeStatement =
                    LogStatement::nNonrecursiveRule(relationName, srcLocation, clauseText);
            rule = mk<ram::LogRelationTimer>(std::move(rule), logTimerStatement, souffle::clone(rrel));
        }

        // add debug info
        std::ostringstream ds;
        ds << toString(*clause) << "\nin file ";
        ds << clause->getSrcLoc();
        rule = mk<ram::DebugInfo>(std::move(rule), ds.str());

        // add rule to result
        appendStmt(res, std::move(rule));
    }

    // add logging for entire relation
    if (Global::config().has("profile")) {
        const std::string& relationName = toString(rel.getQualifiedName());
        const SrcLocation& srcLocation = rel.getSrcLoc();
        const std::string logSizeStatement = LogStatement::nNonrecursiveRelation(relationName, srcLocation);

        // add timer if we did any work
        if (!res.empty()) {
            const std::string logTimerStatement =
                    LogStatement::tNonrecursiveRelation(relationName, srcLocation);
            auto newStmt = mk<ram::LogRelationTimer>(
                    mk<ram::Sequence>(std::move(res)), logTimerStatement, souffle::clone(rrel));
            res.clear();
            appendStmt(res, std::move(newStmt));
        } else {
            // add table size printer
            appendStmt(res, mk<ram::LogSize>(souffle::clone(rrel), logSizeStatement));
        }
    }

    // done
    return mk<ram::Sequence>(std::move(res));
}

/**
 * A utility function assigning names to unnamed variables such that enclosing
 * constructs may be cloned without losing the variable-identity.
 */
void AstToRamTranslator::nameUnnamedVariables(ast::Clause* clause) {
    // the node mapper conducting the actual renaming
    struct Instantiator : public ast::NodeMapper {
        mutable int counter = 0;

        Instantiator() = default;

        Own<ast::Node> operator()(Own<ast::Node> node) const override {
            // apply recursive
            node->apply(*this);

            // replace unknown variables
            if (dynamic_cast<ast::UnnamedVariable*>(node.get()) != nullptr) {
                auto name = " _unnamed_var" + toString(++counter);
                return mk<ast::Variable>(name);
            }

            // otherwise nothing
            return node;
        }
    };

    // name all variables in the atoms
    Instantiator init;
    for (auto& atom : ast::getBodyLiterals<ast::Atom>(*clause)) {
        atom->apply(init);
    }
}

/** generate RAM code for recursive relations in a strongly-connected component */
Own<ram::Statement> AstToRamTranslator::translateRecursiveRelation(const std::set<const ast::Relation*>& scc,
        const ast::analysis::RecursiveClausesAnalysis* recursiveClauses) {
    // initialize sections
    VecOwn<ram::Statement> preamble;
    VecOwn<ram::Statement> updateTable;
    VecOwn<ram::Statement> postamble;

    auto genMerge = [](const ram::RelationReference* dest,
                            const ram::RelationReference* src) -> Own<ram::Statement> {
        VecOwn<ram::Expression> values;
        if (src->get()->getArity() == 0) {
            return mk<ram::Query>(
                    mk<ram::Filter>(mk<ram::Negation>(mk<ram::EmptinessCheck>(souffle::clone(src))),
                            mk<ram::Project>(souffle::clone(dest), std::move(values))));
        }
        for (std::size_t i = 0; i < dest->get()->getArity(); i++) {
            values.push_back(mk<ram::TupleElement>(0, i));
        }
        auto stmt = mk<ram::Query>(mk<ram::Scan>(
                souffle::clone(src), 0, mk<ram::Project>(souffle::clone(dest), std::move(values))));
        if (dest->get()->getRepresentation() == RelationRepresentation::EQREL) {
            return mk<ram::Sequence>(
                    mk<ram::Extend>(souffle::clone(dest), souffle::clone(src)), std::move(stmt));
        }
        return stmt;
    };

    // --- create preamble ---

    /* Compute non-recursive clauses for relations in scc and push
       the results in their delta tables. */
    for (const ast::Relation* rel : scc) {
        /* create update statements for fixpoint (even iteration) */
        Own<ram::Statement> updateRelTable =
                mk<ram::Sequence>(genMerge(translateRelation(rel).get(), translateNewRelation(rel).get()),
                        mk<ram::Swap>(translateDeltaRelation(rel), translateNewRelation(rel)),
                        mk<ram::Clear>(translateNewRelation(rel)));

        /* measure update time for each relation */
        if (Global::config().has("profile")) {
            updateRelTable = mk<ram::LogRelationTimer>(std::move(updateRelTable),
                    LogStatement::cRecursiveRelation(toString(rel->getQualifiedName()), rel->getSrcLoc()),
                    translateNewRelation(rel));
        }

        /* drop temporary tables after recursion */
        appendStmt(postamble, mk<ram::Clear>(translateDeltaRelation(rel)));
        appendStmt(postamble, mk<ram::Clear>(translateNewRelation(rel)));

        /* Generate code for non-recursive part of relation */
        /* Generate merge operation for temp tables */
        appendStmt(preamble, translateNonRecursiveRelation(*rel, recursiveClauses));
        appendStmt(preamble, genMerge(translateDeltaRelation(rel).get(), translateRelation(rel).get()));

        /* Add update operations of relations to parallel statements */
        appendStmt(updateTable, std::move(updateRelTable));
    }

    // --- build main loop ---

    VecOwn<ram::Statement> loopSeq;

    // create a utility to check SCC membership
    auto isInSameSCC = [&](const ast::Relation* rel) {
        return std::find(scc.begin(), scc.end(), rel) != scc.end();
    };

    /* Compute temp for the current tables */
    for (const ast::Relation* rel : scc) {
        VecOwn<ram::Statement> loopRelSeq;

        /* Find clauses for relation rel */
        for (const auto& cl : getClauses(*program, *rel)) {
            // skip non-recursive clauses
            if (!recursiveClauses->recursive(cl)) {
                continue;
            }

            // each recursive rule results in several operations
            int version = 0;
            const auto& atoms = ast::getBodyLiterals<ast::Atom>(*cl);
            for (size_t j = 0; j < atoms.size(); ++j) {
                const ast::Atom* atom = atoms[j];
                const ast::Relation* atomRelation = getAtomRelation(atom, program);

                // only interested in atoms within the same SCC
                if (!isInSameSCC(atomRelation)) {
                    continue;
                }

                // modify the processed rule to use delta relation and write to new relation
                Own<ast::Clause> r1(cl->clone());
                r1->getHead()->setQualifiedName(translateNewRelation(rel)->get()->getName());
                ast::getBodyLiterals<ast::Atom>(*r1)[j]->setQualifiedName(
                        translateDeltaRelation(atomRelation)->get()->getName());
                if (Global::config().has("provenance")) {
                    r1->addToBody(mk<ast::ProvenanceNegation>(souffle::clone(cl->getHead())));
                } else {
                    if (r1->getHead()->getArity() > 0) {
                        r1->addToBody(mk<ast::Negation>(souffle::clone(cl->getHead())));
                    }
                }

                // replace wildcards with variables (reduces indices when wildcards are used in recursive
                // atoms)
                nameUnnamedVariables(r1.get());

                // reduce R to P ...
                for (size_t k = j + 1; k < atoms.size(); k++) {
                    if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                        auto cur = souffle::clone(ast::getBodyLiterals<ast::Atom>(*r1)[k]);
                        cur->setQualifiedName(
                                translateDeltaRelation(getAtomRelation(atoms[k], program))->get()->getName());
                        r1->addToBody(mk<ast::Negation>(std::move(cur)));
                    }
                }

                Own<ram::Statement> rule = ClauseTranslator(*this).translateClause(*r1, *cl, version);

                /* add logging */
                if (Global::config().has("profile")) {
                    const std::string& relationName = toString(rel->getQualifiedName());
                    const SrcLocation& srcLocation = cl->getSrcLoc();
                    const std::string clauseText = stringify(toString(*cl));
                    const std::string logTimerStatement =
                            LogStatement::tRecursiveRule(relationName, version, srcLocation, clauseText);
                    const std::string logSizeStatement =
                            LogStatement::nRecursiveRule(relationName, version, srcLocation, clauseText);
                    rule = mk<ram::LogRelationTimer>(
                            std::move(rule), logTimerStatement, translateNewRelation(rel));
                }

                // add debug info
                std::ostringstream ds;
                ds << toString(*cl) << "\nin file ";
                ds << cl->getSrcLoc();
                rule = mk<ram::DebugInfo>(std::move(rule), ds.str());

                // add to loop body
                appendStmt(loopRelSeq, std::move(rule));

                // increment version counter
                version++;
            }

            if (cl->getExecutionPlan() != nullptr) {
                // ensure that all required versions have been created, as expected
                int maxVersion = -1;
                for (auto const& cur : cl->getExecutionPlan()->getOrders()) {
                    maxVersion = std::max(cur.first, maxVersion);
                }
                assert(version > maxVersion && "missing clause versions");
            }
        }

        // if there was no rule, continue
        if (loopRelSeq.size() == 0) {
            continue;
        }

        // label all versions
        if (Global::config().has("profile")) {
            const std::string& relationName = toString(rel->getQualifiedName());
            const SrcLocation& srcLocation = rel->getSrcLoc();
            const std::string logTimerStatement = LogStatement::tRecursiveRelation(relationName, srcLocation);
            const std::string logSizeStatement = LogStatement::nRecursiveRelation(relationName, srcLocation);
            auto newStmt = mk<ram::LogRelationTimer>(
                    mk<ram::Sequence>(std::move(loopRelSeq)), logTimerStatement, translateNewRelation(rel));
            loopRelSeq.clear();
            appendStmt(loopRelSeq, std::move(newStmt));
        }

        /* add rule computations of a relation to parallel statement */
        appendStmt(loopSeq, mk<ram::Sequence>(std::move(loopRelSeq)));
    }
    auto loop = mk<ram::Parallel>(std::move(loopSeq));

    /* construct exit conditions for odd and even iteration */
    auto addCondition = [](Own<ram::Condition>& cond, Own<ram::Condition> clause) {
        cond = ((cond) ? mk<ram::Conjunction>(std::move(cond), std::move(clause)) : std::move(clause));
    };

    Own<ram::Condition> exitCond;
    VecOwn<ram::Statement> exitStmts;
    for (const ast::Relation* rel : scc) {
        addCondition(exitCond, mk<ram::EmptinessCheck>(translateNewRelation(rel)));
        if (ioType->isLimitSize(rel)) {
            Own<ram::Condition> limit =
                    mk<ram::Constraint>(BinaryConstraintOp::GE, mk<ram::RelationSize>(translateRelation(rel)),
                            mk<ram::SignedConstant>(ioType->getLimitSize(rel)));
            appendStmt(exitStmts, mk<ram::Exit>(std::move(limit)));
        }
    }

    /* construct fixpoint loop  */
    VecOwn<ram::Statement> res;
    if (preamble.size() > 0) {
        appendStmt(res, mk<ram::Sequence>(std::move(preamble)));
    }
    if (!loop->getStatements().empty() && exitCond && updateTable.size() > 0) {
        appendStmt(res,
                mk<ram::Loop>(mk<ram::Sequence>(std::move(loop), mk<ram::Exit>(std::move(exitCond)),
                        mk<ram::Sequence>(std::move(exitStmts)), mk<ram::Sequence>(std::move(updateTable)))));
    }
    if (postamble.size() > 0) {
        appendStmt(res, mk<ram::Sequence>(std::move(postamble)));
    }
    if (res.size() > 0) {
        return mk<ram::Sequence>(std::move(res));
    }

    fatal("Not Implemented");
}

/** make a subroutine to search for subproofs */
Own<ram::Statement> AstToRamTranslator::makeSubproofSubroutine(const ast::Clause& clause) {
    auto intermediateClause = mk<ast::Clause>(souffle::clone(clause.getHead()));

    // create a clone where all the constraints are moved to the end
    for (auto bodyLit : clause.getBodyLiterals()) {
        // first add all the things that are not constraints
        if (!isA<ast::Constraint>(bodyLit)) {
            intermediateClause->addToBody(souffle::clone(bodyLit));
        }
    }

    // now add all constraints
    for (auto bodyLit : ast::getBodyLiterals<ast::Constraint>(clause)) {
        intermediateClause->addToBody(souffle::clone(bodyLit));
    }

    // name unnamed variables
    nameUnnamedVariables(intermediateClause.get());

    // add constraint for each argument in head of atom
    ast::Atom* head = intermediateClause->getHead();
    size_t auxiliaryArity = auxArityAnalysis->getArity(head);
    auto args = head->getArguments();
    for (size_t i = 0; i < head->getArity() - auxiliaryArity; i++) {
        auto arg = args[i];

        if (auto var = dynamic_cast<ast::Variable*>(arg)) {
            // FIXME: float equiv (`FEQ`)
            intermediateClause->addToBody(mk<ast::BinaryConstraint>(
                    BinaryConstraintOp::EQ, souffle::clone(var), mk<ast::SubroutineArgument>(i)));
        } else if (auto func = dynamic_cast<ast::Functor*>(arg)) {
            auto opEq = func->getReturnType() == TypeAttribute::Float ? BinaryConstraintOp::FEQ
                                                                      : BinaryConstraintOp::EQ;
            intermediateClause->addToBody(
                    mk<ast::BinaryConstraint>(opEq, souffle::clone(func), mk<ast::SubroutineArgument>(i)));
        } else if (auto rec = dynamic_cast<ast::RecordInit*>(arg)) {
            intermediateClause->addToBody(mk<ast::BinaryConstraint>(
                    BinaryConstraintOp::EQ, souffle::clone(rec), mk<ast::SubroutineArgument>(i)));
        }
    }

    // index of level argument in argument list
    size_t levelIndex = head->getArguments().size() - auxiliaryArity;

    // add level constraints, i.e., that each body literal has height less than that of the head atom
    const auto& bodyLiterals = intermediateClause->getBodyLiterals();
    for (auto lit : bodyLiterals) {
        if (auto atom = dynamic_cast<ast::Atom*>(lit)) {
            auto arity = atom->getArity();
            auto atomArgs = atom->getArguments();
            // arity - 1 is the level number in body atoms
            intermediateClause->addToBody(mk<ast::BinaryConstraint>(BinaryConstraintOp::LT,
                    souffle::clone(atomArgs[arity - 1]), mk<ast::SubroutineArgument>(levelIndex)));
        }
    }
    return ProvenanceClauseTranslator(*this).translateClause(*intermediateClause, clause);
}

/** make a subroutine to search for subproofs for the non-existence of a tuple */
Own<ram::Statement> AstToRamTranslator::makeNegationSubproofSubroutine(const ast::Clause& clause) {
    // TODO (taipan-snake): Currently we only deal with atoms (no constraints or negations or aggregates
    // or anything else...)
    //
    // The resulting subroutine looks something like this:
    // IF (arg(0), arg(1), _, _) IN rel_1:
    //   return 1
    // IF (arg(0), arg(1), _ ,_) NOT IN rel_1:
    //   return 0
    // ...

    // clone clause for mutation, rearranging constraints to be at the end
    auto clauseReplacedAggregates = mk<ast::Clause>(souffle::clone(clause.getHead()));

    // create a clone where all the constraints are moved to the end
    for (auto bodyLit : clause.getBodyLiterals()) {
        // first add all the things that are not constraints
        if (!isA<ast::Constraint>(bodyLit)) {
            clauseReplacedAggregates->addToBody(souffle::clone(bodyLit));
        }
    }

    // now add all constraints
    for (auto bodyLit : ast::getBodyLiterals<ast::Constraint>(clause)) {
        clauseReplacedAggregates->addToBody(souffle::clone(bodyLit));
    }

    int aggNumber = 0;
    struct AggregatesToVariables : public ast::NodeMapper {
        int& aggNumber;

        AggregatesToVariables(int& aggNumber) : aggNumber(aggNumber) {}

        Own<ast::Node> operator()(Own<ast::Node> node) const override {
            if (dynamic_cast<ast::Aggregator*>(node.get()) != nullptr) {
                return mk<ast::Variable>("agg_" + std::to_string(aggNumber++));
            }

            node->apply(*this);
            return node;
        }
    };

    AggregatesToVariables aggToVar(aggNumber);
    clauseReplacedAggregates->apply(aggToVar);

    // build a vector of unique variables
    std::vector<const ast::Variable*> uniqueVariables;

    visitDepthFirst(*clauseReplacedAggregates, [&](const ast::Variable& var) {
        if (var.getName().find("@level_num") == std::string::npos) {
            // use find_if since uniqueVariables stores pointers, and we need to dereference the pointer to
            // check equality
            if (std::find_if(uniqueVariables.begin(), uniqueVariables.end(),
                        [&](const ast::Variable* v) { return *v == var; }) == uniqueVariables.end()) {
                uniqueVariables.push_back(&var);
            }
        }
    });

    // a mapper to replace variables with subroutine arguments
    struct VariablesToArguments : public ast::NodeMapper {
        const std::vector<const ast::Variable*>& uniqueVariables;

        VariablesToArguments(const std::vector<const ast::Variable*>& uniqueVariables)
                : uniqueVariables(uniqueVariables) {}

        Own<ast::Node> operator()(Own<ast::Node> node) const override {
            // replace unknown variables
            if (auto varPtr = dynamic_cast<const ast::Variable*>(node.get())) {
                if (varPtr->getName().find("@level_num") == std::string::npos) {
                    size_t argNum = std::find_if(uniqueVariables.begin(), uniqueVariables.end(),
                                            [&](const ast::Variable* v) { return *v == *varPtr; }) -
                                    uniqueVariables.begin();

                    return mk<ast::SubroutineArgument>(argNum);
                } else {
                    return mk<ast::UnnamedVariable>();
                }
            }

            // apply recursive
            node->apply(*this);

            // otherwise nothing
            return node;
        }
    };

    // the structure of this subroutine is a sequence where each nested statement is a search in each
    // relation
    VecOwn<ram::Statement> searchSequence;

    // make a copy so that when we mutate clause, pointers to objects in newClause are not affected
    auto newClause = souffle::clone(clauseReplacedAggregates);

    // go through each body atom and create a return
    size_t litNumber = 0;
    for (const auto& lit : newClause->getBodyLiterals()) {
        if (auto atom = dynamic_cast<ast::Atom*>(lit)) {
            size_t auxiliaryArity = auxArityAnalysis->getArity(atom);
            // get a ram::RelationReference
            auto relRef = translateRelation(atom);
            // construct a query
            VecOwn<ram::Expression> query;

            // translate variables to subroutine arguments
            VariablesToArguments varsToArgs(uniqueVariables);
            atom->apply(varsToArgs);

            auto atomArgs = atom->getArguments();
            // add each value (subroutine argument) to the search query
            for (size_t i = 0; i < atom->getArity() - auxiliaryArity; i++) {
                auto arg = atomArgs[i];
                query.push_back(translateValue(arg, ValueIndex()));
            }

            // fill up query with nullptrs for the provenance columns
            for (size_t i = 0; i < auxiliaryArity; i++) {
                query.push_back(mk<ram::UndefValue>());
            }

            // ensure the length of query tuple is correct
            assert(query.size() == atom->getArity() && "wrong query tuple size");

            // create existence checks to check if the tuple exists or not
            auto existenceCheck = mk<ram::ExistenceCheck>(souffle::clone(relRef), std::move(query));
            auto negativeExistenceCheck = mk<ram::Negation>(souffle::clone(existenceCheck));

            // return true if the tuple exists
            VecOwn<ram::Expression> returnTrue;
            returnTrue.push_back(mk<ram::SignedConstant>(1));

            // return false if the tuple exists
            VecOwn<ram::Expression> returnFalse;
            returnFalse.push_back(mk<ram::SignedConstant>(0));

            // create a ram::Query to return true/false
            appendStmt(searchSequence, mk<ram::Query>(mk<ram::Filter>(std::move(existenceCheck),
                                               mk<ram::SubroutineReturn>(std::move(returnTrue)))));
            appendStmt(searchSequence, mk<ram::Query>(mk<ram::Filter>(std::move(negativeExistenceCheck),
                                               mk<ram::SubroutineReturn>(std::move(returnFalse)))));
        } else if (auto neg = dynamic_cast<ast::Negation*>(lit)) {
            auto atom = neg->getAtom();

            size_t auxiliaryArity = auxArityAnalysis->getArity(atom);
            // get a ram::RelationReference
            auto relRef = translateRelation(atom);
            // construct a query
            VecOwn<ram::Expression> query;

            // translate variables to subroutine arguments
            VariablesToArguments varsToArgs(uniqueVariables);
            atom->apply(varsToArgs);

            auto atomArgs = atom->getArguments();
            // add each value (subroutine argument) to the search query
            for (size_t i = 0; i < atom->getArity() - auxiliaryArity; i++) {
                auto arg = atomArgs[i];
                query.push_back(translateValue(arg, ValueIndex()));
            }

            // fill up query with nullptrs for the provenance columns
            for (size_t i = 0; i < auxiliaryArity; i++) {
                query.push_back(mk<ram::UndefValue>());
            }

            // ensure the length of query tuple is correct
            assert(query.size() == atom->getArity() && "wrong query tuple size");

            // create existence checks to check if the tuple exists or not
            auto existenceCheck = mk<ram::ExistenceCheck>(souffle::clone(relRef), std::move(query));
            auto negativeExistenceCheck = mk<ram::Negation>(souffle::clone(existenceCheck));

            // return true if the tuple exists
            VecOwn<ram::Expression> returnTrue;
            returnTrue.push_back(mk<ram::SignedConstant>(1));

            // return false if the tuple exists
            VecOwn<ram::Expression> returnFalse;
            returnFalse.push_back(mk<ram::SignedConstant>(0));

            // create a ram::Query to return true/false
            appendStmt(searchSequence, mk<ram::Query>(mk<ram::Filter>(std::move(existenceCheck),
                                               mk<ram::SubroutineReturn>(std::move(returnFalse)))));
            appendStmt(searchSequence, mk<ram::Query>(mk<ram::Filter>(std::move(negativeExistenceCheck),
                                               mk<ram::SubroutineReturn>(std::move(returnTrue)))));

        } else if (auto con = dynamic_cast<ast::Constraint*>(lit)) {
            VariablesToArguments varsToArgs(uniqueVariables);
            con->apply(varsToArgs);

            // translate to a ram::Condition
            auto condition = translateConstraint(con, ValueIndex());
            auto negativeCondition = mk<ram::Negation>(souffle::clone(condition));

            // create a return true value
            VecOwn<ram::Expression> returnTrue;
            returnTrue.push_back(mk<ram::SignedConstant>(1));

            // create a return false value
            VecOwn<ram::Expression> returnFalse;
            returnFalse.push_back(mk<ram::SignedConstant>(0));

            appendStmt(searchSequence, mk<ram::Query>(mk<ram::Filter>(std::move(condition),
                                               mk<ram::SubroutineReturn>(std::move(returnTrue)))));
            appendStmt(searchSequence, mk<ram::Query>(mk<ram::Filter>(std::move(negativeCondition),
                                               mk<ram::SubroutineReturn>(std::move(returnFalse)))));
        }

        litNumber++;
    }

    return mk<ram::Sequence>(std::move(searchSequence));
}

/** translates the given datalog program into an equivalent RAM program  */
void AstToRamTranslator::translateProgram(const ast::TranslationUnit& translationUnit) {
    // obtain IO Type of relations
    ioType = translationUnit.getAnalysis<ast::analysis::IOTypeAnalysis>();

    // obtain type environment from analysis
    typeEnv = &translationUnit.getAnalysis<ast::analysis::TypeEnvironmentAnalysis>()->getTypeEnvironment();

    // obtain recursive clauses from analysis
    const auto* recursiveClauses = translationUnit.getAnalysis<ast::analysis::RecursiveClausesAnalysis>();

    // obtain strongly connected component (SCC) graph from analysis
    const auto& sccGraph = *translationUnit.getAnalysis<ast::analysis::SCCGraphAnalysis>();

    // obtain some topological order over the nodes of the SCC graph
    const auto& sccOrder = *translationUnit.getAnalysis<ast::analysis::TopologicallySortedSCCGraphAnalysis>();

    // obtain the schedule of relations expired at each index of the topological order
    const auto& expirySchedule =
            translationUnit.getAnalysis<ast::analysis::RelationScheduleAnalysis>()->schedule();

    // get auxiliary arity analysis
    auxArityAnalysis = translationUnit.getAnalysis<ast::analysis::AuxiliaryArityAnalysis>();

    // determine the sips to use
    std::string sipsChosen = "all-bound";
    if (Global::config().has("RamSIPS")) {
        sipsChosen = Global::config().get("RamSIPS");
    }
    sips = ast::SipsMetric::create(sipsChosen, translationUnit);

    // handle the case of an empty SCC graph
    if (sccGraph.getNumberOfSCCs() == 0) return;

    // a function to load relations
    const auto& makeRamLoad = [&](VecOwn<ram::Statement>& current, const ast::Relation* relation) {
        for (auto directives : getInputDirectives(relation)) {
            Own<ram::Statement> statement =
                    mk<ram::IO>(Own<ram::RelationReference>(translateRelation(relation)), directives);
            if (Global::config().has("profile")) {
                const std::string logTimerStatement = LogStatement::tRelationLoadTime(
                        toString(relation->getQualifiedName()), relation->getSrcLoc());
                statement = mk<ram::LogRelationTimer>(std::move(statement), logTimerStatement,
                        Own<ram::RelationReference>(translateRelation(relation)));
            }
            appendStmt(current, std::move(statement));
        }
    };

    // a function to store relations
    const auto& makeRamStore = [&](VecOwn<ram::Statement>& current, const ast::Relation* relation) {
        for (auto directives : getOutputDirectives(relation)) {
            Own<ram::Statement> statement =
                    mk<ram::IO>(Own<ram::RelationReference>(translateRelation(relation)), directives);
            if (Global::config().has("profile")) {
                const std::string logTimerStatement = LogStatement::tRelationSaveTime(
                        toString(relation->getQualifiedName()), relation->getSrcLoc());
                statement = mk<ram::LogRelationTimer>(std::move(statement), logTimerStatement,
                        Own<ram::RelationReference>(translateRelation(relation)));
            }
            appendStmt(current, std::move(statement));
        }
    };

    // a function to drop relations
    const auto& makeRamClear = [&](VecOwn<ram::Statement>& current, const ast::Relation* relation) {
        appendStmt(current, mk<ram::Clear>(translateRelation(relation)));
    };

    // maintain the index of the SCC within the topological order
    size_t indexOfScc = 0;

    // create all Ram relations in ramRels
    for (const auto& scc : sccOrder.order()) {
        const auto& isRecursive = sccGraph.isRecursive(scc);
        const auto& allInterns = sccGraph.getInternalRelations(scc);
        for (const auto& rel : allInterns) {
            std::string name = rel->getQualifiedName().toString();
            auto arity = rel->getArity();
            auto auxiliaryArity = auxArityAnalysis->getArity(rel);
            auto representation = rel->getRepresentation();
            const auto& attributes = rel->getAttributes();
            std::vector<std::string> attributeNames;
            std::vector<std::string> attributeTypeQualifiers;
            for (size_t i = 0; i < rel->getArity(); ++i) {
                attributeNames.push_back(attributes[i]->getName());
                if (typeEnv != nullptr) {
                    attributeTypeQualifiers.push_back(
                            getTypeQualifier(typeEnv->getType(attributes[i]->getTypeName())));
                }
            }
            ramRels[name] = mk<ram::Relation>(
                    name, arity, auxiliaryArity, attributeNames, attributeTypeQualifiers, representation);
            if (isRecursive) {
                std::string deltaName = "@delta_" + name;
                std::string newName = "@new_" + name;
                ramRels[deltaName] = mk<ram::Relation>(deltaName, arity, auxiliaryArity, attributeNames,
                        attributeTypeQualifiers, representation);
                ramRels[newName] = mk<ram::Relation>(newName, arity, auxiliaryArity, attributeNames,
                        attributeTypeQualifiers, representation);
            }
        }
    }
    // iterate over each SCC according to the topological order
    for (const auto& scc : sccOrder.order()) {
        // make a new ram statement for the current SCC
        VecOwn<ram::Statement> current;

        // find out if the current SCC is recursive
        const auto& isRecursive = sccGraph.isRecursive(scc);

        // make variables for particular sets of relations contained within the current SCC, and,
        // predecessors and successor SCCs thereof
        const auto& allInterns = sccGraph.getInternalRelations(scc);
        const auto& internIns = sccGraph.getInternalInputRelations(scc);
        const auto& internOuts = sccGraph.getInternalOutputRelations(scc);

        // make a variable for all relations that are expired at the current SCC
        const auto& internExps = expirySchedule.at(indexOfScc).expired();

        // load all internal input relations from the facts dir with a .facts extension
        for (const auto& relation : internIns) {
            makeRamLoad(current, relation);
        }

        // compute the relations themselves
        Own<ram::Statement> bodyStatement =
                (!isRecursive) ? translateNonRecursiveRelation(
                                         *((const ast::Relation*)*allInterns.begin()), recursiveClauses)
                               : translateRecursiveRelation(allInterns, recursiveClauses);
        appendStmt(current, std::move(bodyStatement));

        // store all internal output relations to the output dir with a .csv extension
        for (const auto& relation : internOuts) {
            makeRamStore(current, relation);
        }

        // if provenance is not enabled...
        if (!Global::config().has("provenance")) {
            // otherwise, drop all  relations expired as per the topological order
            for (const auto& relation : internExps) {
                makeRamClear(current, relation);
            }
        }

        // create subroutine for this stratum
        ramSubs["stratum_" + std::to_string(indexOfScc)] = mk<ram::Sequence>(std::move(current));
        indexOfScc++;
    }

    // invoke all strata
    VecOwn<ram::Statement> res;
    for (size_t i = 0; i < indexOfScc; i++) {
        appendStmt(res, mk<ram::Call>("stratum_" + std::to_string(i)));
    }

    // add main timer if profiling
    if (res.size() > 0 && Global::config().has("profile")) {
        auto newStmt = mk<ram::LogTimer>(mk<ram::Sequence>(std::move(res)), LogStatement::runtime());
        res.clear();
        appendStmt(res, std::move(newStmt));
    }

    // done for main prog
    ramMain = mk<ram::Sequence>(std::move(res));

    // add subroutines for each clause
    if (Global::config().has("provenance")) {
        visitDepthFirst(*program, [&](const ast::Clause& clause) {
            std::stringstream relName;
            relName << clause.getHead()->getQualifiedName();

            // do not add subroutines for info relations or facts
            if (relName.str().find("@info") != std::string::npos || clause.getBodyLiterals().empty()) {
                return;
            }

            std::string subroutineLabel =
                    relName.str() + "_" + std::to_string(getClauseNum(program, &clause)) + "_subproof";
            ramSubs[subroutineLabel] = makeSubproofSubroutine(clause);

            std::string negationSubroutineLabel = relName.str() + "_" +
                                                  std::to_string(getClauseNum(program, &clause)) +
                                                  "_negation_subproof";
            ramSubs[negationSubroutineLabel] = makeNegationSubproofSubroutine(clause);
        });
    }
}

Own<ram::TranslationUnit> AstToRamTranslator::translateUnit(ast::TranslationUnit& tu) {
    auto ram_start = std::chrono::high_resolution_clock::now();
    program = &tu.getProgram();

    translateProgram(tu);
    SymbolTable& symTab = getSymbolTable();
    ErrorReport& errReport = tu.getErrorReport();
    DebugReport& debugReport = tu.getDebugReport();
    VecOwn<ram::Relation> rels;
    for (auto& cur : ramRels) {
        rels.push_back(std::move(cur.second));
    }
    if (ramMain == nullptr) {
        ramMain = mk<ram::Sequence>();
    }
    auto ramProg = mk<ram::Program>(std::move(rels), std::move(ramMain), std::move(ramSubs));
    if (!Global::config().get("debug-report").empty()) {
        if (ramProg) {
            auto ram_end = std::chrono::high_resolution_clock::now();
            std::string runtimeStr =
                    "(" + std::to_string(std::chrono::duration<double>(ram_end - ram_start).count()) + "s)";
            std::stringstream ramProgStr;
            ramProgStr << *ramProg;
            debugReport.addSection("ram-program", "RAM Program " + runtimeStr, ramProgStr.str());
        }
    }
    return mk<ram::TranslationUnit>(std::move(ramProg), std::move(symTab), errReport, debugReport);
}

}  // end of namespace souffle
