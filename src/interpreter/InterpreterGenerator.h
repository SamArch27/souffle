/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2019, The Souffle Developers. All rights reserved.
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file InterpreterGenerator.h
 *
 * Declares the Interpreter Generator class. The generator takes an entry
 * of the RAM program and translate it into an executable InterpreterNode representation
 * with environment symbol binding in each node.
 ***********************************************************************/

#pragma once

#include "Global.h"
#include "RelationTag.h"
#include "interpreter/InterpreterIndex.h"
#include "interpreter/InterpreterNode.h"
#include "interpreter/InterpreterRelation.h"
#include "interpreter/InterpreterViewContext.h"
#include "ram/AbstractExistenceCheck.h"
#include "ram/AbstractParallel.h"
#include "ram/Aggregate.h"
#include "ram/AutoIncrement.h"
#include "ram/Break.h"
#include "ram/Call.h"
#include "ram/Choice.h"
#include "ram/Clear.h"
#include "ram/Condition.h"
#include "ram/Conjunction.h"
#include "ram/Constant.h"
#include "ram/Constraint.h"
#include "ram/DebugInfo.h"
#include "ram/EmptinessCheck.h"
#include "ram/ExistenceCheck.h"
#include "ram/Exit.h"
#include "ram/Expression.h"
#include "ram/Extend.h"
#include "ram/False.h"
#include "ram/Filter.h"
#include "ram/IO.h"
#include "ram/IndexAggregate.h"
#include "ram/IndexChoice.h"
#include "ram/IndexOperation.h"
#include "ram/IndexScan.h"
#include "ram/IntrinsicOperator.h"
#include "ram/LogRelationTimer.h"
#include "ram/LogSize.h"
#include "ram/LogTimer.h"
#include "ram/Loop.h"
#include "ram/Negation.h"
#include "ram/NestedIntrinsicOperator.h"
#include "ram/NestedOperation.h"
#include "ram/Node.h"
#include "ram/Operation.h"
#include "ram/PackRecord.h"
#include "ram/Parallel.h"
#include "ram/ParallelAggregate.h"
#include "ram/ParallelChoice.h"
#include "ram/ParallelIndexAggregate.h"
#include "ram/ParallelIndexChoice.h"
#include "ram/ParallelIndexScan.h"
#include "ram/ParallelScan.h"
#include "ram/Program.h"
#include "ram/Project.h"
#include "ram/ProvenanceExistenceCheck.h"
#include "ram/Query.h"
#include "ram/Relation.h"
#include "ram/RelationSize.h"
#include "ram/Scan.h"
#include "ram/Sequence.h"
#include "ram/Statement.h"
#include "ram/SubroutineArgument.h"
#include "ram/SubroutineReturn.h"
#include "ram/Swap.h"
#include "ram/True.h"
#include "ram/TupleElement.h"
#include "ram/TupleOperation.h"
#include "ram/UndefValue.h"
#include "ram/UnpackRecord.h"
#include "ram/UserDefinedOperator.h"
#include "ram/Utils.h"
#include "ram/Visitor.h"
#include "ram/analysis/Index.h"
#include "souffle/RamTypes.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/MiscUtil.h"
#include <algorithm>
#include <array>
#include <cstddef>
#include <iterator>
#include <map>
#include <memory>
#include <queue>
#include <string>
#include <typeinfo>
#include <unordered_map>
#include <utility>
#include <vector>

namespace souffle {

/*
 * @class NodeGenerator
 * @brief Generate an executable InterpreterNode tree based on the RAM tree.
 *        Each node contains run time information which is necessary for InterpreterEngine to interpreter.
 */
class NodeGenerator : public ram::Visitor<Own<InterpreterNode>> {
    using NodePtr = Own<InterpreterNode>;
    using NodePtrVec = std::vector<NodePtr>;
    using RelationHandle = Own<InterpreterRelation>;

public:
    NodeGenerator(ram::analysis::IndexAnalysis* isa)
            : isa(isa), isProvenance(Global::config().has("provenance")),
              profileEnabled(Global::config().has("profile")) {}

    /**
     * @brief Generate the tree based on given entry.
     * Return a NodePtr to the root.
     */
    NodePtr generateTree(const ram::Node& root, const ram::Program& program) {
        this->program = const_cast<ram::Program*>(&program);
        // Encode all relation, indexPos and viewId.
        visitDepthFirst(root, [&](const ram::Node& node) {
            if (isA<ram::Query>(&node)) {
                newQueryBlock();
            }
            if (const auto* indexSearch = dynamic_cast<const ram::IndexOperation*>(&node)) {
                encodeIndexPos(*indexSearch);
                encodeView(indexSearch);
            } else if (const auto* exists = dynamic_cast<const ram::ExistenceCheck*>(&node)) {
                encodeIndexPos(*exists);
                encodeView(exists);
            } else if (const auto* provExists = dynamic_cast<const ram::ProvenanceExistenceCheck*>(&node)) {
                encodeIndexPos(*provExists);
                encodeView(provExists);
            }
        });
        // Parse program
        return visit(root);
    }

    NodePtr visitConstant(const ram::Constant& num) override {
        return mk<InterpreterConstant>(I_Constant, &num);
    }

    NodePtr visitTupleElement(const ram::TupleElement& access) override {
        return mk<InterpreterTupleElement>(I_TupleElement, &access);
    }

    NodePtr visitAutoIncrement(const ram::AutoIncrement& inc) override {
        return mk<InterpreterAutoIncrement>(I_AutoIncrement, &inc);
    }

    NodePtr visitIntrinsicOperator(const ram::IntrinsicOperator& op) override {
        NodePtrVec children;
        for (const auto& arg : op.getArguments()) {
            children.push_back(visit(arg));
        }
        return mk<InterpreterIntrinsicOperator>(I_IntrinsicOperator, &op, std::move(children));
    }

    NodePtr visitUserDefinedOperator(const ram::UserDefinedOperator& op) override {
        NodePtrVec children;
        for (const auto& arg : op.getArguments()) {
            children.push_back(visit(arg));
        }
        return mk<InterpreterUserDefinedOperator>(I_UserDefinedOperator, &op, std::move(children));
    }

    NodePtr visitNestedIntrinsicOperator(const ram::NestedIntrinsicOperator& op) override {
        NodePtrVec children;
        for (auto&& arg : op.getArguments()) {
            children.push_back(visit(arg));
        }
        children.push_back(visitTupleOperation(op));
        return mk<InterpreterNestedIntrinsicOperator>(I_NestedIntrinsicOperator, &op, std::move(children));
    }

    NodePtr visitPackRecord(const ram::PackRecord& pr) override {
        NodePtrVec children;
        for (const auto& arg : pr.getArguments()) {
            children.push_back(visit(arg));
        }
        return mk<InterpreterPackRecord>(I_PackRecord, &pr, std::move(children));
    }

    NodePtr visitSubroutineArgument(const ram::SubroutineArgument& arg) override {
        return mk<InterpreterSubroutineArgument>(I_SubroutineArgument, &arg);
    }

    // -- connectors operators --
    NodePtr visitTrue(const ram::True& ltrue) override {
        return mk<InterpreterTrue>(I_True, &ltrue);
    }

    NodePtr visitFalse(const ram::False& lfalse) override {
        return mk<InterpreterFalse>(I_False, &lfalse);
    }

    NodePtr visitConjunction(const ram::Conjunction& conj) override {
        return mk<InterpreterConjunction>(I_Conjunction, &conj, visit(conj.getLHS()), visit(conj.getRHS()));
    }

    NodePtr visitNegation(const ram::Negation& neg) override {
        return mk<InterpreterNegation>(I_Negation, &neg, visit(neg.getOperand()));
    }

    NodePtr visitEmptinessCheck(const ram::EmptinessCheck& emptiness) override {
        size_t relId = encodeRelation(emptiness.getRelation());
        auto rel = relations[relId].get();
        return mk<InterpreterEmptinessCheck>(I_EmptinessCheck, &emptiness, rel);
    }

    NodePtr visitRelationSize(const ram::RelationSize& size) override {
        size_t relId = encodeRelation(size.getRelation());
        auto rel = relations[relId].get();
        return mk<InterpreterRelationSize>(I_RelationSize, &size, rel);
    }

    NodePtr visitExistenceCheck(const ram::ExistenceCheck& exists) override {
        InterpreterSuperInstruction superOp = getExistenceSuperInstInfo(exists);
        // Check if the search signature is a total signature
        bool isTotal = true;
        for (const auto& cur : exists.getValues()) {
            if (isUndefValue(cur)) {
                isTotal = false;
            }
        }
        return mk<InterpreterExistenceCheck>(
                I_ExistenceCheck, &exists, isTotal, encodeView(&exists), std::move(superOp));
    }

    NodePtr visitProvenanceExistenceCheck(const ram::ProvenanceExistenceCheck& provExists) override {
        InterpreterSuperInstruction superOp = getExistenceSuperInstInfo(provExists);
        return mk<InterpreterProvenanceExistenceCheck>(I_ProvenanceExistenceCheck, &provExists,
                visit(provExists.getChildNodes().back()), encodeView(&provExists), std::move(superOp));
    }

    // -- comparison operators --
    NodePtr visitConstraint(const ram::Constraint& relOp) override {
        return mk<InterpreterConstraint>(I_Constraint, &relOp, visit(relOp.getLHS()), visit(relOp.getRHS()));
    }

    NodePtr visitNestedOperation(const ram::NestedOperation& nested) override {
        return visit(nested.getOperation());
    }

    NodePtr visitTupleOperation(const ram::TupleOperation& search) override {
        if (profileEnabled) {
            return mk<InterpreterTupleOperation>(I_TupleOperation, &search, visit(search.getOperation()));
        }
        return visit(search.getOperation());
    }

    NodePtr visitScan(const ram::Scan& scan) override {
        size_t relId = encodeRelation(scan.getRelation());
        auto rel = relations[relId].get();
        return mk<InterpreterScan>(I_Scan, &scan, rel, visitTupleOperation(scan));
    }

    NodePtr visitParallelScan(const ram::ParallelScan& pScan) override {
        size_t relId = encodeRelation(pScan.getRelation());
        auto rel = relations[relId].get();
        auto res = mk<InterpreterParallelScan>(I_ParallelScan, &pScan, rel, visitTupleOperation(pScan));
        res->setViewContext(parentQueryViewContext);
        return res;
    }

    NodePtr visitIndexScan(const ram::IndexScan& scan) override {
        InterpreterSuperInstruction indexOperation = getIndexSuperInstInfo(scan);
        NodePtrVec children;
        children.push_back(visitTupleOperation(scan));
        return mk<InterpreterIndexScan>(I_IndexScan, &scan, nullptr, visitTupleOperation(scan),
                encodeView(&scan), std::move(indexOperation));
    }

    NodePtr visitParallelIndexScan(const ram::ParallelIndexScan& piscan) override {
        size_t relId = encodeRelation(piscan.getRelation());
        auto rel = relations[relId].get();
        InterpreterSuperInstruction indexOperation = getIndexSuperInstInfo(piscan);
        auto res = mk<InterpreterParallelIndexScan>(I_ParallelIndexScan, &piscan, rel,
                visitTupleOperation(piscan), encodeIndexPos(piscan), std::move(indexOperation));
        res->setViewContext(parentQueryViewContext);
        return res;
    }

    NodePtr visitChoice(const ram::Choice& choice) override {
        size_t relId = encodeRelation(choice.getRelation());
        auto rel = relations[relId].get();
        return mk<InterpreterChoice>(
                I_Choice, &choice, rel, visit(choice.getCondition()), visitTupleOperation(choice));
    }

    NodePtr visitParallelChoice(const ram::ParallelChoice& pchoice) override {
        size_t relId = encodeRelation(pchoice.getRelation());
        auto rel = relations[relId].get();
        auto res = mk<InterpreterParallelChoice>(
                I_ParallelChoice, &pchoice, rel, visit(pchoice.getCondition()), visitTupleOperation(pchoice));
        res->setViewContext(parentQueryViewContext);
        return res;
    }

    NodePtr visitIndexChoice(const ram::IndexChoice& choice) override {
        InterpreterSuperInstruction indexOperation = getIndexSuperInstInfo(choice);
        return mk<InterpreterIndexChoice>(I_IndexChoice, &choice, nullptr, visit(choice.getCondition()),
                visitTupleOperation(choice), encodeView(&choice), std::move(indexOperation));
    }

    NodePtr visitParallelIndexChoice(const ram::ParallelIndexChoice& ichoice) override {
        InterpreterSuperInstruction indexOperation = getIndexSuperInstInfo(ichoice);
        size_t relId = encodeRelation(ichoice.getRelation());
        auto rel = relations[relId].get();
        auto res = mk<InterpreterParallelIndexChoice>(I_ParallelIndexChoice, &ichoice, rel,
                visit(ichoice.getCondition()), visit(ichoice.getOperation()), encodeIndexPos(ichoice),
                std::move(indexOperation));
        res->setViewContext(parentQueryViewContext);
        return res;
    }

    NodePtr visitUnpackRecord(const ram::UnpackRecord& lookup) override {  // get reference
        return mk<InterpreterUnpackRecord>(
                I_UnpackRecord, &lookup, visit(lookup.getExpression()), visitTupleOperation(lookup));
    }

    NodePtr visitAggregate(const ram::Aggregate& aggregate) override {
        size_t relId = encodeRelation(aggregate.getRelation());
        auto rel = relations[relId].get();
        return mk<InterpreterAggregate>(I_Aggregate, &aggregate, rel, visit(aggregate.getExpression()),
                visit(aggregate.getCondition()), visitTupleOperation(aggregate));
    }

    NodePtr visitParallelAggregate(const ram::ParallelAggregate& aggregate) override {
        size_t relId = encodeRelation(aggregate.getRelation());
        auto rel = relations[relId].get();
        auto res = mk<InterpreterParallelAggregate>(I_ParallelAggregate, &aggregate, rel,
                visit(aggregate.getExpression()), visit(aggregate.getCondition()),
                visitTupleOperation(aggregate));
        res->setViewContext(parentQueryViewContext);
        return res;
    }

    NodePtr visitIndexAggregate(const ram::IndexAggregate& aggregate) override {
        InterpreterSuperInstruction indexOperation = getIndexSuperInstInfo(aggregate);
        size_t relId = encodeRelation(aggregate.getRelation());
        auto rel = relations[relId].get();
        return mk<InterpreterIndexAggregate>(I_IndexAggregate, &aggregate, rel,
                visit(aggregate.getExpression()), visit(aggregate.getCondition()),
                visitTupleOperation(aggregate), encodeView(&aggregate), std::move(indexOperation));
    }

    NodePtr visitParallelIndexAggregate(const ram::ParallelIndexAggregate& aggregate) override {
        InterpreterSuperInstruction indexOperation = getIndexSuperInstInfo(aggregate);
        size_t relId = encodeRelation(aggregate.getRelation());
        auto rel = relations[relId].get();
        auto res = mk<InterpreterParallelIndexAggregate>(I_ParallelIndexAggregate, &aggregate, rel,
                visit(aggregate.getExpression()), visit(aggregate.getCondition()),
                visitTupleOperation(aggregate), encodeView(&aggregate), std::move(indexOperation));
        res->setViewContext(parentQueryViewContext);
        return res;
    }

    NodePtr visitBreak(const ram::Break& breakOp) override {
        return mk<InterpreterBreak>(
                I_Break, &breakOp, visit(breakOp.getCondition()), visit(breakOp.getOperation()));
    }

    NodePtr visitFilter(const ram::Filter& filter) override {
        return mk<InterpreterFilter>(
                I_Filter, &filter, visit(filter.getCondition()), visit(filter.getOperation()));
    }

    NodePtr visitProject(const ram::Project& project) override {
        InterpreterSuperInstruction superOp = getProjectSuperInstInfo(project);
        size_t relId = encodeRelation(project.getRelation());
        auto rel = relations[relId].get();
        return mk<InterpreterProject>(I_Project, &project, rel, std::move(superOp));
    }

    // -- return from subroutine --
    NodePtr visitSubroutineReturn(const ram::SubroutineReturn& ret) override {
        NodePtrVec children;
        for (const auto& value : ret.getValues()) {
            children.push_back(visit(value));
        }
        return mk<InterpreterSubroutineReturn>(I_SubroutineReturn, &ret, std::move(children));
    }

    NodePtr visitSequence(const ram::Sequence& seq) override {
        NodePtrVec children;
        for (const auto& value : seq.getStatements()) {
            children.push_back(visit(value));
        }
        return mk<InterpreterSequence>(I_Sequence, &seq, std::move(children));
    }

    NodePtr visitParallel(const ram::Parallel& parallel) override {
        // Parallel statements are executed in sequence for now.
        NodePtrVec children;
        for (const auto& value : parallel.getStatements()) {
            children.push_back(visit(value));
        }
        return mk<InterpreterParallel>(I_Parallel, &parallel, std::move(children));
    }

    NodePtr visitLoop(const ram::Loop& loop) override {
        return mk<InterpreterLoop>(I_Loop, &loop, visit(loop.getBody()));
    }

    NodePtr visitExit(const ram::Exit& exit) override {
        return mk<InterpreterExit>(I_Exit, &exit, visit(exit.getCondition()));
    }

    NodePtr visitCall(const ram::Call& call) override {
        // translate a subroutine name to an index
        // the index is used to identify the subroutine
        // in the interpreter. The index is stored in the
        // data array of the InterpreterNode as the first
        // entry.
        auto subs = program->getSubroutines();
        size_t subroutineId = distance(subs.begin(), subs.find(call.getName()));
        return mk<InterpreterCall>(I_Call, &call, subroutineId);
    }

    NodePtr visitLogRelationTimer(const ram::LogRelationTimer& timer) override {
        size_t relId = encodeRelation(timer.getRelation());
        auto rel = relations[relId].get();
        NodePtrVec children;
        children.push_back(visit(timer.getStatement()));
        return mk<InterpreterLogRelationTimer>(I_LogRelationTimer, &timer, visit(timer.getStatement()), rel);
    }

    NodePtr visitLogTimer(const ram::LogTimer& timer) override {
        NodePtrVec children;
        children.push_back(visit(timer.getStatement()));
        return mk<InterpreterLogTimer>(I_LogTimer, &timer, visit(timer.getStatement()));
    }

    NodePtr visitDebugInfo(const ram::DebugInfo& dbg) override {
        NodePtrVec children;
        children.push_back(visit(dbg.getStatement()));
        return mk<InterpreterDebugInfo>(I_DebugInfo, &dbg, visit(dbg.getStatement()));
    }

    NodePtr visitClear(const ram::Clear& clear) override {
        size_t relId = encodeRelation(clear.getRelation());
        auto rel = relations[relId].get();
        return mk<InterpreterClear>(I_Clear, &clear, rel);
    }

    NodePtr visitLogSize(const ram::LogSize& size) override {
        size_t relId = encodeRelation(size.getRelation());
        auto rel = relations[relId].get();
        return mk<InterpreterLogSize>(I_LogSize, &size, rel);
    }

    NodePtr visitIO(const ram::IO& io) override {
        size_t relId = encodeRelation(io.getRelation());
        auto rel = relations[relId].get();
        return mk<InterpreterIO>(I_IO, &io, rel);
    }

    NodePtr visitQuery(const ram::Query& query) override {
        std::shared_ptr<InterpreterViewContext> viewContext = std::make_shared<InterpreterViewContext>();
        parentQueryViewContext = viewContext;
        // split terms of conditions of outer-most filter operation
        // into terms that require a context and terms that
        // do not require a view
        const ram::Operation* next = &query.getOperation();
        std::vector<const ram::Condition*> freeOfView;
        if (const auto* filter = dynamic_cast<const ram::Filter*>(&query.getOperation())) {
            next = &filter->getOperation();
            // Check terms of outer filter operation whether they can be pushed before
            // the view-generation for speed improvements
            auto conditions = toConjunctionList(&filter->getCondition());
            for (auto const& cur : conditions) {
                bool needView = false;
                visitDepthFirst(*cur, [&](const ram::Node& node) {
                    if (requireView(&node)) {
                        needView = true;
                        const auto& rel = getRelationRefForView(&node);
                        viewContext->addViewInfoForFilter(
                                encodeRelation(rel), indexTable[&node], encodeView(&node));
                    }
                });

                if (needView) {
                    viewContext->addViewOperationForFilter(visit(*cur));
                } else {
                    viewContext->addViewFreeOperationForFilter(visit(*cur));
                }
            }
        }

        visitDepthFirst(*next, [&](const ram::Node& node) {
            if (requireView(&node)) {
                const auto& rel = getRelationRefForView(&node);
                viewContext->addViewInfoForNested(encodeRelation(rel), indexTable[&node], encodeView(&node));
            };
        });

        visitDepthFirst(*next, [&](const ram::AbstractParallel&) { viewContext->isParallel = true; });

        NodePtrVec children;
        children.push_back(visit(*next));

        auto res = mk<InterpreterQuery>(I_Query, &query, visit(*next));
        res->setViewContext(parentQueryViewContext);
        return res;
    }

    NodePtr visitExtend(const ram::Extend& extend) override {
        size_t src = encodeRelation(extend.getFirstRelation());
        size_t target = encodeRelation(extend.getSecondRelation());
        return mk<InterpreterExtend>(I_Extend, &extend, src, target);
    }

    NodePtr visitSwap(const ram::Swap& swap) override {
        size_t src = encodeRelation(swap.getFirstRelation());
        size_t target = encodeRelation(swap.getSecondRelation());
        return mk<InterpreterSwap>(I_Swap, &swap, src, target);
    }

    NodePtr visitUndefValue(const ram::UndefValue&) override {
        return nullptr;
    }

    NodePtr visitNode(const ram::Node& node) override {
        fatal("unsupported node type: %s", typeid(node).name());
    }

public:
    /** @brief Move relation map */
    VecOwn<RelationHandle>& getRelations() {
        return relations;
    }

    /** @brief Return relation handle from given index */
    RelationHandle& getRelationHandle(const size_t idx) {
        return *relations[idx];
    }

private:
    /** Environment encoding, store a mapping from ram::Node to its operation index id. */
    std::unordered_map<const ram::Node*, size_t> indexTable;
    /** Used by index encoding */
    ram::analysis::IndexAnalysis* isa;
    /** Points to the current viewContext during the generation.
     * It is used to passing viewContext between parent query and its nested parallel operation.
     * As parallel operation requires its own view information. */
    std::shared_ptr<InterpreterViewContext> parentQueryViewContext = nullptr;
    /** Next available location to encode View */
    size_t viewId = 0;
    /** Next available location to encode a relation */
    size_t relId = 0;
    /** Environment encoding, store a mapping from ram::Node to its View id. */
    std::unordered_map<const ram::Node*, size_t> viewTable;
    /** Environment encoding, store a mapping from ram::Relation to its id */
    std::unordered_map<const ram::Relation*, size_t> relTable;
    /** Symbol table for relations */
    VecOwn<RelationHandle> relations;
    /** If generating a provenance program */
    const bool isProvenance;
    /** If profile is enable in this program */
    const bool profileEnabled;
    /** ram::Program */
    ram::Program* program;

    /** @brief Reset view allocation system, since view's life time is within each query. */
    void newQueryBlock() {
        viewTable.clear();
        viewId = 0;
    }

    /** @brief Get a valid relation id for encoding */
    size_t getNewRelId() {
        return relId++;
    }

    /** @brief Get a valid view id for encoding */
    size_t getNextViewId() {
        return viewId++;
    }

    /** @brief Return operation index id from the result of indexAnalysis */
    template <class RamNode>
    size_t encodeIndexPos(RamNode& node) {
        const ram::analysis::MinIndexSelection& orderSet = isa->getIndexes(node.getRelation());
        ram::analysis::SearchSignature signature =
                ram::analysis::SearchSignature::getFixed(isa->getSearchSignature(&node));
        // A zero signature is equivalent as a full order signature.
        if (signature.empty()) {
            signature = ram::analysis::SearchSignature::getFullSearchSignature(signature.arity());
        }
        auto i = orderSet.getLexOrderNum(signature);
        indexTable[&node] = i;
        return i;
    };

    /** @brief Encode and return the View id of an operation. */
    size_t encodeView(const ram::Node* node) {
        auto pos = viewTable.find(node);
        if (pos != viewTable.end()) {
            return pos->second;
        }
        size_t id = getNextViewId();
        viewTable[node] = id;
        return id;
    }

    /** @brief Encode and create the relation, return the relation id */
    size_t encodeRelation(const ram::Relation& rel) {
        auto pos = relTable.find(&rel);
        if (pos != relTable.end()) {
            return pos->second;
        }
        size_t id = getNewRelId();
        relTable[&rel] = id;
        createRelation(rel, isa->getIndexes(rel), id);
        return id;
    }

    /**
     * @brief Find all operations under the root node that requires a view.
     * Return a list of InterpreterNodes.
     */
    NodePtrVec findAllViews(const ram::Node& node) {
        NodePtrVec res;
        visitDepthFirst(node, [&](const ram::Node& node) {
            if (requireView(&node)) {
                res.push_back(visit(node));
            };
        });
        return res;
    }

    /**
     * Return true if the given operation requires a view.
     */
    bool requireView(const ram::Node* node) {
        if (isA<ram::AbstractExistenceCheck>(node)) {
            return true;
        } else if (isA<ram::IndexOperation>(node)) {
            return true;
        }
        return false;
    }

    /**
     * @brief Return the associated relation of a operation which requires a view.
     * This function assume the operation does requires a view.
     */
    const ram::Relation& getRelationRefForView(const ram::Node* node) {
        if (const auto* exist = dynamic_cast<const ram::AbstractExistenceCheck*>(node)) {
            return exist->getRelation();
        } else if (const auto* index = dynamic_cast<const ram::IndexOperation*>(node)) {
            return index->getRelation();
        }

        fatal("The ram::Node does not require a view.");
    }

    /**
     * @brief Convert terms of a conjunction to a list
     *
     * Convert a condition of the format C1 /\ C2 /\ ... /\ Cn
     * to a list {C1, C2, ..., Cn}.
     */
    inline std::vector<const ram::Condition*> toConjunctionList(const ram::Condition* condition) {
        std::vector<const ram::Condition*> conditionList;
        std::queue<const ram::Condition*> conditionsToProcess;
        if (condition != nullptr) {
            conditionsToProcess.push(condition);
            while (!conditionsToProcess.empty()) {
                condition = conditionsToProcess.front();
                conditionsToProcess.pop();
                if (const auto* ramConj = dynamic_cast<const ram::Conjunction*>(condition)) {
                    conditionsToProcess.push(&ramConj->getLHS());
                    conditionsToProcess.push(&ramConj->getRHS());
                } else {
                    conditionList.emplace_back(condition);
                }
            }
        }
        return conditionList;
    }

    /**
     * @brief Create and add relation into the runtime environment.
     */
    void createRelation(
            const ram::Relation& id, const ram::analysis::MinIndexSelection& orderSet, const size_t idx) {
        RelationHandle res;
        if (relations.size() < idx + 1) {
            relations.resize(idx + 1);
        }
        if (id.getRepresentation() == RelationRepresentation::EQREL) {
            res = mk<InterpreterEqRelation>(id.getArity(), id.getAuxiliaryArity(), id.getName(),
                    std::vector<std::string>(), orderSet);
        } else {
            if (isProvenance) {
                res = mk<InterpreterRelation>(id.getArity(), id.getAuxiliaryArity(), id.getName(),
                        std::vector<std::string>(), orderSet, createBTreeProvenanceIndex);
            } else {
                res = mk<InterpreterRelation>(id.getArity(), id.getAuxiliaryArity(), id.getName(),
                        std::vector<std::string>(), orderSet);
            }
        }
        relations[idx] = mk<RelationHandle>(std::move(res));
    }

    /**
     * @brief Encode and return the super-instruction information about a index operation.
     */
    InterpreterSuperInstruction getIndexSuperInstInfo(const ram::IndexOperation& ramIndex) {
        size_t arity = ramIndex.getRelation().getArity();
        InterpreterSuperInstruction indexOperation(arity);
        const auto& first = ramIndex.getRangePattern().first;
        for (size_t i = 0; i < arity; ++i) {
            auto& low = first[i];
            // Unbounded
            if (isUndefValue(low)) {
                indexOperation.first[i] = MIN_RAM_SIGNED;
                continue;
            }

            // Constant
            if (isA<ram::Constant>(low)) {
                indexOperation.first[i] = dynamic_cast<ram::Constant*>(low)->getConstant();
                continue;
            }

            // TupleElement
            if (isA<ram::TupleElement>(low)) {
                auto lowTuple = dynamic_cast<ram::TupleElement*>(low);
                indexOperation.tupleFirst.push_back(
                        {i, (size_t)lowTuple->getTupleId(), lowTuple->getElement()});
                continue;
            }

            // Generic expression
            indexOperation.exprFirst.push_back(std::pair<size_t, Own<InterpreterNode>>(i, visit(low)));
        }
        const auto& second = ramIndex.getRangePattern().second;
        for (size_t i = 0; i < arity; ++i) {
            auto& hig = second[i];
            // Unbounded
            if (isUndefValue(hig)) {
                indexOperation.second[i] = MAX_RAM_SIGNED;
                continue;
            }

            // Constant
            if (isA<ram::Constant>(hig)) {
                indexOperation.second[i] = dynamic_cast<ram::Constant*>(hig)->getConstant();
                continue;
            }

            // TupleElement
            if (isA<ram::TupleElement>(hig)) {
                auto highTuple = dynamic_cast<ram::TupleElement*>(hig);
                indexOperation.tupleSecond.push_back(
                        {i, (size_t)highTuple->getTupleId(), highTuple->getElement()});
                continue;
            }

            // Generic expression
            indexOperation.exprSecond.push_back(std::pair<size_t, Own<InterpreterNode>>(i, visit(hig)));
        }
        return indexOperation;
    }

    /**
     * @brief Encode and return the super-instruction information about an existence check operation
     */
    InterpreterSuperInstruction getExistenceSuperInstInfo(const ram::AbstractExistenceCheck& exist) {
        size_t arity = exist.getRelation().getArity();
        InterpreterSuperInstruction superOp(arity);
        const auto& children = exist.getValues();
        for (size_t i = 0; i < arity; ++i) {
            auto& child = children[i];
            // Unbounded
            if (isUndefValue(child)) {
                superOp.first[i] = MIN_RAM_SIGNED;
                superOp.second[i] = MAX_RAM_SIGNED;
                continue;
            }

            // Constant
            if (isA<ram::Constant>(child)) {
                superOp.first[i] = dynamic_cast<ram::Constant*>(child)->getConstant();
                superOp.second[i] = superOp.first[i];
                continue;
            }

            // TupleElement
            if (isA<ram::TupleElement>(child)) {
                auto tuple = dynamic_cast<ram::TupleElement*>(child);
                superOp.tupleFirst.push_back({i, (size_t)tuple->getTupleId(), tuple->getElement()});
                continue;
            }

            // Generic expression
            superOp.exprFirst.push_back(std::pair<size_t, Own<InterpreterNode>>(i, visit(child)));
        }
        return superOp;
    }

    /**
     * @brief Encode and return the super-instruction information about a project operation
     */
    InterpreterSuperInstruction getProjectSuperInstInfo(const ram::Project& exist) {
        size_t arity = exist.getRelation().getArity();
        InterpreterSuperInstruction superOp(arity);
        const auto& children = exist.getValues();
        for (size_t i = 0; i < arity; ++i) {
            auto& child = children[i];
            // Constant
            if (isA<ram::Constant>(child)) {
                superOp.first[i] = dynamic_cast<ram::Constant*>(child)->getConstant();
                continue;
            }

            // TupleElement
            if (isA<ram::TupleElement>(child)) {
                auto tuple = dynamic_cast<ram::TupleElement*>(child);
                superOp.tupleFirst.push_back({i, (size_t)tuple->getTupleId(), tuple->getElement()});
                continue;
            }

            // Generic expression
            superOp.exprFirst.push_back(std::pair<size_t, Own<InterpreterNode>>(i, visit(child)));
        }
        return superOp;
    }
};
}  // namespace souffle
