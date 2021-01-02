/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2019, The Souffle Developers. All rights reserved.
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Generator.h
 *
 * Declares the Interpreter Generator class. The generator takes an entry
 * of the RAM program and translate it into an executable Node representation
 * with environment symbol binding in each node.
 ***********************************************************************/

#pragma once

#include "Global.h"
#include "RelationTag.h"
#include "interpreter/Index.h"
#include "interpreter/Relation.h"
#include "interpreter/ViewContext.h"
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
#include "ram/analysis/Index.h"
#include "ram/utility/Utils.h"
#include "ram/utility/Visitor.h"
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

namespace souffle::interpreter {
class Engine;
/*
 * @class NodeGenerator
 * @brief Generate an executable Node tree based on the RAM tree.
 *        Each node contains run time information which is necessary for Engine to interpreter.
 */
class NodeGenerator : public ram::Visitor<Own<Node>> {
    using NodePtr = Own<Node>;
    using NodePtrVec = std::vector<NodePtr>;
    using RelationHandle = Own<RelationWrapper>;

public:
    NodeGenerator(Engine& engine);

    /**
     * @brief Generate the tree based on given entry.
     * Return a NodePtr to the root.
     */
    NodePtr generateTree(const ram::Node& root);

    NodePtr visitConstant(const ram::Constant& num) override;

    NodePtr visitTupleElement(const ram::TupleElement& access) override;

    NodePtr visitAutoIncrement(const ram::AutoIncrement& inc) override;

    NodePtr visitIntrinsicOperator(const ram::IntrinsicOperator& op) override;

    NodePtr visitUserDefinedOperator(const ram::UserDefinedOperator& op) override;

    NodePtr visitNestedIntrinsicOperator(const ram::NestedIntrinsicOperator& op) override;

    NodePtr visitPackRecord(const ram::PackRecord& pr) override;

    NodePtr visitSubroutineArgument(const ram::SubroutineArgument& arg) override;

    NodePtr visitTrue(const ram::True& ltrue) override;

    NodePtr visitFalse(const ram::False& lfalse) override;

    NodePtr visitConjunction(const ram::Conjunction& conj) override;

    NodePtr visitNegation(const ram::Negation& neg) override;

    NodePtr visitEmptinessCheck(const ram::EmptinessCheck& emptiness) override;

    NodePtr visitRelationSize(const ram::RelationSize& size) override;

    NodePtr visitExistenceCheck(const ram::ExistenceCheck& exists) override;

    NodePtr visitProvenanceExistenceCheck(const ram::ProvenanceExistenceCheck& provExists) override;

    NodePtr visitConstraint(const ram::Constraint& relOp) override;

    NodePtr visitNestedOperation(const ram::NestedOperation& nested) override;

    NodePtr visitTupleOperation(const ram::TupleOperation& search) override;

    NodePtr visitScan(const ram::Scan& scan) override;

    NodePtr visitParallelScan(const ram::ParallelScan& pScan) override;

    NodePtr visitIndexScan(const ram::IndexScan& iScan) override;

    NodePtr visitParallelIndexScan(const ram::ParallelIndexScan& piscan) override;

    NodePtr visitChoice(const ram::Choice& choice) override;

    NodePtr visitParallelChoice(const ram::ParallelChoice& pChoice) override;

    NodePtr visitIndexChoice(const ram::IndexChoice& iChoice) override;

    NodePtr visitParallelIndexChoice(const ram::ParallelIndexChoice& piChoice) override;

    NodePtr visitUnpackRecord(const ram::UnpackRecord& unpack) override;

    NodePtr visitAggregate(const ram::Aggregate& aggregate) override;

    NodePtr visitParallelAggregate(const ram::ParallelAggregate& pAggregate) override;

    NodePtr visitIndexAggregate(const ram::IndexAggregate& iAggregate) override;

    NodePtr visitParallelIndexAggregate(const ram::ParallelIndexAggregate& piAggregate) override;

    NodePtr visitBreak(const ram::Break& breakOp) override;

    NodePtr visitFilter(const ram::Filter& filter) override;

    NodePtr visitGuardedProject(const ram::GuardedProject& guardedPorject) override;

    NodePtr visitProject(const ram::Project& project) override;

    NodePtr visitSubroutineReturn(const ram::SubroutineReturn& ret) override;

    NodePtr visitSequence(const ram::Sequence& seq) override;

    NodePtr visitParallel(const ram::Parallel& parallel) override;

    NodePtr visitLoop(const ram::Loop& loop) override;

    NodePtr visitExit(const ram::Exit& exit) override;

    NodePtr visitCall(const ram::Call& call) override;

    NodePtr visitLogRelationTimer(const ram::LogRelationTimer& timer) override;

    NodePtr visitLogTimer(const ram::LogTimer& timer) override;

    NodePtr visitDebugInfo(const ram::DebugInfo& dbg) override;

    NodePtr visitClear(const ram::Clear& clear) override;

    NodePtr visitLogSize(const ram::LogSize& size) override;

    NodePtr visitIO(const ram::IO& io) override;

    NodePtr visitQuery(const ram::Query& query) override;

    NodePtr visitExtend(const ram::Extend& extend) override;

    NodePtr visitSwap(const ram::Swap& swap) override;

    NodePtr visitUndefValue(const ram::UndefValue&) override;

    NodePtr visitNode(const ram::Node& node) override;

private:
    /**
     * @class OrderingContext
     * @brief This class help generator reordering tuple access based on the index oder.
     */
    class OrderingContext {
    public:
        OrderingContext(NodeGenerator& generator);

        /** @brief Bind tuple with a natural full order.
         *
         * This is usually used when an operation implicitly introduce a runtime tuple, such as UnpackRecord
         * NestedIntrinsicOperator, and nested operation in Aggregate.
         * */
        void addNewTuple(size_t tupleId, size_t arity);

        /** @brief Bind tuple with the default order.
         *
         * This is usually used for tuples created by non-indexed operations. Such as Scan, Aggregate, Choice.
         * */
        template <class RamNode>
        void addTupleWithDefaultOrder(size_t tupleId, const RamNode& node);

        /** @brief Bind tuple with the corresponding index order.
         *
         * This is usually used for tuples created by indexed operations. Such as IndexScan, IndexAggregate,
         * IndexChoice.
         * */
        template <class RamNode>
        void addTupleWithIndexOrder(size_t tupleId, const RamNode& node);

        /** @brief Map the decoded order of elementId based on current context */
        size_t mapOrder(size_t tupleId, size_t elementId) const;

    private:
        void insertOrder(size_t tupleId, const Order& order);
        std::vector<Order> tupleOrders;
        NodeGenerator& generator;
    };

private:
    /** @brief Reset view allocation system, since view's life time is within each query. */
    void newQueryBlock();

    /** @brief Get a valid relation id for encoding */
    size_t getNewRelId();

    /** @brief Get a valid view id for encoding */
    size_t getNextViewId();

    /** @brief Return operation index id from the result of indexAnalysis */
    template <class RamNode>
    size_t encodeIndexPos(RamNode& node);

    /** @brief Encode and return the View id of an operation. */
    size_t encodeView(const ram::Node* node);

    /** @brief get arity of relation */
    const ram::Relation& lookup(const std::string& relName);

    /** @brief get arity of relation */
    size_t getArity(const std::string& relName);

    /** @brief Encode and create the relation, return the relation id */
    size_t encodeRelation(const std::string& relName);

    /* @brief Get a relation instance from engine */
    RelationHandle* getRelationHandle(const size_t idx);

    /**
     * Return true if the given operation requires a view.
     */
    bool requireView(const ram::Node* node);

    /**
     * @brief Return the associated relation of a operation which requires a view.
     * This function assume the operation does requires a view.
     */
    const std::string& getViewRelation(const ram::Node* node);

    /**
     * @brief Encode and return the super-instruction information about a index operation.
     */
    SuperInstruction getIndexSuperInstInfo(const ram::IndexOperation& ramIndex);

    /**
     * @brief Encode and return the super-instruction information about an existence check operation
     */
    SuperInstruction getExistenceSuperInstInfo(const ram::AbstractExistenceCheck& abstractExist);

    /**
     * @brief Encode and return the super-instruction information about a project operation
     *
     * No reordering needed for projection as project can have more then one target indexes and reordering can
     * only be done during runtime.
     */
    SuperInstruction getProjectSuperInstInfo(const ram::Project& exist);

    /** Environment encoding, store a mapping from ram::Node to its operation index id. */
    std::unordered_map<const ram::Node*, size_t> indexTable;
    /** Points to the current viewContext during the generation.
     * It is used to passing viewContext between parent query and its nested parallel operation.
     * As parallel operation requires its own view information. */
    std::shared_ptr<ViewContext> parentQueryViewContext = nullptr;
    /** Next available location to encode View */
    size_t viewId = 0;
    /** Next available location to encode a relation */
    size_t relId = 0;
    /** Environment encoding, store a mapping from ram::Node to its View id. */
    std::unordered_map<const ram::Node*, size_t> viewTable;
    /** Environment encoding, store a mapping from ram::Relation to its id */
    std::unordered_map<std::string, size_t> relTable;
    /** name / relation mapping */
    std::unordered_map<std::string, const ram::Relation*> relationMap;
    /** ordering context */
    OrderingContext orderingContext = OrderingContext(*this);
    /** Reference to the engine instance */
    Engine& engine;
};
}  // namespace souffle::interpreter
