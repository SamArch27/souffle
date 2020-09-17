/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Visitor.h
 *
 * Provides some infrastructure for the implementation of operations
 * on top of RAM structures.
 *
 ***********************************************************************/

#pragma once

#include "ram/AbstractConditional.h"
#include "ram/AbstractExistenceCheck.h"
#include "ram/AbstractOperator.h"
#include "ram/Aggregate.h"
#include "ram/AutoIncrement.h"
#include "ram/BinRelationStatement.h"
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
#include "ram/FloatConstant.h"
#include "ram/IO.h"
#include "ram/IndexAggregate.h"
#include "ram/IndexChoice.h"
#include "ram/IndexOperation.h"
#include "ram/IndexScan.h"
#include "ram/IntrinsicOperator.h"
#include "ram/ListStatement.h"
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
#include "ram/RelationOperation.h"
#include "ram/RelationSize.h"
#include "ram/RelationStatement.h"
#include "ram/Scan.h"
#include "ram/Sequence.h"
#include "ram/SignedConstant.h"
#include "ram/Statement.h"
#include "ram/SubroutineArgument.h"
#include "ram/SubroutineReturn.h"
#include "ram/Swap.h"
#include "ram/True.h"
#include "ram/TupleElement.h"
#include "ram/TupleOperation.h"
#include "ram/UndefValue.h"
#include "ram/UnpackRecord.h"
#include "ram/UnsignedConstant.h"
#include "ram/UserDefinedOperator.h"
#include "souffle/utility/FunctionalUtil.h"
#include "souffle/utility/MiscUtil.h"
#include <cstddef>
#include <functional>
#include <type_traits>
#include <typeinfo>
#include <vector>

namespace souffle::ram {

/** A tag type required for the is_ram_visitor type trait to identify RamVisitors */
struct ram_visitor_tag {};

/**
 * The generic base type of all RamVisitors realizing the dispatching of
 * visitor calls. Each visitor may define a return type R and a list of
 * extra parameters to be passed along with the visited Nodes to the
 * corresponding visitor function.
 *
 * @tparam R the result type produced by a visit call
 * @tparam Params extra parameters to be passed to the visit call
 */
template <typename R = void, typename... Params>
struct Visitor : public ram_visitor_tag {
    /** A virtual destructor */
    virtual ~Visitor() = default;

    /** The main entry for the user allowing visitors to be utilized as functions */
    R operator()(const Node& node, Params... args) {
        return visit(node, args...);
    }

    /** The main entry for the user allowing visitors to be utilized as functions */
    R operator()(const Node* node, Params... args) {
        return visit(*node, args...);
    }

    /**
     * The main entry for a visit process conducting the dispatching of
     * a visit to the various sub-types of Nodes. Sub-classes may override
     * this implementation to conduct pre-visit operations.
     *
     * Note that the order of this list is important. Sub-classes must be listed
     * before their super-classes; otherwise sub-classes cannot be visited.
     *
     * @param node the node to be visited
     * @param args a list of extra parameters to be forwarded
     */
    virtual R visit(const Node& node, Params... args) {
        // dispatch node processing based on dynamic type

#define FORWARD(Kind) \
    if (const auto* n = dynamic_cast<const Kind*>(&node)) return visit##Kind(*n, args...);

        // Relation
        FORWARD(Relation);
        FORWARD(RelationReference);

        // Expressions
        FORWARD(TupleElement);
        FORWARD(SignedConstant);
        FORWARD(UnsignedConstant);
        FORWARD(FloatConstant);
        FORWARD(Constant);
        FORWARD(IntrinsicOperator);
        FORWARD(UserDefinedOperator);
        FORWARD(AutoIncrement);
        FORWARD(PackRecord);
        FORWARD(SubroutineArgument);
        FORWARD(UndefValue);
        FORWARD(RelationSize);

        // Conditions
        FORWARD(True);
        FORWARD(False);
        FORWARD(EmptinessCheck);
        FORWARD(ProvenanceExistenceCheck);
        FORWARD(ExistenceCheck);
        FORWARD(Conjunction);
        FORWARD(Negation);
        FORWARD(Constraint);

        // Operations
        FORWARD(Filter);
        FORWARD(Break);
        FORWARD(Project);
        FORWARD(SubroutineReturn);
        FORWARD(UnpackRecord);
        FORWARD(NestedIntrinsicOperator);
        FORWARD(ParallelScan);
        FORWARD(Scan);
        FORWARD(ParallelIndexScan);
        FORWARD(IndexScan);
        FORWARD(ParallelChoice);
        FORWARD(Choice);
        FORWARD(ParallelIndexChoice);
        FORWARD(IndexChoice);
        FORWARD(ParallelAggregate);
        FORWARD(Aggregate);
        FORWARD(ParallelIndexAggregate);
        FORWARD(IndexAggregate);

        // Statements
        FORWARD(IO);
        FORWARD(Query);
        FORWARD(Clear);
        FORWARD(LogSize);

        FORWARD(Swap);
        FORWARD(Extend);

        // Control-flow
        FORWARD(Program);
        FORWARD(Sequence);
        FORWARD(Loop);
        FORWARD(Parallel);
        FORWARD(Exit);
        FORWARD(LogTimer);
        FORWARD(LogRelationTimer);
        FORWARD(DebugInfo);
        FORWARD(Call);

#undef FORWARD

        // did not work ...
        fatal("unsupported type: %s", typeid(node).name());
    }

    virtual R visit(const Node* node, Params... args) {
        return visit(*node, args...);
    }

protected:
#define LINK(Node, Parent)                                 \
    virtual R visit##Node(const Node& n, Params... args) { \
        return visit##Parent(n, args...);                  \
    }

    // -- statements --
    LINK(IO, RelationStatement);
    LINK(Query, Statement);
    LINK(Clear, RelationStatement);
    LINK(LogSize, RelationStatement);

    LINK(RelationStatement, Statement);

    LINK(Swap, BinRelationStatement);
    LINK(Extend, BinRelationStatement);
    LINK(BinRelationStatement, Statement);

    LINK(Sequence, ListStatement);
    LINK(Loop, Statement);
    LINK(Parallel, ListStatement);
    LINK(ListStatement, Statement);
    LINK(Exit, Statement);
    LINK(LogTimer, Statement);
    LINK(LogRelationTimer, Statement);
    LINK(DebugInfo, Statement);
    LINK(Call, Statement);

    LINK(Statement, Node);

    // -- operations --
    LINK(Project, Operation);
    LINK(SubroutineReturn, Operation);
    LINK(UnpackRecord, TupleOperation);
    LINK(NestedIntrinsicOperator, TupleOperation)
    LINK(Scan, RelationOperation);
    LINK(ParallelScan, Scan);
    LINK(IndexScan, IndexOperation);
    LINK(ParallelIndexScan, IndexScan);
    LINK(Choice, RelationOperation);
    LINK(ParallelChoice, Choice);
    LINK(IndexChoice, IndexOperation);
    LINK(ParallelIndexChoice, IndexChoice);
    LINK(RelationOperation, TupleOperation);
    LINK(Aggregate, RelationOperation);
    LINK(ParallelAggregate, Aggregate);
    LINK(IndexAggregate, IndexOperation);
    LINK(ParallelIndexAggregate, IndexAggregate);
    LINK(IndexOperation, RelationOperation);
    LINK(TupleOperation, NestedOperation);
    LINK(Filter, AbstractConditional);
    LINK(Break, AbstractConditional);
    LINK(AbstractConditional, NestedOperation);
    LINK(NestedOperation, Operation);

    LINK(Operation, Node);

    // -- conditions --
    LINK(True, Condition);
    LINK(False, Condition);
    LINK(Conjunction, Condition);
    LINK(Negation, Condition);
    LINK(Constraint, Condition);
    LINK(ProvenanceExistenceCheck, AbstractExistenceCheck);
    LINK(ExistenceCheck, AbstractExistenceCheck);
    LINK(EmptinessCheck, Condition);
    LINK(AbstractExistenceCheck, Condition);

    LINK(Condition, Node);

    // -- values --
    LINK(SignedConstant, Constant);
    LINK(UnsignedConstant, Constant);
    LINK(FloatConstant, Constant);
    LINK(Constant, Expression);
    LINK(UndefValue, Expression);
    LINK(TupleElement, Expression);
    LINK(IntrinsicOperator, AbstractOperator);
    LINK(UserDefinedOperator, AbstractOperator);
    LINK(AbstractOperator, Expression);
    LINK(AutoIncrement, Expression);
    LINK(PackRecord, Expression);
    LINK(SubroutineArgument, Expression);
    LINK(RelationSize, Expression);

    LINK(Expression, Node);

    // -- program --
    LINK(Program, Node);

    // -- relation
    LINK(Relation, Node);
    LINK(RelationReference, Node);

#undef LINK

    /** The base case for all visitors -- if no more specific overload was defined */
    virtual R visitNode(const Node& /*node*/, Params... /*args*/) {
        return R();
    }
};

/**
 * A utility function visiting all nodes within the RAM fragment rooted by the given node
 * recursively in a depth-first pre-order fashion applying the given visitor to each
 * encountered node.
 *
 * @param root the root of the RAM fragment to be visited
 * @param visitor the visitor to be applied on each node
 * @param args a list of extra parameters to be forwarded to the visitor
 */
template <typename R, typename... Ps, typename... Args>
void visitDepthFirstPreOrder(const Node& root, Visitor<R, Ps...>& visitor, Args&... args) {
    visitor(root, args...);
    for (const Node* cur : root.getChildNodes()) {
        if (cur != nullptr) {
            visitDepthFirstPreOrder(*cur, visitor, args...);
        }
    }
}

/**
 * A utility function visiting all nodes within the RAM fragments rooted by the given node
 * recursively in a depth-first pre-order fashion applying the given visitor to each
 * encountered node.
 *
 * @param root the root of the RAM fragments to be visited
 * @param visitor the visitor to be applied on each node
 * @param args a list of extra parameters to be forwarded to the visitor
 */
template <typename R, typename... Ps, typename... Args>
void visitDepthFirst(const Node& root, Visitor<R, Ps...>& visitor, Args&... args) {
    visitDepthFirstPreOrder(root, visitor, args...);
}

namespace detail {

/**
 * A specialized visitor wrapping a lambda function -- an auxiliary type required
 * for visitor convenience functions.
 */
template <typename R, typename N>
struct LambdaVisitor : public Visitor<void> {
    std::function<R(const N&)> lambda;
    LambdaVisitor(std::function<R(const N&)> lambda) : lambda(std::move(lambda)) {}
    void visit(const Node& node) override {
        if (const auto* n = dynamic_cast<const N*>(&node)) {
            lambda(*n);
        }
    }
};

/**
 * A factory function for creating LambdaVisitor instances.
 */
template <typename R, typename N>
LambdaVisitor<R, N> makeLambdaVisitor(const std::function<R(const N&)>& fun) {
    return LambdaVisitor<R, N>(fun);
}

/**
 * A type trait determining whether a given type is a visitor or not.
 */
template <typename T>
struct is_ram_visitor {
    static constexpr size_t value = std::is_base_of<ram_visitor_tag, T>::value;
};

template <typename T>
struct is_ram_visitor<const T> : public is_ram_visitor<T> {};

template <typename T>
struct is_ram_visitor<T&> : public is_ram_visitor<T> {};
}  // namespace detail

/**
 * A utility function visiting all nodes within the RAM fragment rooted by the given node
 * recursively in a depth-first pre-order fashion applying the given function to each
 * encountered node.
 *
 * @param root the root of the RAM fragment to be visited
 * @param fun the function to be applied
 * @param args a list of extra parameters to be forwarded to the visitor
 */
template <typename R, typename N>
void visitDepthFirst(const Node& root, const std::function<R(const N&)>& fun) {
    auto visitor = detail::makeLambdaVisitor(fun);
    visitDepthFirst<void>(root, visitor);
}

/**
 * A utility function visiting all nodes within the RAM fragment rooted by the given node
 * recursively in a depth-first pre-order fashion applying the given function to each
 * encountered node.
 *
 * @param root the root of the RAM fragment to be visited
 * @param fun the function to be applied
 * @param args a list of extra parameters to be forwarded to the visitor
 */
template <typename Lambda, typename R = typename lambda_traits<Lambda>::result_type,
        typename N = typename lambda_traits<Lambda>::arg0_type>
typename std::enable_if<!detail::is_ram_visitor<Lambda>::value, void>::type visitDepthFirst(
        const Node& root, const Lambda& fun) {
    visitDepthFirst(root, std::function<R(const N&)>(fun));
}

}  // namespace souffle::ram
