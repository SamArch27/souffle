/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2020, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ram_operation_equal_clone_test.cpp
 *
 * Tests equal and clone function of Condition classes.
 *
 ***********************************************************************/

#include "tests/test.h"

#include "AggregateOp.h"
#include "RelationTag.h"
#include "ram/Aggregate.h"
#include "ram/Break.h"
#include "ram/Choice.h"
#include "ram/Condition.h"
#include "ram/Conjunction.h"
#include "ram/Constraint.h"
#include "ram/EmptinessCheck.h"
#include "ram/ExistenceCheck.h"
#include "ram/Expression.h"
#include "ram/Filter.h"
#include "ram/IndexAggregate.h"
#include "ram/IndexChoice.h"
#include "ram/IndexScan.h"
#include "ram/Negation.h"
#include "ram/Operation.h"
#include "ram/PackRecord.h"
#include "ram/ParallelChoice.h"
#include "ram/ParallelIndexChoice.h"
#include "ram/ParallelIndexScan.h"
#include "ram/ParallelScan.h"
#include "ram/Project.h"
#include "ram/Relation.h"
#include "ram/Scan.h"
#include "ram/SignedConstant.h"
#include "ram/SubroutineReturn.h"
#include "ram/True.h"
#include "ram/TupleElement.h"
#include "ram/UndefValue.h"
#include "ram/UnpackRecord.h"
#include "souffle/BinaryConstraintOps.h"
#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace souffle::ram::test {

TEST(RamScan, CloneAndEquals) {
    Relation A("A", 1, 1, {"x"}, {"i"}, RelationRepresentation::DEFAULT);
    // FOR t0 in A
    //  RETURN number(0)
    VecOwn<Expression> a_return_args;
    a_return_args.emplace_back(new SignedConstant(0));
    auto a_return = mk<SubroutineReturn>(std::move(a_return_args));
    Scan a("A", 0, std::move(a_return), "Scan test");

    VecOwn<Expression> b_return_args;
    b_return_args.emplace_back(new SignedConstant(0));
    auto b_return = mk<SubroutineReturn>(std::move(b_return_args));
    Scan b("A", 0, std::move(b_return), "Scan test");

    EXPECT_EQ(a, b);
    EXPECT_NE(&a, &b);

    Scan* c = a.clone();
    EXPECT_EQ(a, *c);
    EXPECT_NE(&a, c);
    delete c;
}

TEST(RamParallelScan, CloneAndEquals) {
    Relation A("A", 1, 1, {"x"}, {"i"}, RelationRepresentation::DEFAULT);
    // PARALLEL FOR t0 in A
    //  RETURN number(0)
    VecOwn<Expression> a_return_args;
    a_return_args.emplace_back(new SignedConstant(0));
    auto a_return = mk<SubroutineReturn>(std::move(a_return_args));
    ParallelScan a("A", 0, std::move(a_return), "ParallelScan test");

    VecOwn<Expression> b_return_args;
    b_return_args.emplace_back(new SignedConstant(0));
    auto b_return = mk<SubroutineReturn>(std::move(b_return_args));
    ParallelScan b("A", 0, std::move(b_return), "ParallelScan test");

    EXPECT_EQ(a, b);
    EXPECT_NE(&a, &b);

    ParallelScan* c = a.clone();
    EXPECT_EQ(a, *c);
    EXPECT_NE(&a, c);
    delete c;
}

TEST(RamIndexScan, CloneAndEquals) {
    Relation edge("edge", 2, 1, {"x", "y"}, {"i", "i"}, RelationRepresentation::DEFAULT);
    Relation vertex("vertex", 1, 1, {"x"}, {"i"}, RelationRepresentation::DEFAULT);
    // get vertices contain self loop
    // FOR t1 IN edge ON INDEX t1.x = t1.1 AND t1.y = ⊥
    //  PROJECT (t1.0) INTO vertex
    VecOwn<Expression> a_project_args;
    a_project_args.emplace_back(new TupleElement(1, 0));
    auto a_project = mk<Project>("vertex", std::move(a_project_args));
    RamPattern a_criteria;
    a_criteria.first.emplace_back(new TupleElement(1, 1));
    a_criteria.first.emplace_back(new UndefValue);
    a_criteria.second.emplace_back(new TupleElement(1, 1));
    a_criteria.second.emplace_back(new UndefValue);

    IndexScan a("edge", 1, std::move(a_criteria), std::move(a_project), "IndexScan test");

    VecOwn<Expression> b_project_args;
    b_project_args.emplace_back(new TupleElement(1, 0));
    auto b_project = mk<Project>("vertex", std::move(b_project_args));
    RamPattern b_criteria;
    b_criteria.first.emplace_back(new TupleElement(1, 1));
    b_criteria.first.emplace_back(new UndefValue);
    b_criteria.second.emplace_back(new TupleElement(1, 1));
    b_criteria.second.emplace_back(new UndefValue);

    IndexScan b("edge", 1, std::move(b_criteria), std::move(b_project), "IndexScan test");
    EXPECT_EQ(a, b);
    EXPECT_NE(&a, &b);

    IndexScan* c = a.clone();
    EXPECT_EQ(a, *c);
    EXPECT_NE(&a, c);
    delete c;
}

TEST(RamParallelIndexScan, CloneAndEquals) {
    Relation edge("edge", 2, 1, {"x", "y"}, {"i", "i"}, RelationRepresentation::DEFAULT);
    Relation new_edge("new_edge", 2, 1, {"x", "y"}, {"i", "i"}, RelationRepresentation::DEFAULT);
    // get edges direct to vertex 5
    // PARALLEL FOR t1 IN edge ON INDEX t1.x = ⊥ AND t1.y = 5
    //  PROJECT (t1.0, t1.1) INTO new_edge
    VecOwn<Expression> a_project_args;
    a_project_args.emplace_back(new TupleElement(1, 0));
    a_project_args.emplace_back(new TupleElement(1, 1));
    auto a_project = mk<Project>("new_edge", std::move(a_project_args));
    RamPattern a_criteria;
    a_criteria.first.emplace_back(new UndefValue);
    a_criteria.first.emplace_back(new SignedConstant(5));
    a_criteria.second.emplace_back(new UndefValue);
    a_criteria.second.emplace_back(new SignedConstant(5));

    ParallelIndexScan a("edge", 1, std::move(a_criteria), std::move(a_project), "ParallelIndexScan test");

    VecOwn<Expression> b_project_args;
    b_project_args.emplace_back(new TupleElement(1, 0));
    b_project_args.emplace_back(new TupleElement(1, 1));
    auto b_project = mk<Project>("new_edge", std::move(b_project_args));
    RamPattern b_criteria;
    b_criteria.first.emplace_back(new UndefValue);
    b_criteria.first.emplace_back(new SignedConstant(5));
    b_criteria.second.emplace_back(new UndefValue);
    b_criteria.second.emplace_back(new SignedConstant(5));

    ParallelIndexScan b("edge", 1, std::move(b_criteria), std::move(b_project), "ParallelIndexScan test");
    EXPECT_EQ(a, b);
    EXPECT_NE(&a, &b);

    ParallelIndexScan* c = a.clone();
    EXPECT_EQ(a, *c);
    EXPECT_NE(&a, c);
    delete c;
}

TEST(RamChoice, CloneAndEquals) {
    Relation edge("edge", 2, 1, {"x", "y"}, {"i", "i"}, RelationRepresentation::DEFAULT);
    // choose an edge not adjcent to vertex 5
    // CHOICE t1 IN edge WHERE NOT t1.0 = 5 AND NOT t1.1 = 5
    //  RETURN (t1.0, t1.1)
    VecOwn<Expression> a_return_args;
    a_return_args.emplace_back(new TupleElement(1, 0));
    a_return_args.emplace_back(new TupleElement(1, 1));
    auto a_return = mk<SubroutineReturn>(std::move(a_return_args));
    auto a_constraint1 =
            mk<Constraint>(BinaryConstraintOp::EQ, mk<TupleElement>(1, 0), mk<SignedConstant>(5));
    auto a_neg1 = mk<Negation>(std::move(a_constraint1));
    auto a_constraint2 =
            mk<Constraint>(BinaryConstraintOp::EQ, mk<TupleElement>(1, 1), mk<SignedConstant>(5));
    auto a_neg2 = mk<Negation>(std::move(a_constraint2));
    auto a_cond = mk<Conjunction>(std::move(a_neg1), std::move(a_neg2));
    Choice a("edge", 1, std::move(a_cond), std::move(a_return), "Choice test");

    VecOwn<Expression> b_return_args;
    b_return_args.emplace_back(new TupleElement(1, 0));
    b_return_args.emplace_back(new TupleElement(1, 1));
    auto b_return = mk<SubroutineReturn>(std::move(b_return_args));
    auto b_constraint1 =
            mk<Constraint>(BinaryConstraintOp::EQ, mk<TupleElement>(1, 0), mk<SignedConstant>(5));
    auto b_neg1 = mk<Negation>(std::move(b_constraint1));
    auto b_constraint2 =
            mk<Constraint>(BinaryConstraintOp::EQ, mk<TupleElement>(1, 1), mk<SignedConstant>(5));
    auto b_neg2 = mk<Negation>(std::move(b_constraint2));
    auto b_cond = mk<Conjunction>(std::move(b_neg1), std::move(b_neg2));
    Choice b("edge", 1, std::move(b_cond), std::move(b_return), "Choice test");

    EXPECT_EQ(a, b);
    EXPECT_NE(&a, &b);

    Choice* c = a.clone();
    EXPECT_EQ(a, *c);
    EXPECT_NE(&a, c);
    delete c;
}

TEST(RamParallelChoice, CloneAndEquals) {
    Relation edge("edge", 2, 1, {"x", "y"}, {"i", "i"}, RelationRepresentation::DEFAULT);
    // parallel choose an edge not adjcent to vertex 5
    // PARALLEL CHOICE t1 IN edge WHERE NOT t1.0 = 5 AND NOT t1.1 = 5
    //  RETURN (t1.0, t1.1)
    VecOwn<Expression> a_return_args;
    a_return_args.emplace_back(new TupleElement(1, 0));
    a_return_args.emplace_back(new TupleElement(1, 1));
    auto a_return = mk<SubroutineReturn>(std::move(a_return_args));
    auto a_constraint1 =
            mk<Constraint>(BinaryConstraintOp::EQ, mk<TupleElement>(1, 0), mk<SignedConstant>(5));
    auto a_neg1 = mk<Negation>(std::move(a_constraint1));
    auto a_constraint2 =
            mk<Constraint>(BinaryConstraintOp::EQ, mk<TupleElement>(1, 1), mk<SignedConstant>(5));
    auto a_neg2 = mk<Negation>(std::move(a_constraint2));
    auto a_cond = mk<Conjunction>(std::move(a_neg1), std::move(a_neg2));
    ParallelChoice a("edge", 1, std::move(a_cond), std::move(a_return), "ParallelChoice test");

    VecOwn<Expression> b_return_args;
    b_return_args.emplace_back(new TupleElement(1, 0));
    b_return_args.emplace_back(new TupleElement(1, 1));
    auto b_return = mk<SubroutineReturn>(std::move(b_return_args));
    auto b_constraint1 =
            mk<Constraint>(BinaryConstraintOp::EQ, mk<TupleElement>(1, 0), mk<SignedConstant>(5));
    auto b_neg1 = mk<Negation>(std::move(b_constraint1));
    auto b_constraint2 =
            mk<Constraint>(BinaryConstraintOp::EQ, mk<TupleElement>(1, 1), mk<SignedConstant>(5));
    auto b_neg2 = mk<Negation>(std::move(b_constraint2));
    auto b_cond = mk<Conjunction>(std::move(b_neg1), std::move(b_neg2));
    ParallelChoice b("edge", 1, std::move(b_cond), std::move(b_return), "ParallelChoice test");

    EXPECT_EQ(a, b);
    EXPECT_NE(&a, &b);

    ParallelChoice* c = a.clone();
    EXPECT_EQ(a, *c);
    EXPECT_NE(&a, c);
    delete c;
}

TEST(RamIndexChoice, CloneAndEquals) {
    Relation edge("edge", 2, 1, {"x", "y"}, {"i", "i"}, RelationRepresentation::DEFAULT);
    // FOR t1 IN edge ON INDEX t1.x = 5 AND t1.y = ⊥
    // WHERE NOT t1.1 = 5
    //  RETURN (t1.0, t1.1)
    VecOwn<Expression> a_return_args;
    a_return_args.emplace_back(new TupleElement(1, 0));
    a_return_args.emplace_back(new TupleElement(1, 1));
    auto a_return = mk<SubroutineReturn>(std::move(a_return_args));
    auto a_constraint = mk<Constraint>(BinaryConstraintOp::EQ, mk<TupleElement>(1, 1), mk<SignedConstant>(5));
    auto a_neg = mk<Negation>(std::move(a_constraint));
    RamPattern a_criteria;
    a_criteria.first.emplace_back(new SignedConstant(5));
    a_criteria.first.emplace_back(new UndefValue);
    a_criteria.second.emplace_back(new SignedConstant(5));
    a_criteria.second.emplace_back(new UndefValue);
    IndexChoice a(
            "edge", 1, std::move(a_neg), std::move(a_criteria), std::move(a_return), "IndexChoice test");

    VecOwn<Expression> b_return_args;
    b_return_args.emplace_back(new TupleElement(1, 0));
    b_return_args.emplace_back(new TupleElement(1, 1));
    auto b_return = mk<SubroutineReturn>(std::move(b_return_args));
    auto b_constraint = mk<Constraint>(BinaryConstraintOp::EQ, mk<TupleElement>(1, 1), mk<SignedConstant>(5));
    auto b_neg = mk<Negation>(std::move(b_constraint));
    RamPattern b_criteria;
    b_criteria.first.emplace_back(new SignedConstant(5));
    b_criteria.first.emplace_back(new UndefValue);
    b_criteria.second.emplace_back(new SignedConstant(5));
    b_criteria.second.emplace_back(new UndefValue);
    IndexChoice b(
            "edge", 1, std::move(b_neg), std::move(b_criteria), std::move(b_return), "IndexChoice test");
    EXPECT_EQ(a, b);
    EXPECT_NE(&a, &b);

    IndexChoice* c = a.clone();
    EXPECT_EQ(a, *c);
    EXPECT_NE(&a, c);
    delete c;
}

TEST(RamiParallelIndexChoice, CloneAndEquals) {
    Relation edge("edge", 2, 1, {"x", "y"}, {"i", "i"}, RelationRepresentation::DEFAULT);
    // PARALLEL FOR t1 IN edge ON INDEX t1.x = 5 AND t1.y = ⊥
    // WHERE NOT t1.1 = 5
    //  RETURN (t1.0, t1.1)
    VecOwn<Expression> a_return_args;
    a_return_args.emplace_back(new TupleElement(1, 0));
    a_return_args.emplace_back(new TupleElement(1, 1));
    auto a_return = mk<SubroutineReturn>(std::move(a_return_args));
    auto a_constraint = mk<Constraint>(BinaryConstraintOp::EQ, mk<TupleElement>(1, 1), mk<SignedConstant>(5));
    auto a_neg = mk<Negation>(std::move(a_constraint));
    RamPattern a_criteria;
    a_criteria.first.emplace_back(new SignedConstant(5));
    a_criteria.first.emplace_back(new UndefValue);
    a_criteria.second.emplace_back(new SignedConstant(5));
    a_criteria.second.emplace_back(new UndefValue);
    ParallelIndexChoice a(
            "edge", 1, std::move(a_neg), std::move(a_criteria), std::move(a_return), "IndexChoice test");

    VecOwn<Expression> b_return_args;
    b_return_args.emplace_back(new TupleElement(1, 0));
    b_return_args.emplace_back(new TupleElement(1, 1));
    auto b_return = mk<SubroutineReturn>(std::move(b_return_args));
    auto b_constraint = mk<Constraint>(BinaryConstraintOp::EQ, mk<TupleElement>(1, 1), mk<SignedConstant>(5));
    auto b_neg = mk<Negation>(std::move(b_constraint));
    RamPattern b_criteria;
    b_criteria.first.emplace_back(new SignedConstant(5));
    b_criteria.first.emplace_back(new UndefValue);
    b_criteria.second.emplace_back(new SignedConstant(5));
    b_criteria.second.emplace_back(new UndefValue);
    ParallelIndexChoice b(
            "edge", 1, std::move(b_neg), std::move(b_criteria), std::move(b_return), "IndexChoice test");
    EXPECT_EQ(a, b);
    EXPECT_NE(&a, &b);

    ParallelIndexChoice* c = a.clone();
    EXPECT_EQ(a, *c);
    EXPECT_NE(&a, c);
    delete c;
}

TEST(RamAggregate, CloneAndEquals) {
    Relation edge("edge", 2, 1, {"x", "y"}, {"i", "i"}, RelationRepresentation::DEFAULT);
    // t0.0 = COUNT FOR ALL t1 IN edge
    //  RETURN t0.0
    VecOwn<Expression> a_return_args;
    a_return_args.emplace_back(new TupleElement(0, 0));
    auto a_return = mk<SubroutineReturn>(std::move(a_return_args));
    Aggregate a(std::move(a_return), AggregateOp::COUNT, "edge", mk<TupleElement>(0, 0), mk<True>(), 1);

    VecOwn<Expression> b_return_args;
    b_return_args.emplace_back(new TupleElement(0, 0));
    auto b_return = mk<SubroutineReturn>(std::move(b_return_args));
    Aggregate b(std::move(b_return), AggregateOp::COUNT, "edge", mk<TupleElement>(0, 0), mk<True>(), 1);
    EXPECT_EQ(a, b);
    EXPECT_NE(&a, &b);

    Aggregate* c = a.clone();
    EXPECT_EQ(a, *c);
    EXPECT_NE(&a, c);
    delete c;
}

TEST(RamIndexAggregate, CloneAndEquals) {
    Relation sqrt("sqrt", 2, 1, {"nth", "value"}, {"i", "i"}, RelationRepresentation::DEFAULT);
    // t0.0 = MIN t1.1 SEARCH t1 IN sqrt ON INDEX t1.0 = ⊥ AND t1.1 = ⊥
    // WHERE t1.1 > 80
    //  RETURN t0.0
    VecOwn<Expression> a_return_args;
    a_return_args.emplace_back(new TupleElement(0, 0));
    auto a_return = mk<SubroutineReturn>(std::move(a_return_args));
    auto a_cond = mk<Constraint>(BinaryConstraintOp::GE, mk<TupleElement>(1, 1), mk<SignedConstant>(80));
    RamPattern a_criteria;
    a_criteria.first.emplace_back(new UndefValue);
    a_criteria.first.emplace_back(new UndefValue);
    a_criteria.second.emplace_back(new UndefValue);
    a_criteria.second.emplace_back(new UndefValue);
    IndexAggregate a(std::move(a_return), AggregateOp::MIN, "sqrt", mk<TupleElement>(1, 1), std::move(a_cond),
            std::move(a_criteria), 1);

    VecOwn<Expression> b_return_args;
    b_return_args.emplace_back(new TupleElement(0, 0));
    auto b_return = mk<SubroutineReturn>(std::move(b_return_args));
    auto b_cond = mk<Constraint>(BinaryConstraintOp::GE, mk<TupleElement>(1, 1), mk<SignedConstant>(80));
    RamPattern b_criteria;
    b_criteria.first.emplace_back(new UndefValue);
    b_criteria.first.emplace_back(new UndefValue);
    b_criteria.second.emplace_back(new UndefValue);
    b_criteria.second.emplace_back(new UndefValue);
    IndexAggregate b(std::move(b_return), AggregateOp::MIN, "sqrt", mk<TupleElement>(1, 1), std::move(b_cond),
            std::move(b_criteria), 1);
    EXPECT_EQ(a, b);
    EXPECT_NE(&a, &b);

    IndexAggregate* c = a.clone();
    EXPECT_EQ(a, *c);
    EXPECT_NE(&a, c);
    delete c;
}

TEST(RamUnpackedRecord, CloneAndEquals) {
    // UNPACK (t0.0, t0.2) INTO t1
    // RETURN number(0)
    VecOwn<Expression> a_return_args;
    a_return_args.emplace_back(new SignedConstant(0));
    auto a_return = mk<SubroutineReturn>(std::move(a_return_args));
    VecOwn<Expression> a_record_args;
    a_record_args.emplace_back(new TupleElement(0, 0));
    a_record_args.emplace_back(new TupleElement(0, 2));
    auto a_record = mk<PackRecord>(std::move(a_record_args));
    UnpackRecord a(std::move(a_return), 1, std::move(a_record), 2);

    VecOwn<Expression> b_return_args;
    b_return_args.emplace_back(new SignedConstant(0));
    auto b_return = mk<SubroutineReturn>(std::move(b_return_args));
    VecOwn<Expression> b_record_args;
    b_record_args.emplace_back(new TupleElement(0, 0));
    b_record_args.emplace_back(new TupleElement(0, 2));
    auto b_record = mk<PackRecord>(std::move(b_record_args));
    UnpackRecord b(std::move(b_return), 1, std::move(b_record), 2);
    EXPECT_EQ(a, b);
    EXPECT_NE(&a, &b);

    UnpackRecord* c = a.clone();
    EXPECT_EQ(a, *c);
    EXPECT_NE(&a, c);
    delete c;
}

TEST(RamFilter, CloneAndEquals) {
    Relation A("A", 1, 1, {"a"}, {"i"}, RelationRepresentation::DEFAULT);
    // IF (NOT t0.1 in A)
    // RETURN number(0)
    VecOwn<Expression> a_return_args;
    a_return_args.emplace_back(new SignedConstant(0));
    auto a_return = mk<SubroutineReturn>(std::move(a_return_args));
    VecOwn<Expression> a_existence_check_args;
    a_existence_check_args.emplace_back(new TupleElement(0, 1));
    auto a_existence_check = mk<ExistenceCheck>("A", std::move(a_existence_check_args));
    Filter a(mk<Negation>(std::move(a_existence_check)), std::move(a_return), "Filter test");

    VecOwn<Expression> b_return_args;
    b_return_args.emplace_back(new SignedConstant(0));
    auto b_return = mk<SubroutineReturn>(std::move(b_return_args));
    VecOwn<Expression> b_existence_check_args;
    b_existence_check_args.emplace_back(new TupleElement(0, 1));
    auto b_existence_check = mk<ExistenceCheck>("A", std::move(b_existence_check_args));
    Filter b(mk<Negation>(std::move(b_existence_check)), std::move(b_return), "Filter test");
    EXPECT_EQ(a, b);
    EXPECT_NE(&a, &b);

    Filter* c = a.clone();
    EXPECT_EQ(a, *c);
    EXPECT_NE(&a, c);
    delete c;
}

TEST(RamBreak, CloneAndEquals) {
    Relation A("A", 1, 1, {"a"}, {"i"}, RelationRepresentation::DEFAULT);
    // IF (A = ∅) BREAK
    // RETURN number(0)
    VecOwn<Expression> a_return_args;
    a_return_args.emplace_back(new SignedConstant(0));
    auto a_return = mk<SubroutineReturn>(std::move(a_return_args));
    Break a(mk<EmptinessCheck>("A"), std::move(a_return), "Break test");

    VecOwn<Expression> b_return_args;
    b_return_args.emplace_back(new SignedConstant(0));
    auto b_return = mk<SubroutineReturn>(std::move(b_return_args));
    Break b(mk<EmptinessCheck>("A"), std::move(b_return), "Break test");
    EXPECT_EQ(a, b);
    EXPECT_NE(&a, &b);

    Break* c = a.clone();
    EXPECT_EQ(a, *c);
    EXPECT_NE(&a, c);
    delete c;
}

TEST(RamProject, CloneAndEquals) {
    Relation A("A", 2, 1, {"a", "b"}, {"i", "i"}, RelationRepresentation::DEFAULT);
    // PROJECT (t0.1, t0.3) INTO A
    VecOwn<Expression> a_args;
    a_args.emplace_back(new TupleElement(0, 1));
    a_args.emplace_back(new TupleElement(0, 3));
    Project a("A", std::move(a_args));

    VecOwn<Expression> b_args;
    b_args.emplace_back(new TupleElement(0, 1));
    b_args.emplace_back(new TupleElement(0, 3));
    Project b("A", std::move(b_args));
    EXPECT_EQ(a, b);
    EXPECT_NE(&a, &b);

    Project* c = a.clone();
    EXPECT_EQ(a, *c);
    EXPECT_NE(&a, c);
    delete c;
}

TEST(RamSubroutineReturn, CloneAndEquals) {
    // RETURN (t0.1, t0.2)
    VecOwn<Expression> a_args;
    a_args.emplace_back(new TupleElement(0, 1));
    a_args.emplace_back(new TupleElement(0, 2));
    SubroutineReturn a(std::move(a_args));

    VecOwn<Expression> b_args;
    b_args.emplace_back(new TupleElement(0, 1));
    b_args.emplace_back(new TupleElement(0, 2));
    SubroutineReturn b(std::move(b_args));
    EXPECT_EQ(a, b);
    EXPECT_NE(&a, &b);

    SubroutineReturn* c = a.clone();
    EXPECT_EQ(a, *c);
    EXPECT_NE(&a, c);
    delete c;

    // RETURN (number(0))
    VecOwn<Expression> d_args;
    d_args.emplace_back(new SignedConstant(0));
    SubroutineReturn d(std::move(d_args));

    VecOwn<Expression> e_args;
    e_args.emplace_back(new SignedConstant(0));
    SubroutineReturn e(std::move(e_args));
    EXPECT_EQ(d, e);
    EXPECT_NE(&d, &e);

    SubroutineReturn* f = d.clone();
    EXPECT_EQ(d, *f);
    EXPECT_NE(&d, f);
    delete f;
}
}  // namespace souffle::ram::test
