/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file UnaryOperator.h
 *
 * Defines unary operators and relational operators.
 *
 ***********************************************************************/
#pragma once

#include <cassert>

namespace souffle {

/**
 * Unary Operators
 */
enum class UnaryOp {
    __UNDEFINED__,
    ORD,
    NEG,
    BNOT,
    LNOT
};

/**
 * Returns the corresponding symbol for the given relational operator.
 */
inline std::string getSymbolForUnaryOp(UnaryOp op) {
    switch(op) {
    case UnaryOp::ORD : return "ord";
    case UnaryOp::NEG : return "-";
    case UnaryOp::BNOT : return "bnot";
    case UnaryOp::LNOT : return "lnot";
    default: break;
    }
    assert(false && "Unsupported Operator!");
    return "?";
}

/**
 * Returns the corresponding operator for the given symbol.
 */
inline UnaryOp getUnaryOpForSymbol(const std::string &symbol) {
    if (symbol == "ord") return  UnaryOp::ORD;
    if (symbol == "-") return  UnaryOp::NEG;
    if (symbol == "bnot") return  UnaryOp::BNOT;
    if (symbol == "lnot") return  UnaryOp::LNOT;
    std::cout << "Unrecognised operator: " << symbol << "\n";
    assert(false && "Unsupported Operator!");
    return UnaryOp::__UNDEFINED__;
}

/**
 * Returns whether the given operator has a numeric return value.
 */
inline bool isNumericUnaryOp(const UnaryOp op) {
    switch(op) {
    case UnaryOp::ORD:
    case UnaryOp::NEG:
    case UnaryOp::BNOT:
    case UnaryOp::LNOT: return true;
    default: break;
    }
    assert(false && "Uncovered case!");
    return false;
}

/**
 * Returns whether the given operator has a symbolic return value.
 */
inline bool isSymbolicUnaryOp(const UnaryOp op) {
    return !isNumericUnaryOp(op);
}

/**
 * Returns whether the given operator takes a numeric argument.
 */
inline bool unaryOpAcceptsNumbers(const UnaryOp op) {
    switch (op) {
    case UnaryOp::NEG:
    case UnaryOp::BNOT:
    case UnaryOp::LNOT: return true;
    case UnaryOp::ORD: return false;
    default: break;
    }
    assert(false && "Unsupported operator encountered!");
    return false;
}

/**
 * Returns whether the given operator takes a symbolic argument.
 */
inline bool unaryOpAcceptsSymbols(const UnaryOp op) {
    return !unaryOpAcceptsNumbers(op);
}

} // end of namespace souffle

