/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2019, The Souffle Developers. All rights reserved.
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file InterpreterIndex.cpp
 *
 * Interpreter index with generic interface.
 *
 ***********************************************************************/

#include "interpreter/InterpreterIndex.h"
#include "souffle/utility/StreamUtil.h"
#include <ostream>

namespace souffle {

Order Order::create(size_t arity) {
    Order res;
    res.order.resize(arity);
    for (size_t i = 0; i < arity; i++) {
        res.order[i] = i;
    }
    return res;
}

std::size_t Order::size() const {
    return order.size();
}

bool Order::valid() const {
    // Check that all indices are in range.
    for (int i : order) {
        if (i < 0 || i >= int(order.size())) {
            return false;
        }
    }
    // Check that there are no duplicates.
    for (std::size_t i = 0; i < order.size(); i++) {
        for (std::size_t j = i + 1; j < order.size(); j++) {
            if (order[i] == order[j]) {
                return false;
            }
        }
    }
    return true;
}

bool Order::operator==(const Order& other) const {
    return order == other.order;
}

bool Order::operator!=(const Order& other) const {
    return !(*this == other);
}

bool Order::operator<(const Order& other) const {
    return order < other.order;
}

std::ostream& operator<<(std::ostream& out, const Order& order) {
    return out << "[" << join(order.order) << "]";
}

std::ostream& operator<<(std::ostream& out, TupleRef ref) {
    out << "[";
    for (std::size_t i = 0; i < ref.size(); i++) {
        if (i > 0) {
            out << ',';
        }
        out << ref[i];
    }
    return out << "]";
}

}  // namespace souffle
