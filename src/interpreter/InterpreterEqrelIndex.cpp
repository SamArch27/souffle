/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2019, The Souffle Developers. All rights reserved.
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file InterpreterEqrelIndex.cpp
 *
 * Interpreter index with generic interface.
 *
 ***********************************************************************/

#include "interpreter/InterpreterIndex.h"
#include "souffle/CompiledTuple.h"
#include "souffle/RamTypes.h"
#include "souffle/datastructure/EquivalenceRelation.h"
#include "souffle/datastructure/PiggyList.h"
#include <algorithm>
#include <cassert>
#include <cstddef>
#include <memory>
#include <ostream>
#include <vector>

namespace souffle {

// Node type
template <std::size_t Arity>
using t_tuple = typename souffle::Tuple<RamDomain, Arity>;

/**
 * A index adapter for EquivalenceRelation, using the generic index adapter.
 */
class EqrelIndex : public GenericIndex<EquivalenceRelation<t_tuple<2>>> {
public:
    using GenericIndex<EquivalenceRelation<t_tuple<2>>>::GenericIndex;

    void extend(InterpreterIndex* other) override {
        auto otherIndex = dynamic_cast<EqrelIndex*>(other);
        assert(otherIndex != nullptr && "Can only extend to EqrelIndex");
        this->data.extend(otherIndex->data);
    }
};

std::unique_ptr<InterpreterIndex> createEqrelIndex(const Order& order) {
    assert(order.size() == 2 && "Eqrel index must have tuple of 2 arities");
    return std::make_unique<EqrelIndex>(order);
}

}  // namespace souffle
