/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2019, The Souffle Developers. All rights reserved.
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file InterpreterBTreeIndex.cpp
 *
 * Interpreter index with generic interface.
 *
 ***********************************************************************/

#include "interpreter/InterpreterIndex.h"
#include "souffle/CompiledTuple.h"
#include "souffle/RamTypes.h"
#include "souffle/datastructure/BTree.h"
#include "souffle/utility/MiscUtil.h"
#include <algorithm>
#include <cstddef>
#include <memory>
#include <ostream>
#include <vector>

namespace souffle {

// The comparator to be used for B-tree nodes.
template <std::size_t Arity>
using comparator = typename index_utils::get_full_index<Arity>::type::comparator;

// Node type
template <std::size_t Arity>
using t_tuple = typename souffle::Tuple<RamDomain, Arity>;

/**
 * A index adapter for B-trees, using the generic index adapter.
 */
template <std::size_t Arity>
class BTreeIndex : public GenericIndex<btree_set<t_tuple<Arity>, comparator<Arity>>> {
public:
    using GenericIndex<btree_set<t_tuple<Arity>, comparator<Arity>>>::GenericIndex;
};

std::unique_ptr<InterpreterIndex> createBTreeIndex(const Order& order) {
    switch (order.size()) {
        case 0: return std::make_unique<NullaryIndex>();
        case 1: return std::make_unique<BTreeIndex<1>>(order);
        case 2: return std::make_unique<BTreeIndex<2>>(order);
        case 3: return std::make_unique<BTreeIndex<3>>(order);
        case 4: return std::make_unique<BTreeIndex<4>>(order);
        case 5: return std::make_unique<BTreeIndex<5>>(order);
        case 6: return std::make_unique<BTreeIndex<6>>(order);
        case 7: return std::make_unique<BTreeIndex<7>>(order);
        case 8: return std::make_unique<BTreeIndex<8>>(order);
        case 9: return std::make_unique<BTreeIndex<9>>(order);
        case 10: return std::make_unique<BTreeIndex<10>>(order);
        case 11: return std::make_unique<BTreeIndex<11>>(order);
        case 12: return std::make_unique<BTreeIndex<12>>(order);
        case 13: return std::make_unique<BTreeIndex<13>>(order);
        case 14: return std::make_unique<BTreeIndex<14>>(order);
        case 15: return std::make_unique<BTreeIndex<15>>(order);
        case 16: return std::make_unique<BTreeIndex<16>>(order);
        case 17: return std::make_unique<BTreeIndex<17>>(order);
        case 18: return std::make_unique<BTreeIndex<18>>(order);
        case 19: return std::make_unique<BTreeIndex<19>>(order);
        case 20: return std::make_unique<BTreeIndex<20>>(order);
    }

    fatal("Requested arity not yet supported. Feel free to add it.");
}

}  // namespace souffle
