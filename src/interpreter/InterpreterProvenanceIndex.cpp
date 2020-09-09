/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2019, The Souffle Developers. All rights reserved.
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file InterpreterProvenanceIndex.cpp
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

// Updater for Provenance
template <std::size_t Arity>
struct InterpreterProvenanceUpdater {
    void update(t_tuple<Arity>& old_t, const t_tuple<Arity>& new_t) {
        old_t[Arity - 2] = new_t[Arity - 2];
        old_t[Arity - 1] = new_t[Arity - 1];
    }
};

/**
 * Btree index for provenance relation
 */
template <std::size_t Arity>
class BTreeProvenanceIndex
        : public GenericIndex<btree_set<t_tuple<Arity>, comparator<Arity>, std::allocator<t_tuple<Arity>>,
                  256, typename detail::default_strategy<t_tuple<Arity>>::type, comparator<Arity - 2>,
                  InterpreterProvenanceUpdater<Arity>>> {
public:
    using GenericIndex<btree_set<t_tuple<Arity>, comparator<Arity>, std::allocator<t_tuple<Arity>>, 256,
            typename detail::default_strategy<t_tuple<Arity>>::type, comparator<Arity - 2>,
            InterpreterProvenanceUpdater<Arity>>>::GenericIndex;
};

std::unique_ptr<InterpreterIndex> createBTreeProvenanceIndex(const Order& order) {
    switch (order.size()) {
        case 0:
        case 1: fatal("Provenance relation with arity < 2.");
        case 2: return std::make_unique<BTreeProvenanceIndex<2>>(order);
        case 3: return std::make_unique<BTreeProvenanceIndex<3>>(order);
        case 4: return std::make_unique<BTreeProvenanceIndex<4>>(order);
        case 5: return std::make_unique<BTreeProvenanceIndex<5>>(order);
        case 6: return std::make_unique<BTreeProvenanceIndex<6>>(order);
        case 7: return std::make_unique<BTreeProvenanceIndex<7>>(order);
        case 8: return std::make_unique<BTreeProvenanceIndex<8>>(order);
        case 9: return std::make_unique<BTreeProvenanceIndex<9>>(order);
        case 10: return std::make_unique<BTreeProvenanceIndex<10>>(order);
        case 11: return std::make_unique<BTreeProvenanceIndex<11>>(order);
        case 12: return std::make_unique<BTreeProvenanceIndex<12>>(order);
        case 13: return std::make_unique<BTreeProvenanceIndex<13>>(order);
        case 14: return std::make_unique<BTreeProvenanceIndex<14>>(order);
        case 15: return std::make_unique<BTreeProvenanceIndex<15>>(order);
        case 16: return std::make_unique<BTreeProvenanceIndex<16>>(order);
        case 17: return std::make_unique<BTreeProvenanceIndex<17>>(order);
        case 18: return std::make_unique<BTreeProvenanceIndex<18>>(order);
        case 19: return std::make_unique<BTreeProvenanceIndex<19>>(order);
        case 20: return std::make_unique<BTreeProvenanceIndex<20>>(order);
        case 21: return std::make_unique<BTreeProvenanceIndex<21>>(order);
        case 22: return std::make_unique<BTreeProvenanceIndex<22>>(order);
        case 23: return std::make_unique<BTreeProvenanceIndex<23>>(order);
        case 24: return std::make_unique<BTreeProvenanceIndex<24>>(order);
        case 25: return std::make_unique<BTreeProvenanceIndex<25>>(order);
        case 26: return std::make_unique<BTreeProvenanceIndex<26>>(order);
        case 27: return std::make_unique<BTreeProvenanceIndex<27>>(order);
        case 28: return std::make_unique<BTreeProvenanceIndex<28>>(order);
        case 29: return std::make_unique<BTreeProvenanceIndex<29>>(order);
        case 30: return std::make_unique<BTreeProvenanceIndex<30>>(order);
    }

    fatal("Requested arity not yet supported. Feel free to add it.");
}

}  // namespace souffle
