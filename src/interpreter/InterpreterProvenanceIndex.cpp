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

Own<InterpreterIndex> createBTreeProvenanceIndex(const Order& order) {
    switch (order.size()) {
        case 0:
        case 1: fatal("Provenance relation with arity < 2.");
        case 2: return mk<BTreeProvenanceIndex<2>>(order);
        case 3: return mk<BTreeProvenanceIndex<3>>(order);
        case 4: return mk<BTreeProvenanceIndex<4>>(order);
        case 5: return mk<BTreeProvenanceIndex<5>>(order);
        case 6: return mk<BTreeProvenanceIndex<6>>(order);
        case 7: return mk<BTreeProvenanceIndex<7>>(order);
        case 8: return mk<BTreeProvenanceIndex<8>>(order);
        case 9: return mk<BTreeProvenanceIndex<9>>(order);
        case 10: return mk<BTreeProvenanceIndex<10>>(order);
        case 11: return mk<BTreeProvenanceIndex<11>>(order);
        case 12: return mk<BTreeProvenanceIndex<12>>(order);
        case 13: return mk<BTreeProvenanceIndex<13>>(order);
        case 14: return mk<BTreeProvenanceIndex<14>>(order);
        case 15: return mk<BTreeProvenanceIndex<15>>(order);
        case 16: return mk<BTreeProvenanceIndex<16>>(order);
        case 17: return mk<BTreeProvenanceIndex<17>>(order);
        case 18: return mk<BTreeProvenanceIndex<18>>(order);
        case 19: return mk<BTreeProvenanceIndex<19>>(order);
        case 20: return mk<BTreeProvenanceIndex<20>>(order);
        case 21: return mk<BTreeProvenanceIndex<21>>(order);
        case 22: return mk<BTreeProvenanceIndex<22>>(order);
        case 23: return mk<BTreeProvenanceIndex<23>>(order);
        case 24: return mk<BTreeProvenanceIndex<24>>(order);
        case 25: return mk<BTreeProvenanceIndex<25>>(order);
        case 26: return mk<BTreeProvenanceIndex<26>>(order);
        case 27: return mk<BTreeProvenanceIndex<27>>(order);
        case 28: return mk<BTreeProvenanceIndex<28>>(order);
        case 29: return mk<BTreeProvenanceIndex<29>>(order);
        case 30: return mk<BTreeProvenanceIndex<30>>(order);
    }

    fatal("Requested arity not yet supported. Feel free to add it.");
}

}  // namespace souffle
