/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2019, The Souffle Developers. All rights reserved.
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file InterpreterBrieIndex.cpp
 *
 * Interpreter index with generic interface.
 *
 ***********************************************************************/

#include "interpreter/InterpreterIndex.h"
#include "souffle/datastructure/Brie.h"
#include "souffle/utility/MiscUtil.h"
#include <algorithm>
#include <memory>
#include <ostream>
#include <vector>

namespace souffle {

/**
 * A index adapter for Bries, using the generic index adapter.
 */
template <std::size_t Arity>
class BrieIndex : public GenericIndex<Trie<Arity>> {
public:
    using GenericIndex<Trie<Arity>>::GenericIndex;
};

Own<InterpreterIndex> createBrieIndex(const Order& order) {
    switch (order.size()) {
        case 0: return mk<NullaryIndex>();
        case 1: return mk<BrieIndex<1>>(order);
        case 2: return mk<BrieIndex<2>>(order);
        case 3: return mk<BrieIndex<3>>(order);
        case 4: return mk<BrieIndex<4>>(order);
        case 5: return mk<BrieIndex<5>>(order);
        case 6: return mk<BrieIndex<6>>(order);
        case 7: return mk<BrieIndex<7>>(order);
        case 8: return mk<BrieIndex<8>>(order);
        case 9: return mk<BrieIndex<9>>(order);
        case 10: return mk<BrieIndex<10>>(order);
        case 11: return mk<BrieIndex<11>>(order);
        case 12: return mk<BrieIndex<12>>(order);
        case 13: return mk<BrieIndex<13>>(order);
        case 14: return mk<BrieIndex<14>>(order);
        case 15: return mk<BrieIndex<15>>(order);
        case 16: return mk<BrieIndex<16>>(order);
        case 17: return mk<BrieIndex<17>>(order);
        case 18: return mk<BrieIndex<18>>(order);
        case 19: return mk<BrieIndex<19>>(order);
        case 20: return mk<BrieIndex<20>>(order);
    }

    fatal("Requested arity not yet supported. Feel free to add it.");
}

}  // namespace souffle
