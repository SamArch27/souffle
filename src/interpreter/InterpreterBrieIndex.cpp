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
#include <cstddef>
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

std::unique_ptr<InterpreterIndex> createBrieIndex(const Order& order) {
    switch (order.size()) {
        case 0: return std::make_unique<NullaryIndex>();
        case 1: return std::make_unique<BrieIndex<1>>(order);
        case 2: return std::make_unique<BrieIndex<2>>(order);
        case 3: return std::make_unique<BrieIndex<3>>(order);
        case 4: return std::make_unique<BrieIndex<4>>(order);
        case 5: return std::make_unique<BrieIndex<5>>(order);
        case 6: return std::make_unique<BrieIndex<6>>(order);
        case 7: return std::make_unique<BrieIndex<7>>(order);
        case 8: return std::make_unique<BrieIndex<8>>(order);
        case 9: return std::make_unique<BrieIndex<9>>(order);
        case 10: return std::make_unique<BrieIndex<10>>(order);
        case 11: return std::make_unique<BrieIndex<11>>(order);
        case 12: return std::make_unique<BrieIndex<12>>(order);
        case 13: return std::make_unique<BrieIndex<13>>(order);
        case 14: return std::make_unique<BrieIndex<14>>(order);
        case 15: return std::make_unique<BrieIndex<15>>(order);
        case 16: return std::make_unique<BrieIndex<16>>(order);
        case 17: return std::make_unique<BrieIndex<17>>(order);
        case 18: return std::make_unique<BrieIndex<18>>(order);
        case 19: return std::make_unique<BrieIndex<19>>(order);
        case 20: return std::make_unique<BrieIndex<20>>(order);
    }

    fatal("Requested arity not yet supported. Feel free to add it.");
}

}  // namespace souffle
