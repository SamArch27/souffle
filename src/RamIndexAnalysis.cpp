/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file IndexAnalysis.cpp
 *
 * Computes indexes for relations in a translation unit
 *
 ***********************************************************************/

#include "RamIndexAnalysis.h"
#include "RamCondition.h"
#include "RamExpression.h"
#include "RamNode.h"
#include "RamOperation.h"
#include "RamProgram.h"
#include "RamRelation.h"
#include "RamStatement.h"
#include "RamTranslationUnit.h"
#include "RamUtils.h"
#include "RamVisitor.h"
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <iterator>
#include <queue>

namespace souffle {

SearchSignature::SearchSignature(size_t arity) : constraints(arity, AttributeConstraint::None) {}

size_t SearchSignature::arity() const {
    return constraints.size();
}

// array subscript operator
AttributeConstraint SearchSignature::operator[](std::size_t pos) const {
    assert(pos < constraints.size());
    return constraints[pos];
}

// comparison operators
bool SearchSignature::operator<(const SearchSignature& other) const {
    assert(constraints.size() == other.constraints.size());
    size_t len = constraints.size();

    for (size_t i = 0; i < len; ++i) {
        if (constraints[i] != AttributeConstraint::None &&
                other.constraints[i] == AttributeConstraint::None) {
            return false;
        }
        if (constraints[i] == AttributeConstraint::None &&
                other.constraints[i] != AttributeConstraint::None) {
            return true;
        }
    }

    for (size_t i = 0; i < len; ++i) {
        // if ours has a constraint and other's has a constraint then it is smaller
        if (constraints[i] < other.constraints[i]) {
            return true;
        }
        // if ours has a constraint and other's has no constraint then it is larger
        else if (constraints[i] > other.constraints[i]) {
            return false;
        }
    }
    return false;
}

bool SearchSignature::operator==(const SearchSignature& other) const {
    assert(constraints.size() == other.constraints.size());
    for (size_t i = 0; i < constraints.size(); ++i) {
        if (constraints[i] == AttributeConstraint::None &&
                other.constraints[i] != AttributeConstraint::None) {
            return false;
        }
        if (constraints[i] != AttributeConstraint::None &&
                other.constraints[i] == AttributeConstraint::None) {
            return false;
        }
    }
    return true;
}

bool SearchSignature::empty() const {
    size_t len = constraints.size();
    for (size_t i = 0; i < len; ++i) {
        if (constraints[i] != AttributeConstraint::None) {
            return false;
        }
    }
    return true;
}

bool SearchSignature::isComparable(const SearchSignature& lhs, const SearchSignature& rhs) {
    assert(lhs.arity() == rhs.arity());
    return isStrictSubset(lhs, rhs) || isStrictSubset(rhs, lhs);
}

bool SearchSignature::isStrictSubset(const SearchSignature& lhs, const SearchSignature& rhs) {
    assert(lhs.arity() == rhs.arity());
    size_t len = lhs.arity();
    for (size_t i = 0; i < len; ++i) {
        if ((lhs.constraints[i] != AttributeConstraint::None) &&
                (rhs.constraints[i] == AttributeConstraint::None)) {
            return false;
        }
    }
    return lhs.constraints != rhs.constraints;
}

SearchSignature SearchSignature::getDelta(const SearchSignature& lhs, const SearchSignature& rhs) {
    assert(lhs.arity() == rhs.arity());
    SearchSignature delta(lhs.arity());
    for (size_t i = 0; i < lhs.arity(); ++i) {
        // if constraints are the same then delta is nothing
        if (lhs.constraints[i] == rhs.constraints[i]) {
            delta.constraints[i] = AttributeConstraint::None;
            continue;
        }

        // if rhs has no constraint then delta has lhs constraint
        if (rhs.constraints[i] == AttributeConstraint::None) {
            delta.constraints[i] = lhs.constraints[i];
            continue;
        }

        // in the special case where we have equality/inequality bounds consider the delta to be 0
        delta.constraints[i] = AttributeConstraint::None;
    }
    return delta;
}

SearchSignature SearchSignature::getFullSearchSignature(size_t arity) {
    SearchSignature res(arity);
    for (size_t i = 0; i < arity; ++i) {
        res.constraints[i] = AttributeConstraint::Equal;
    }
    return res;
}

// set a constraint
SearchSignature& SearchSignature::set(size_t pos, AttributeConstraint constraint) {
    assert(pos < constraints.size());
    constraints[pos] = constraint;
    return *this;
}

std::ostream& operator<<(std::ostream& out, const SearchSignature& signature) {
    size_t len = signature.constraints.size();
    for (size_t i = 0; i < len; ++i) {
        switch (signature.constraints[i]) {
            case AttributeConstraint::None: out << 0; break;
            case AttributeConstraint::Equal: out << 1; break;
            case AttributeConstraint::Inequal: out << 2; break;
        }
    }
    return out;
}

void MaxMatching::addEdge(Node u, Node v) {
    assert(u >= 1 && v >= 1 && "Nodes must be greater than or equal to 1");
    if (graph.find(u) == graph.end()) {
        Edges vals;
        vals.insert(v);
        graph.insert(make_pair(u, vals));
    } else {
        graph[u].insert(v);
    }
}

MaxMatching::Node MaxMatching::getMatch(Node v) {
    auto it = match.find(v);
    if (it == match.end()) {
        return NullVertex;
    }
    return it->second;
}

MaxMatching::Distance MaxMatching::getDistance(Node v) {
    auto it = distance.find(v);
    if (it == distance.end()) {
        return InfiniteDistance;
    }
    return it->second;
}

bool MaxMatching::bfSearch() {
    Node u;
    std::queue<Node> bfQueue;
    // Build layers
    for (auto& it : graph) {
        if (getMatch(it.first) == NullVertex) {
            distance[it.first] = 0;
            bfQueue.push(it.first);
        } else {
            distance[it.first] = InfiniteDistance;
        }
    }

    distance[NullVertex] = InfiniteDistance;
    while (!bfQueue.empty()) {
        u = bfQueue.front();
        bfQueue.pop();
        assert(u != NullVertex);
        const Edges& children = graph[u];
        for (auto it : children) {
            Node mv = getMatch(it);
            if (getDistance(mv) == InfiniteDistance) {
                distance[mv] = getDistance(u) + 1;
                if (mv != NullVertex) {
                    bfQueue.push(mv);
                }
            }
        }
    }
    return (getDistance(NullVertex) != InfiniteDistance);
}

bool MaxMatching::dfSearch(Node u) {
    if (u != 0) {
        Edges& children = graph[u];
        for (auto v : children) {
            if (getDistance(getMatch(v)) == getDistance(u) + 1) {
                if (dfSearch(getMatch(v))) {
                    match[u] = v;
                    match[v] = u;
                    return true;
                }
            }
        }

        distance[u] = InfiniteDistance;
        return false;
    }
    return true;
}

const MaxMatching::Matchings& MaxMatching::solve() {
    while (bfSearch()) {
        for (auto& it : graph) {
            if (getMatch(it.first) == NullVertex) {
                dfSearch(it.first);
            }
        }
    }
    return match;
}

void MinIndexSelection::solve() {
    // map the keys in the key set to lexicographical order
    if (searches.empty()) {
        return;
    }

    // map the signatures of each searches to a unique index for the matching problem
    AttributeIndex currentIndex = 1;
    for (SearchSignature s : searches) {
        // we skip if the search is empty
        if (s.empty()) {
            continue;
        }

        // map the signature to its unique index in each set
        signatureToIndexA.insert({s, currentIndex});
        signatureToIndexB.insert({s, currentIndex + 1});
        // map each index back to the search signature
        indexToSignature.insert({currentIndex, s});
        indexToSignature.insert({currentIndex + 1, s});
        currentIndex += 2;
    }

    // Construct the matching poblem
    for (auto search : searches) {
        // For this node check if other nodes are strict subsets
        for (auto itt : searches) {
            if (SearchSignature::isStrictSubset(search, itt)) {
                // less general searches only have out edges to more general counterpart
                if (lessGeneralSearches.count(search) > 0) {
                    continue;
                }
                // more general searches only have in edges from less general counterpart
                if (moreGeneralSearches.count(itt) > 0) {
                    continue;
                }

                // dont draw an edge from more to less general counterpart
                if (moreGeneralSearches.count(search) > 0 && lessGeneralSearches.count(itt) > 0) {
                    continue;
                }

                bool containsInequality = false;
                for (size_t i = 0; i < search.arity(); ++i) {
                    if (search[i] == AttributeConstraint::Inequal) {
                        containsInequality = true;
                    }
                }
                if (!containsInequality) {
                    matching.addEdge(signatureToIndexA[search], signatureToIndexB[itt]);
                }
            }
        }
    }

    // add edges from less -> more general pairs
    for (auto less : lessGeneralSearches) {
        auto more = lessToMoreGeneralSearch.at(less);
        matching.addEdge(signatureToIndexA[less], signatureToIndexB[more]);
    }

    // Perform the Hopcroft-Karp on the graph and receive matchings (mapped A->B and B->A)
    // Assume: alg.calculate is not called on an empty graph
    assert(!searches.empty());
    const MaxMatching::Matchings& matchings = matching.solve();
    // Extract the chains given the nodes and matchings
    ChainOrderMap chains = getChainsFromMatching(matchings, searches);
    // Should never get no chains back as we never call calculate on an empty graph
    assert(!chains.empty());
    // std::cout << "End: " << chains.size() << "\n;

    for (const auto& chain : chains) {
        std::vector<uint32_t> ids;
        SearchSignature initDelta = *(chain.begin());
        insertIndex(ids, initDelta);

        for (auto iit = chain.begin(); next(iit) != chain.end(); ++iit) {
            SearchSignature delta = SearchSignature::getDelta(*next(iit), *iit);
            insertIndex(ids, delta);
        }

        assert(!ids.empty());

        orders.push_back(ids);
    }

    // Construct the matching poblem
    for (auto search : searches) {
        int idx = map(search);
        size_t l = card(search);
        SearchSignature k(search.arity());
        for (size_t i = 0; i < l; i++) {
            k.set(orders[idx][i], AttributeConstraint::Equal);
        }
        for (size_t i = 0; i < search.arity(); ++i) {
            if (k[i] == AttributeConstraint::None && search[i] != AttributeConstraint::None) {
                assert("incorrect lexicographical order");
            }
            if (k[i] != AttributeConstraint::None && search[i] == AttributeConstraint::None) {
                assert("incorrect lexicographical order");
            }
        }
    }
}

MinIndexSelection::Chain MinIndexSelection::getChain(
        const SearchSignature umn, const MaxMatching::Matchings& match) {
    SearchSignature start = umn;  // start at an unmatched node
    Chain chain;
    // given an unmapped node from set A we follow it from set B until it cannot be matched from B
    //  if not mateched from B then umn is a chain
    //
    // Assume : no circular mappings, i.e. a in A -> b in B -> ........ -> a in A is not allowed.
    // Given this, the loop will terminate
    while (true) {
        auto mit = match.find(signatureToIndexB[start]);  // we start from B side
        // on each iteration we swap sides when collecting the chain so we use the corresponding index map
        chain.insert(start);

        if (mit == match.end()) {
            return chain;
        }

        SearchSignature a = indexToSignature.at(mit->second);
        chain.insert(a);
        start = a;
    }
}

const MinIndexSelection::ChainOrderMap MinIndexSelection::getChainsFromMatching(
        const MaxMatching::Matchings& match, const SearchSet& nodes) {
    assert(!nodes.empty());

    // Get all unmatched nodes from A
    const SearchSet& umKeys = getUnmatchedKeys(match, nodes);

    // Case: if no unmatched nodes then we have an anti-chain
    if (umKeys.empty()) {
        for (auto node : nodes) {
            std::set<SearchSignature> a;
            a.insert(node);
            chainToOrder.push_back(a);
            return mergeChains(chainToOrder);
        }
    }

    assert(!umKeys.empty());

    // A worklist of used nodes
    SearchSet usedKeys;

    // Case: nodes < umKeys or if nodes == umKeys then anti chain - this is handled by this loop
    for (auto umKey : umKeys) {
        Chain c = getChain(umKey, match);
        assert(!c.empty());
        chainToOrder.push_back(c);
    }

    assert(!chainToOrder.empty());

    return mergeChains(chainToOrder);
}

// Merge the chains at the cost of 1 indexed inequality for 1 less chain/index
const MinIndexSelection::ChainOrderMap MinIndexSelection::mergeChains(
        MinIndexSelection::ChainOrderMap& chains) {
    bool changed = true;
    while (changed) {
        changed = false;
        for (auto lhs_it = chains.begin(); lhs_it != chains.end(); ++lhs_it) {
            const auto lhs = *lhs_it;
            for (auto rhs_it = lhs_it; rhs_it != chains.end(); ++rhs_it) {
                const auto rhs = *rhs_it;

                // merge the two chains
                Chain mergedChain;

                // apply merge algorithm ensuring that both elements are always comparable
                bool successfulMerge = true;
                auto left = lhs.begin();
                auto right = rhs.begin();

                while (left != lhs.end() && right != rhs.end()) {
                    // if we can't compare them then we cannot merge and exit
                    if (!SearchSignature::isComparable(*left, *right)) {
                        successfulMerge = false;
                        break;
                    }
                    // if left element is smaller, insert it and iterate to next in left chain
                    if (*left < *right) {
                        mergedChain.insert(*left);
                        ++left;
                        continue;
                    }
                    // if right element is smaller, insert it and iterate to next in right chain
                    if (*right < *left) {
                        mergedChain.insert(*right);
                        ++right;
                        continue;
                    }
                }

                // failed to merge so find another pair of chains
                if (!successfulMerge) {
                    continue;
                }

                // if left chain is exhausted then merge the rest of right chain
                if (left == lhs.end()) {
                    while (right != rhs.end()) {
                        mergedChain.insert(*right);
                        ++right;
                    }
                }
                // if right chain is exhuasted then merge the rest of left chain
                if (right == rhs.end()) {
                    while (left != lhs.end()) {
                        mergedChain.insert(*left);
                        ++left;
                    }
                }

                changed = true;
                // remove previous 2 chains
                chains.erase(std::remove(chains.begin(), chains.end(), lhs), chains.end());
                chains.erase(std::remove(chains.begin(), chains.end(), rhs), chains.end());

                // insert merge chain
                chains.push_back(mergedChain);
                break;
            }
            if (changed) {
                break;
            }
        }
    }

    size_t inequalities = 0;
    for (const auto& chain : chains) {
        auto end = *chain.rbegin();
        bool hasIndexedInequality = false;
        for (size_t i = 0; i < end.arity(); ++i) {
            if (end[i] == AttributeConstraint::Inequal) {
                hasIndexedInequality = true;
            }
        }
        if (hasIndexedInequality) {
            ++inequalities;
        }
    }

    return chains;
}

MinIndexSelection::AttributeSet MinIndexSelection::getAttributesToDischarge(const RamRelation& rel) {
    // by default we have all attributes w/inequalities discharged
    AttributeSet attributesToDischarge;
    for (auto search : searches) {
        size_t arity = search.arity();
        for (size_t i = 0; i < arity; ++i) {
            if (search[i] == AttributeConstraint::Inequal) {
                attributesToDischarge.insert(i);
            }
        }
    }
    // if we don't have a btree then we don't retain any inequalities
    if (rel.getRepresentation() != RelationRepresentation::BTREE &&
            rel.getRepresentation() != RelationRepresentation::DEFAULT) {
        return attributesToDischarge;
    }
    if (Global::config().has("provenance")) {
        return attributesToDischarge;
    }
    for (LexOrder order : orders) {
        auto end = order.back();
        // don't discharge if we have a numeric attribute in the last position
        if (rel.getAttributeTypes()[end] == "i:number") {
            // if this is an inequality then it won't be discharged
            attributesToDischarge.erase(end);
        }
    }
    return attributesToDischarge;
}

void RamIndexAnalysis::run(const RamTranslationUnit& translationUnit) {
    // After complete:
    // 1. All relations should have at least one index (for full-order search).
    // 2. Two relations involved in a swap operation will have same set of indices.
    // 3. A 0-arity relation will have only one index where LexOrder is defined as empty. A comparator using
    // an empty order should regard all elements as equal and therefore only allow one arbitrary tuple to be
    // inserted.
    //
    // TODO:
    // 0-arity relation in a provenance program still need to be revisited.

    // visit all nodes to collect searches of each relation
    visitDepthFirst(translationUnit.getProgram(), [&](const RamNode& node) {
        if (const auto* indexSearch = dynamic_cast<const RamIndexOperation*>(&node)) {
            MinIndexSelection& indexes = getIndexes(indexSearch->getRelation());
            indexes.addSearch(getSearchSignature(indexSearch));
        } else if (const auto* exists = dynamic_cast<const RamExistenceCheck*>(&node)) {
            MinIndexSelection& indexes = getIndexes(exists->getRelation());
            indexes.addSearch(getSearchSignature(exists));
        } else if (const auto* provExists = dynamic_cast<const RamProvenanceExistenceCheck*>(&node)) {
            MinIndexSelection& indexes = getIndexes(provExists->getRelation());
            indexes.addSearch(getSearchSignature(provExists));
        } else if (const auto* ramRel = dynamic_cast<const RamRelation*>(&node)) {
            MinIndexSelection& indexes = getIndexes(*ramRel);
            indexes.addSearch(getSearchSignature(ramRel));
        }
    });

    // A swap happen between rel A and rel B indicates A should include all indices of B, vice versa.
    visitDepthFirst(translationUnit.getProgram(), [&](const RamSwap& swap) {
        // Note: this naive approach will not work if there exists chain or cyclic swapping.
        // e.g.  swap(relA, relB) swap(relB, relC) swap(relC, relA)
        // One need to keep merging the search set until a fixed point where no more index is introduced
        // in any of the relation in a complete iteration.
        //
        // Currently RAM does not have such situation.
        const RamRelation& relA = swap.getFirstRelation();
        const RamRelation& relB = swap.getSecondRelation();

        MinIndexSelection& indexesA = getIndexes(relA);
        MinIndexSelection& indexesB = getIndexes(relB);
        // Add all searchSignature of A into B
        for (const auto& signature : indexesA.getSearches()) {
            indexesB.addSearch(signature);
        }

        // Add all searchSignature of B into A
        for (const auto& signature : indexesB.getSearches()) {
            indexesA.addSearch(signature);
        }
    });

    // find optimal indexes for relations
    for (auto& cur : minIndexCover) {
        MinIndexSelection& indexes = cur.second;
        indexes.solve();
    }

    // Only case where indexSet is still empty is when relation has arity == 0
    for (auto& cur : minIndexCover) {
        MinIndexSelection& indexes = cur.second;
        if (indexes.getAllOrders().empty()) {
            indexes.insertDefaultTotalIndex(0);
        }
    }
}

MinIndexSelection& RamIndexAnalysis::getIndexes(const RamRelation& rel) {
    auto pos = minIndexCover.find(&rel);
    if (pos != minIndexCover.end()) {
        return pos->second;
    } else {
        auto ret = minIndexCover.insert(std::make_pair(&rel, MinIndexSelection()));
        assert(ret.second);
        return ret.first->second;
    }
}

void RamIndexAnalysis::print(std::ostream& os) const {
    for (auto& cur : minIndexCover) {
        const RamRelation& rel = *cur.first;
        const MinIndexSelection& indexes = cur.second;
        const std::string& relName = rel.getName();

        /* Print searches */
        os << "Relation " << relName << "\n";
        os << "\tNumber of Primitive Searches: " << indexes.getSearches().size() << "\n";

        const auto& attrib = rel.getAttributeNames();
        size_t arity = rel.getArity();

        /* print searches */
        for (auto& cols : indexes.getSearches()) {
            os << "\t\t";
            for (size_t i = 0; i < arity; i++) {
                if (cols[i] != AttributeConstraint::None) {
                    os << attrib[i] << " ";
                }
            }
            os << "\n";
        }

        os << "\tNumber of Indexes: " << indexes.getAllOrders().size() << "\n";
        for (auto& order : indexes.getAllOrders()) {
            os << "\t\t";
            for (auto& i : order) {
                os << attrib[i] << " ";
            }
            os << "\n";
        }
    }
}

namespace {
// handles equality constraints
template <typename Iter>
SearchSignature searchSignature(size_t arity, Iter const& bgn, Iter const& end) {
    SearchSignature keys(arity);

    size_t i = 0;
    for (auto cur = bgn; cur != end; ++cur, ++i) {
        if (!isRamUndefValue(*cur)) {
            keys.set(i, AttributeConstraint::Equal);
        }
    }
    return keys;
}

template <typename Seq>
SearchSignature searchSignature(size_t arity, Seq const& xs) {
    return searchSignature(arity, xs.begin(), xs.end());
}
}  // namespace

SearchSignature RamIndexAnalysis::getSearchSignature(const RamIndexOperation* search) const {
    size_t arity = search->getRelation().getArity();

    auto lower = search->getRangePattern().first;
    auto upper = search->getRangePattern().second;
    SearchSignature keys(arity);
    for (size_t i = 0; i < arity; ++i) {
        // if both bounds are undefined
        if (isRamUndefValue(lower[i]) && isRamUndefValue(upper[i])) {
            keys.set(i, AttributeConstraint::None);
            // if bounds are equal we have an equality
        } else if (*lower[i] == *upper[i]) {
            keys.set(i, AttributeConstraint::Equal);
        } else {
            keys.set(i, AttributeConstraint::Inequal);
        }
    }
    return keys;
}

SearchSignature RamIndexAnalysis::getSearchSignature(
        const RamProvenanceExistenceCheck* provExistCheck) const {
    const auto values = provExistCheck->getValues();
    auto auxiliaryArity = provExistCheck->getRelation().getAuxiliaryArity();

    // values.size() - auxiliaryArity because we discard the height annotations
    auto const numSig = values.size() - auxiliaryArity;
    return searchSignature(auxiliaryArity, values.begin(), values.begin() + numSig);
}

SearchSignature RamIndexAnalysis::getSearchSignature(const RamExistenceCheck* existCheck) const {
    return searchSignature(existCheck->getRelation().getArity(), existCheck->getValues());
}

SearchSignature RamIndexAnalysis::getSearchSignature(const RamRelation* ramRel) const {
    return SearchSignature::getFullSearchSignature(ramRel->getArity());
}

bool RamIndexAnalysis::isTotalSignature(const RamAbstractExistenceCheck* existCheck) const {
    for (const auto& cur : existCheck->getValues()) {
        if (isRamUndefValue(cur)) {
            return false;
        }
    }
    return true;
}

}  // end of namespace souffle
