/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Index.cpp
 *
 * Computes indexes for relations in a translation unit
 *
 ***********************************************************************/

#include "ram/analysis/Index.h"
#include "Global.h"
#include "RelationTag.h"
#include "ram/Expression.h"
#include "ram/Node.h"
#include "ram/Program.h"
#include "ram/Relation.h"
#include "ram/Swap.h"
#include "ram/TranslationUnit.h"
#include "ram/Utils.h"
#include "ram/Visitor.h"
#include "souffle/utility/StreamUtil.h"
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <iterator>
#include <queue>

namespace souffle::ram::analysis {

SearchSignature::SearchSignature(size_t arity) : constraints(arity, AttributeConstraint::None) {}

size_t SearchSignature::arity() const {
    return constraints.size();
}

// convenient operator overload
AttributeConstraint& SearchSignature::operator[](std::size_t pos) {
    assert(pos < constraints.size());
    return constraints[pos];
}

const AttributeConstraint& SearchSignature::operator[](std::size_t pos) const {
    assert(pos < constraints.size());
    return constraints[pos];
}

// comparison operators
bool SearchSignature::operator<(const SearchSignature& other) const {
    assert(constraints.size() == other.constraints.size());
    return isComparable(*this, other) && isSubset(*this, other);
}

bool SearchSignature::operator==(const SearchSignature& other) const {
    assert(constraints.size() == other.constraints.size());
    return constraints == other.constraints;
}

bool SearchSignature::operator!=(const SearchSignature& other) const {
    return !(*this == other);
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

bool SearchSignature::containsEquality() const {
    for (size_t i = 0; i < constraints.size(); ++i) {
        if (constraints[i] == AttributeConstraint::Equal) {
            return true;
        }
    }
    return false;
}

// Note: We have 0 < 1 and 0 < 2 but we cannot say that 1 < 2.
// The reason for this is to prevent search chains such as 100->101->201 which have no valid lex-order
bool SearchSignature::isComparable(const SearchSignature& lhs, const SearchSignature& rhs) {
    assert(lhs.arity() == rhs.arity());
    if (lhs == rhs) {
        return true;
    }

    bool withinDelta = true;
    for (size_t i = 0; i < rhs.arity(); ++i) {
        if (rhs[i] == AttributeConstraint::Inequal) {
            if (lhs[i] != AttributeConstraint::None) {
                withinDelta = false;
            }
        }
    }
    return withinDelta;
}

bool SearchSignature::isSubset(const SearchSignature& lhs, const SearchSignature& rhs) {
    assert(lhs.arity() == rhs.arity());
    size_t len = lhs.arity();
    for (size_t i = 0; i < len; ++i) {
        if (lhs[i] != AttributeConstraint::None && rhs[i] == AttributeConstraint::None) {
            return false;
        }
    }
    return true;
}

SearchSignature SearchSignature::getDelta(const SearchSignature& lhs, const SearchSignature& rhs) {
    assert(lhs.arity() == rhs.arity());
    SearchSignature delta(lhs.arity());
    for (size_t i = 0; i < lhs.arity(); ++i) {
        // if constraints are the same then delta is nothing
        if (rhs[i] == AttributeConstraint::None) {
            delta.constraints[i] = lhs[i];
        } else {
            delta.constraints[i] = AttributeConstraint::None;
        }
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

SearchSignature SearchSignature::getDischarged(const SearchSignature& signature) {
    SearchSignature res = signature;  // copy original
    for (size_t i = 0; i < res.arity(); ++i) {
        if (res[i] == AttributeConstraint::Inequal) {
            res[i] = AttributeConstraint::None;
        }
    }
    return res;
}

SearchSignature SearchSignature::getFixed(const SearchSignature& signature) {
    SearchSignature res = signature;  // copy original
    for (size_t i = 0; i < res.arity(); ++i) {
        if (res[i] == AttributeConstraint::Lower) {
            res[i] = AttributeConstraint::Inequal;
        }
        if (res[i] == AttributeConstraint::Upper) {
            res[i] = AttributeConstraint::Inequal;
        }
    }
    return res;
}

std::ostream& operator<<(std::ostream& out, const SearchSignature& signature) {
    size_t len = signature.constraints.size();
    for (size_t i = 0; i < len; ++i) {
        switch (signature.constraints[i]) {
            case AttributeConstraint::None: out << 0; break;
            case AttributeConstraint::Equal: out << 1; break;
            case AttributeConstraint::Inequal: out << 2; break;
            case AttributeConstraint::Lower: out << 3; break;
            case AttributeConstraint::Upper: out << 4; break;
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
        std::vector<Node> keys(graph.size());
        for (auto& it : graph) {
            keys.push_back(it.first);
        }
        for (auto node : keys) {
            if (getMatch(node) == NullVertex) {
                dfSearch(node);
            }
        }
    }
    return match;
}

void MinIndexSelection::addSearch(SearchSignature cols) {
    if (!cols.empty()) {
        spatialSearches.push_back(cols);  // stats
        searches.insert(SearchSignature::getFixed(cols));
    }
}

const std::vector<SearchSignature>& MinIndexSelection::getAllSpatialSearches() const {
    return spatialSearches;
}

void MinIndexSelection::solve() {
    // map the keys in the key set to lexicographical order
    if (searches.empty()) {
        return;
    }

    // discharge multiple inequalities
    removeExtraInequalities();

    // map the signatures of each search to a unique index for the matching problem
    AttributeIndex currentIndex = 1;
    for (SearchSignature s : searches) {
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
        for (auto itt : searches) {
            if (search == itt) {
                continue;
            }

            if (search < itt) {
                matching.addEdge(signatureToIndexA[search], signatureToIndexB[itt]);
            }
        }
    }

    // Perform the Hopcroft-Karp on the graph and receive matchings (mapped A->B and B->A)
    // Assume: alg.calculate is not called on an empty graph
    assert(!searches.empty());
    const MaxMatching::Matchings& matchings = matching.solve();

    // Extract the chains given the nodes and matchings
    ChainOrderMap chains = getChainsFromMatching(matchings, searches);

    // Should never get no chains back as we never call calculate on an empty graph
    assert(!chains.empty());
    for (const auto& chain : chains) {
        std::vector<uint32_t> ids;

        SearchSignature initDelta = *(chain.begin());
        insertIndex(ids, initDelta);

        // build the lex-order
        for (auto iit = chain.begin(); next(iit) != chain.end(); ++iit) {
            SearchSignature delta = SearchSignature::getDelta(*next(iit), *iit);
            insertIndex(ids, delta);
        }

        assert(!ids.empty());
        orders.push_back(ids);
    }

    // Validate the lex-order
    for (auto chain : chains) {
        for (auto search : chain) {
            int idx = map(search);
            size_t l = card(search);

            SearchSignature k(search.arity());
            for (size_t i = 0; i < l; i++) {
                k[orders[idx][i]] = AttributeConstraint::Equal;
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
        if (std::find(chain.begin(), chain.end(), start) == chain.end()) {
            chain.push_back(start);
        }

        if (mit == match.end()) {
            std::reverse(chain.begin(), chain.end());
            return chain;
        }

        SearchSignature a = indexToSignature.at(mit->second);
        if (std::find(chain.begin(), chain.end(), a) == chain.end()) {
            chain.push_back(a);
        }
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
            Chain a;
            a.push_back(node);
            chainToOrder.push_back(a);
            return chainToOrder;
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
    return chainToOrder;
}

void MinIndexSelection::updateSearch(SearchSignature oldSearch, SearchSignature newSearch) {
    auto delta = SearchSignature::getDelta(oldSearch, newSearch);
    for (size_t i = 0; i < delta.arity(); ++i) {
        if (delta[i] == AttributeConstraint::Inequal) {
            dischargedMap[oldSearch].insert(i);
        }
    }

    for (auto& chain : chainToOrder) {
        for (auto& search : chain) {
            if (search == oldSearch) {
                search = newSearch;
            }
        }
    }
}

void MinIndexSelection::removeExtraInequalities() {
    for (auto oldSearch : searches) {
        auto newSearch = oldSearch;
        bool seenInequality = false;
        for (size_t i = 0; i < oldSearch.arity(); ++i) {
            if (oldSearch[i] == AttributeConstraint::Inequal) {
                if (seenInequality) {
                    newSearch[i] = AttributeConstraint::None;
                } else {
                    seenInequality = true;
                }
            }
        }
        updateSearch(oldSearch, newSearch);
    }
}

MinIndexSelection::AttributeSet MinIndexSelection::getAttributesToDischarge(
        const SearchSignature& s, const Relation& rel) {
    // by default we have all attributes w/inequalities discharged
    AttributeSet allInequalities;
    for (size_t i = 0; i < s.arity(); ++i) {
        if (s[i] == AttributeConstraint::Inequal) {
            allInequalities.insert(i);
        }
    }

    // nothing discharge if we are using an rtree
    if (rel.getRepresentation() == RelationRepresentation::RTREE ||
            Global::config().get("default-datastructure") == "rtree") {
        return {};
    }

    // if we don't have a btree then we don't retain any inequalities
    if (rel.getRepresentation() != RelationRepresentation::BTREE &&
            rel.getRepresentation() != RelationRepresentation::DEFAULT) {
        return allInequalities;
    }

    // do not support indexed inequalities with provenance
    if (Global::config().has("provenance")) {
        return allInequalities;
    }

    // if we are in the interpreter then we only permit signed inequalities
    AttributeSet inequalitiesNotSigned;
    for (size_t i = 0; i < s.arity(); ++i) {
        if (s[i] == AttributeConstraint::Inequal && rel.getAttributeTypes()[i][0] != 'i') {
            inequalitiesNotSigned.insert(i);
        }
    }
    if (!Global::config().has("compile") && !Global::config().has("dl-program") &&
            !Global::config().has("generate") && !Global::config().has("swig")) {
        return inequalitiesNotSigned;
    }

    return dischargedMap[s];
}

void IndexAnalysis::run(const TranslationUnit& translationUnit) {
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
    visitDepthFirst(translationUnit.getProgram(), [&](const Node& node) {
        if (const auto* indexSearch = dynamic_cast<const IndexOperation*>(&node)) {
            MinIndexSelection& indexes = getIndexes(indexSearch->getRelation());
            indexes.addSearch(getSearchSignature(indexSearch));
        } else if (const auto* exists = dynamic_cast<const ExistenceCheck*>(&node)) {
            MinIndexSelection& indexes = getIndexes(exists->getRelation());
            indexes.addSearch(getSearchSignature(exists));
        } else if (const auto* provExists = dynamic_cast<const ProvenanceExistenceCheck*>(&node)) {
            MinIndexSelection& indexes = getIndexes(provExists->getRelation());
            indexes.addSearch(getSearchSignature(provExists));
        } else if (const auto* ramRel = dynamic_cast<const Relation*>(&node)) {
            MinIndexSelection& indexes = getIndexes(*ramRel);
            indexes.addSearch(getSearchSignature(ramRel));
        }
    });

    // A swap happen between rel A and rel B indicates A should include all indices of B, vice versa.
    visitDepthFirst(translationUnit.getProgram(), [&](const Swap& swap) {
        // Note: this naive approach will not work if there exists chain or cyclic swapping.
        // e.g.  swap(relA, relB) swap(relB, relC) swap(relC, relA)
        // One need to keep merging the search set until a fixed point where no more index is introduced
        // in any of the relation in a complete iteration.
        //
        // Currently RAM does not have such situation.
        const Relation& relA = swap.getFirstRelation();
        const Relation& relB = swap.getSecondRelation();

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

MinIndexSelection& IndexAnalysis::getIndexes(const Relation& rel) {
    auto pos = minIndexCover.find(&rel);
    if (pos != minIndexCover.end()) {
        return pos->second;
    } else {
        auto ret = minIndexCover.insert(std::make_pair(&rel, MinIndexSelection()));
        assert(ret.second);
        return ret.first->second;
    }
}

void IndexAnalysis::print(std::ostream& os) const {
    for (auto& cur : minIndexCover) {
        const Relation& rel = *cur.first;
        const MinIndexSelection& indexes = cur.second;
        const std::string& relName = rel.getName();

        /* Print searches */
        os << "Relation " << relName << "\n";
        os << "\tNumber of Searches: " << indexes.getSearches().size() << "\n";

        /* print searches */
        for (auto& search : indexes.getSearches()) {
            os << "\t\t";
            os << search;
            os << "\n";
        }

        /* print chains */
        for (auto& chain : indexes.getAllChains()) {
            os << join(chain, "-->") << "\n";
        }
        os << "\n";

        os << "\tNumber of Indexes: " << indexes.getAllOrders().size() << "\n";
        for (auto& order : indexes.getAllOrders()) {
            os << "\t\t";
            os << join(order, "<") << "\n";
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
        if (!isUndefValue(*cur)) {
            keys[i] = AttributeConstraint::Equal;
        }
    }
    return keys;
}

template <typename Seq>
SearchSignature searchSignature(size_t arity, Seq const& xs) {
    return searchSignature(arity, xs.begin(), xs.end());
}
}  // namespace

SearchSignature IndexAnalysis::getSearchSignature(const IndexOperation* search) const {
    size_t arity = search->getRelation().getArity();

    auto lower = search->getRangePattern().first;
    auto upper = search->getRangePattern().second;
    SearchSignature keys(arity);
    for (size_t i = 0; i < arity; ++i) {
        // if both bounds are undefined
        if (isUndefValue(lower[i]) && isUndefValue(upper[i])) {
            keys[i] = AttributeConstraint::None;
            // if bounds are equal we have an equality
        } else if (*lower[i] == *upper[i]) {
            keys[i] = AttributeConstraint::Equal;
        } else if (!isUndefValue(lower[i]) && !isUndefValue(upper[i])) {
            keys[i] = AttributeConstraint::Inequal;
        } else if (!isUndefValue(lower[i]) && isUndefValue(upper[i])) {
            keys[i] = AttributeConstraint::Lower;
        } else if (isUndefValue(lower[i]) && !isUndefValue(upper[i])) {
            keys[i] = AttributeConstraint::Upper;
        }
    }
    return keys;
}

SearchSignature IndexAnalysis::getSearchSignature(const ProvenanceExistenceCheck* provExistCheck) const {
    const auto values = provExistCheck->getValues();
    auto auxiliaryArity = provExistCheck->getRelation().getAuxiliaryArity();

    SearchSignature keys(values.size());

    // all payload attributes should be equalities
    for (size_t i = 0; i < values.size() - auxiliaryArity; i++) {
        if (!isUndefValue(values[i])) {
            keys[i] = AttributeConstraint::Equal;
        }
    }

    // all auxiliary attributes should be free
    for (size_t i = values.size() - auxiliaryArity; i < values.size(); i++) {
        keys[i] = AttributeConstraint::None;
    }

    return keys;
}

SearchSignature IndexAnalysis::getSearchSignature(const ExistenceCheck* existCheck) const {
    return searchSignature(existCheck->getRelation().getArity(), existCheck->getValues());
}

SearchSignature IndexAnalysis::getSearchSignature(const Relation* ramRel) const {
    return SearchSignature::getFullSearchSignature(ramRel->getArity());
}

bool IndexAnalysis::isTotalSignature(const AbstractExistenceCheck* existCheck) const {
    for (const auto& cur : existCheck->getValues()) {
        if (isUndefValue(cur)) {
            return false;
        }
    }
    return true;
}

}  // namespace souffle::ram::analysis
