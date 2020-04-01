/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

#include "SynthesiserRelation.h"
#include "Global.h"
#include "RelationTag.h"
#include "Util.h"
#include <algorithm>
#include <cassert>
#include <map>
#include <numeric>
#include <set>

// #define BLOOM_F 1

namespace souffle {

std::unique_ptr<SynthesiserRelation> SynthesiserRelation::getSynthesiserRelation(
        const RamRelation& ramRel, const MinIndexSelection& indexSet, bool isProvenance) {
    SynthesiserRelation* rel;

    // Handle the qualifier in souffle code
    if (isProvenance) {
        rel = new SynthesiserDirectRelation(ramRel, indexSet, isProvenance);
    } else if (ramRel.isNullary()) {
        rel = new SynthesiserNullaryRelation(ramRel, indexSet, isProvenance);
    } else if (ramRel.getRepresentation() == RelationRepresentation::BTREE) {
        rel = new SynthesiserDirectRelation(ramRel, indexSet, isProvenance);
    } else if (ramRel.getRepresentation() == RelationRepresentation::RTREE) {
        rel = new SynthesiserRtreeRelation(ramRel, indexSet, isProvenance);
    } else if (ramRel.getRepresentation() == RelationRepresentation::BRIE) {
        rel = new SynthesiserBrieRelation(ramRel, indexSet, isProvenance);
    } else if (ramRel.getRepresentation() == RelationRepresentation::EQREL) {
        rel = new SynthesiserEqrelRelation(ramRel, indexSet, isProvenance);
    } else if (ramRel.getRepresentation() == RelationRepresentation::INFO) {
        rel = new SynthesiserInfoRelation(ramRel, indexSet, isProvenance);
    } else {
	   std::string ds = Global::config().get("default-datastructure");
	   if (!Global::config().has("default-datastructure") || ds == "btree") {
               // Handle the data structure command line flag
	       if(ramRel.getArity() > 6) {
		  rel = new SynthesiserIndirectRelation(ramRel, indexSet, isProvenance);
	       } else {
		  rel = new SynthesiserDirectRelation(ramRel, indexSet, isProvenance);
	       }
	   } else {
	       if (ds == "rtree") {
		  rel = new SynthesiserRtreeRelation(ramRel, indexSet, isProvenance);
	       } else if (ds == "brie") {
		  rel = new SynthesiserBrieRelation(ramRel, indexSet, isProvenance);
	       } else {
		  assert(false && "wrong data-structure");
	       }
	   }
    }
	       
   assert(rel != nullptr && "relation type not specified");

    // generate index set
    rel->computeIndices();

    return std::unique_ptr<SynthesiserRelation>(rel);
}

// -------- Info Relation --------

/** Generate index set for a info relation, which should be empty */
void SynthesiserInfoRelation::computeIndices() {
    computedIndices = {};
}

/** Generate type name of a info relation */
std::string SynthesiserInfoRelation::getTypeName() {
    return "t_info<" + std::to_string(getArity()) + ">";
}

/** Generate type struct of a info relation, which is empty,
 * the actual implementation is in CompiledSouffle.h */
void SynthesiserInfoRelation::generateTypeStruct(std::ostream&) {
    return;
}

// -------- Nullary Relation --------

/** Generate index set for a nullary relation, which should be empty */
void SynthesiserNullaryRelation::computeIndices() {
    computedIndices = {};
}

/** Generate type name of a nullary relation */
std::string SynthesiserNullaryRelation::getTypeName() {
    return "t_nullaries";
}

/** Generate type struct of a nullary relation, which is empty,
 * the actual implementation is in CompiledSouffle.h */
void SynthesiserNullaryRelation::generateTypeStruct(std::ostream&) {
    return;
}

// -------- Direct Indexed B-Tree Relation --------

/** Generate index set for a direct indexed relation */
void SynthesiserDirectRelation::computeIndices() {
    // Generate and set indices
    MinIndexSelection::OrderCollection inds = indices.getAllOrders();

    // generate a full index if no indices exist
    if (inds.empty()) {
        MinIndexSelection::LexOrder fullInd(getArity());
        std::iota(fullInd.begin(), fullInd.end(), 0);
        inds.push_back(fullInd);
    }

    size_t index_nr = 0;
    // expand all search orders to be full
    for (auto& ind : inds) {
        // use a set as a cache for fast lookup
        std::set<int> curIndexElems(ind.begin(), ind.end());

        // If this relation is used with provenance,
        // we must expand all search orders to be full indices,
        // since weak/strong comparators and updaters need this,
        // and also add provenance annotations to the indices
        if (isProvenance) {
            // expand index to be full
            for (size_t i = 0; i < getArity() - relation.getAuxiliaryArity(); i++) {
                if (curIndexElems.find(i) == curIndexElems.end()) {
                    ind.push_back(i);
                }
            }

            if (Global::config().get("provenance") == "subtreeHeights") {
                // TODO (sarah): assumption index is used exclusively for provenance in case a height
                // parameter occurs in order of columns before regular columns (at least only in this case it
                // needs to be copied) -- verify this!!

                auto firstProvenanceColumn = (getArity() - relation.getAuxiliaryArity());

                // position of last non provenance column
                auto nonProv = std::find_if(ind.rbegin(), ind.rend(),
                        [firstProvenanceColumn](size_t i) { return i < firstProvenanceColumn; });
                auto indNonProv = std::distance(nonProv, ind.rend());

                // position of first height column
                auto prov = std::find_if(ind.begin(), ind.end(),
                        [firstProvenanceColumn](size_t i) { return i >= firstProvenanceColumn + 1; });
                auto indProv = std::distance(ind.begin(), prov);

                if (indNonProv > indProv) {
                    provenanceIndexNumbers.insert(index_nr);
                } else {
                    // index was not added for provenance and can therefore be used as master index
                    masterIndex = index_nr;
                }

                // add provenance annotations to the index but in reverse order
                // add height columns if not already contained
                for (size_t i = getArity() - relation.getAuxiliaryArity() + 1; i < getArity(); i++) {
                    if (curIndexElems.find(i) == curIndexElems.end()) {
                        ind.push_back(i);
                    }
                }

                // remove rule annotation if already in the index order
                if (curIndexElems.find(getArity() - relation.getAuxiliaryArity()) != curIndexElems.end()) {
                    ind.erase(std::find(ind.begin(), ind.end(), getArity() - relation.getAuxiliaryArity()));
                }
                // add rule as last parameter
                ind.push_back(getArity() - relation.getAuxiliaryArity());
            } else {
                // remove any provenance annotations already in the index order
                if (curIndexElems.find(getArity() - relation.getAuxiliaryArity() + 1) !=
                        curIndexElems.end()) {
                    ind.erase(
                            std::find(ind.begin(), ind.end(), getArity() - relation.getAuxiliaryArity() + 1));
                }

                if (curIndexElems.find(getArity() - relation.getAuxiliaryArity()) != curIndexElems.end()) {
                    ind.erase(std::find(ind.begin(), ind.end(), getArity() - relation.getAuxiliaryArity()));
                }

                // add provenance annotations to the index, but in reverse order
                ind.push_back(getArity() - relation.getAuxiliaryArity() + 1);
                ind.push_back(getArity() - relation.getAuxiliaryArity());
                masterIndex = 0;
            }

        } else if (ind.size() < getArity()) {
            // expand index to be full
            for (size_t i = 0; i < getArity(); i++) {
                if (curIndexElems.find(i) == curIndexElems.end()) {
                    ind.push_back(i);
                }
            }
        }

        index_nr++;
    }

    if (!isProvenance) {
        masterIndex = 0;
    }

    assert(masterIndex < inds.size());

    computedIndices = inds;
}

/** Generate type name of a direct indexed relation */
std::string SynthesiserDirectRelation::getTypeName() {
    std::stringstream res;
    res << "t_btree_" << getArity();

    for (auto& ind : getIndices()) {
        res << "__" << join(ind, "_");
    }

    for (auto& search : getMinIndexSelection().getSearches()) {
        res << "__" << search;
    }

    return res.str();
}

/** Generate type struct of a direct indexed relation */
void SynthesiserDirectRelation::generateTypeStruct(std::ostream& out) {
    size_t arity = getArity();
    size_t auxiliaryArity = relation.getAuxiliaryArity();
    const auto& inds = getIndices();
    size_t numIndexes = inds.size();
    std::map<MinIndexSelection::LexOrder, int> indexToNumMap;

    // struct definition
    out << "struct " << getTypeName() << " {\n";

    // stored tuple type
    out << "using t_tuple = Tuple<RamDomain, " << arity << ">;\n";

    // generate an updater class for provenance
    if (isProvenance) {
        out << "struct updater_" << getTypeName() << " {\n";
        out << "void update(t_tuple& old_t, const t_tuple& new_t) {\n";

        for (size_t i = arity - auxiliaryArity; i < arity; i++) {
            out << "old_t[" << i << "] = new_t[" << i << "];\n";
        }

        out << "}\n";
        out << "};\n";
    }

    // generate the btree type for each relation
    for (size_t i = 0; i < inds.size(); i++) {
        auto& ind = inds[i];

        if (i < getMinIndexSelection().getAllOrders().size()) {
            indexToNumMap[getMinIndexSelection().getAllOrders()[i]] = i;
        }

        // for provenance, all indices must be full so we use btree_set
        // also strong/weak comparators and updater methods
        if (isProvenance) {
            if (provenanceIndexNumbers.find(i) == provenanceIndexNumbers.end()) {  // index for bottom up
                                                                                   // phase
                out << "using t_ind_" << i << " = btree_set<t_tuple, index_utils::comparator<" << join(ind);
                out << ">, std::allocator<t_tuple>, 256, typename "
                       "souffle::detail::default_strategy<t_tuple>::type, index_utils::comparator<";
                out << join(ind.begin(), ind.end() - auxiliaryArity) << ">, updater_" << getTypeName()
                    << ">;\n";
            } else {  // index for top down phase
                out << "using t_ind_" << i << " = btree_set<t_tuple, index_utils::comparator<" << join(ind);
                out << ">, std::allocator<t_tuple>, 256, typename "
                       "souffle::detail::default_strategy<t_tuple>::type, index_utils::comparator<";
                out << join(ind.begin(), ind.end()) << ">, updater_" << getTypeName() << ">;\n";
            }
            // without provenance, some indices may be not full, so we use btree_multiset for those
        } else {
            if (ind.size() == arity) {
                out << "using t_ind_" << i << " = btree_set<t_tuple, index_utils::comparator<" << join(ind)
                    << ">>;\n";
            } else {
                out << "using t_ind_" << i << " = btree_multiset<t_tuple, index_utils::comparator<"
                    << join(ind) << ">>;\n";
            }
        }
        out << "t_ind_" << i << " ind_" << i << ";\n";
    }

    // typedef master index iterator to be struct iterator
    out << "using iterator = t_ind_" << masterIndex << "::iterator;\n";

    // create a struct storing hints for each btree
    out << "struct context {\n";
    for (size_t i = 0; i < numIndexes; i++) {
        out << "t_ind_" << i << "::operation_hints hints_" << i << ";\n";
    }
    out << "};\n";
    out << "context createContext() { return context(); }\n";

    // insert methods
    out << "bool insert(const t_tuple& t) {\n";
    out << "context h;\n";
    out << "return insert(t, h);\n";
    out << "}\n";  // end of insert(t_tuple&)

    out << "bool insert(const t_tuple& t, context& h) {\n";
    out << "if (ind_" << masterIndex << ".insert(t, h.hints_" << masterIndex << ")) {\n";
    for (size_t i = 0; i < numIndexes; i++) {
        if (i != masterIndex && provenanceIndexNumbers.find(i) == provenanceIndexNumbers.end()) {
            out << "ind_" << i << ".insert(t, h.hints_" << i << ");\n";
        }
    }
    out << "return true;\n";
    out << "} else return false;\n";
    out << "}\n";  // end of insert(t_tuple&, context&)

    out << "bool insert(const RamDomain* ramDomain) {\n";
    out << "RamDomain data[" << arity << "];\n";
    out << "std::copy(ramDomain, ramDomain + " << arity << ", data);\n";
    out << "const t_tuple& tuple = reinterpret_cast<const t_tuple&>(data);\n";
    out << "context h;\n";
    out << "return insert(tuple, h);\n";
    out << "}\n";  // end of insert(RamDomain*)

    std::vector<std::string> decls;
    std::vector<std::string> params;
    for (size_t i = 0; i < arity; i++) {
        decls.push_back("RamDomain a" + std::to_string(i));
        params.push_back("a" + std::to_string(i));
    }
    out << "bool insert(" << join(decls, ",") << ") {\n";
    out << "RamDomain data[" << arity << "] = {" << join(params, ",") << "};\n";
    out << "return insert(data);\n";
    out << "}\n";  // end of insert(RamDomain x1, RamDomain x2, ...)

    // contains methods
    out << "bool contains(const t_tuple& t, context& h) const {\n";
    out << "return ind_" << masterIndex << ".contains(t, h.hints_" << masterIndex << ");\n";
    out << "}\n";

    out << "bool contains(const t_tuple& t) const {\n";
    out << "context h;\n";
    out << "return contains(t, h);\n";
    out << "}\n";

    // size method
    out << "std::size_t size() const {\n";
    out << "return ind_" << masterIndex << ".size();\n";
    out << "}\n";

    // find methods
    out << "iterator find(const t_tuple& t, context& h) const {\n";
    out << "return ind_" << masterIndex << ".find(t, h.hints_" << masterIndex << ");\n";
    out << "}\n";

    out << "iterator find(const t_tuple& t) const {\n";
    out << "context h;\n";
    out << "return find(t, h);\n";
    out << "}\n";

    // empty equalRange method
    out << "range<iterator> equalRange_0(const t_tuple& t, context& h) const {\n";
    out << "return range<iterator>(ind_" << masterIndex << ".begin(),ind_" << masterIndex << ".end());\n";
    out << "}\n";

    out << "range<iterator> equalRange_0(const t_tuple& t) const {\n";
    out << "return range<iterator>(ind_" << masterIndex << ".begin(),ind_" << masterIndex << ".end());\n";
    out << "}\n";

    // equalRange methods for each pattern which is used to search this relation
    for (int64_t search : getMinIndexSelection().getSearches()) {
        auto& lexOrder = getMinIndexSelection().getLexOrder(search);
        size_t indNum = indexToNumMap[lexOrder];

        out << "range<t_ind_" << indNum << "::iterator> equalRange_" << search;
        out << "(const t_tuple& t, context& h) const {\n";

        // count size of search pattern
        size_t indSize = 0;
        for (size_t column = 0; column < arity; column++) {
            if (((search >> column) & 1) != 0) {
                indSize++;
            }
        }

        // use the more efficient find() method if the search pattern is full
        if (indSize == arity) {
            out << "auto pos = ind_" << indNum << ".find(t, h.hints_" << indNum << ");\n";
            out << "auto fin = ind_" << indNum << ".end();\n";
            out << "if (pos != fin) {fin = pos; ++fin;}\n";
            out << "return make_range(pos, fin);\n";
        } else {
            // generate lower and upper bounds for range search
            out << "t_tuple low(t); t_tuple high(t);\n";
            // check which indices to pad out
            for (size_t column = 0; column < arity; column++) {
                // if bit number column is set
                if (((search >> column) & 1) == 0) {
                    out << "low[" << column << "] = MIN_RAM_SIGNED;\n";
                    out << "high[" << column << "] = MAX_RAM_SIGNED;\n";
                }
            }
            out << "return make_range(ind_" << indNum << ".lower_bound(low, h.hints_" << indNum << "), ind_"
                << indNum << ".upper_bound(high, h.hints_" << indNum << "));\n";
        }
        out << "}\n";

        out << "range<t_ind_" << indNum << "::iterator> equalRange_" << search;
        out << "(const t_tuple& t) const {\n";
        out << "context h;\n";
        out << "return equalRange_" << search << "(t, h);\n";
        out << "}\n";
    }

    // empty method
    out << "bool empty() const {\n";
    out << "return ind_" << masterIndex << ".empty();\n";
    out << "}\n";

    // partition method for parallelism
    out << "std::vector<range<iterator>> partition() const {\n";
    out << "return ind_" << masterIndex << ".getChunks(400);\n";
    out << "}\n";

    // purge method
    out << "void purge() {\n";
    for (size_t i = 0; i < numIndexes; i++) {
        out << "ind_" << i << ".clear();\n";
    }
    out << "}\n";

    // begin and end iterators
    out << "iterator begin() const {\n";
    out << "return ind_" << masterIndex << ".begin();\n";
    out << "}\n";

    out << "iterator end() const {\n";
    out << "return ind_" << masterIndex << ".end();\n";
    out << "}\n";

    // copyIndex method
    if (!provenanceIndexNumbers.empty()) {
        out << "void copyIndex() {\n";
        out << "for (auto const &cur : ind_" << masterIndex << ") {\n";
        for (auto const i : provenanceIndexNumbers) {
            out << "ind_" << i << ".insert(cur);\n";
        }
        out << "}\n";
        out << "}\n";
    }

    // printHintStatistics method
    out << "void printHintStatistics(std::ostream& o, const std::string prefix) const {\n";
    for (size_t i = 0; i < numIndexes; i++) {
        out << "const auto& stats_" << i << " = ind_" << i << ".getHintStatistics();\n";
        out << "o << prefix << \"arity " << getArity() << " direct b-tree index " << inds[i]
            << ": (hits/misses/total)\\n\";\n";
        out << "o << prefix << \"Insert: \" << stats_" << i << ".inserts.getHits() << \"/\" << stats_" << i
            << ".inserts.getMisses() << \"/\" << stats_" << i << ".inserts.getAccesses() << \"\\n\";\n";
        out << "o << prefix << \"Contains: \" << stats_" << i << ".contains.getHits() << \"/\" << stats_" << i
            << ".contains.getMisses() << \"/\" << stats_" << i << ".contains.getAccesses() << \"\\n\";\n";
        out << "o << prefix << \"Lower-bound: \" << stats_" << i
            << ".lower_bound.getHits() << \"/\" << stats_" << i
            << ".lower_bound.getMisses() << \"/\" << stats_" << i
            << ".lower_bound.getAccesses() << \"\\n\";\n";
        out << "o << prefix << \"Upper-bound: \" << stats_" << i
            << ".upper_bound.getHits() << \"/\" << stats_" << i
            << ".upper_bound.getMisses() << \"/\" << stats_" << i
            << ".upper_bound.getAccesses() << \"\\n\";\n";
    }
    out << "}\n";

    // end struct
    out << "};\n";
}

// -------- Indirect Indexed B-Tree Relation --------

/** Generate index set for a indirect indexed relation */
void SynthesiserIndirectRelation::computeIndices() {
    assert(!isProvenance);

    // Generate and set indices
    MinIndexSelection::OrderCollection inds = indices.getAllOrders();

    // generate a full index if no indices exist
    if (inds.empty()) {
        MinIndexSelection::LexOrder fullInd(getArity());
        std::iota(fullInd.begin(), fullInd.end(), 0);
        inds.push_back(fullInd);
        masterIndex = 0;
    }

    // Expand the first index to be a full index if no full inds exist
    bool fullExists = false;
    // check for full index
    for (size_t i = 0; i < inds.size(); i++) {
        auto& ind = inds[i];
        if (ind.size() == getArity()) {
            fullExists = true;
            if (masterIndex == (size_t)-1) {
                masterIndex = i;
            }
        }
    }

    // expand the first ind to be full, it is guaranteed that at least one index exists
    if (!fullExists) {
        std::set<int> curIndexElems(inds[0].begin(), inds[0].end());

        // expand index to be full
        for (size_t i = 0; i < getArity(); i++) {
            if (curIndexElems.find(i) == curIndexElems.end()) {
                inds[0].push_back(i);
            }
        }

        masterIndex = 0;
    }

    computedIndices = inds;
}

/** Generate type name of a indirect indexed relation */
std::string SynthesiserIndirectRelation::getTypeName() {
    std::stringstream res;
    res << "t_btree_" << getArity();

    for (auto& ind : getIndices()) {
        res << "__" << join(ind, "_");
    }

    for (auto& search : getMinIndexSelection().getSearches()) {
        res << "__" << search;
    }

    return res.str();
}

/** Generate type struct of a indirect indexed relation */
void SynthesiserIndirectRelation::generateTypeStruct(std::ostream& out) {
    size_t arity = getArity();
    const auto& inds = getIndices();
    size_t numIndexes = inds.size();
    std::map<MinIndexSelection::LexOrder, int> indexToNumMap;

    // struct definition
    out << "struct " << getTypeName() << " {\n";

    // stored tuple type
    out << "using t_tuple = Tuple<RamDomain, " << arity << ">;\n";

    // table and lock required for storing actual data for indirect indices
    out << "Table<t_tuple> dataTable;\n";
    out << "Lock insert_lock;\n";

    // btree types
    for (size_t i = 0; i < inds.size(); i++) {
        auto ind = inds[i];

        if (i < getMinIndexSelection().getAllOrders().size()) {
            indexToNumMap[getMinIndexSelection().getAllOrders()[i]] = i;
        }

        if (ind.size() == arity) {
            out << "using t_ind_" << i
                << " = btree_set<const t_tuple*, index_utils::deref_compare<typename "
                   "index_utils::comparator<"
                << join(ind) << ">>>;\n";
        } else {
            out << "using t_ind_" << i
                << " = btree_multiset<const t_tuple*, index_utils::deref_compare<typename "
                   "index_utils::comparator<"
                << join(ind) << ">>>;\n";
        }

        out << "t_ind_" << i << " ind_" << i << ";\n";
    }

    // typedef deref iterators
    for (size_t i = 0; i < numIndexes; i++) {
        out << "using iterator_" << i << " = IterDerefWrapper<typename t_ind_" << i << "::iterator>;\n";
    }
    out << "using iterator = iterator_" << masterIndex << ";\n";

    // Create a struct storing the context hints for each index
    out << "struct context {\n";
    for (size_t i = 0; i < numIndexes; i++) {
        out << "t_ind_" << i << "::operation_hints hints_" << i << ";\n";
    }
    out << "};\n";
    out << "context createContext() { return context(); }\n";

    // insert methods
    out << "bool insert(const t_tuple& t) {\n";
    out << "context h;\n";
    out << "return insert(t, h);\n";
    out << "}\n";

    out << "bool insert(const t_tuple& t, context& h) {\n";
    out << "const t_tuple* masterCopy = nullptr;\n";
    out << "{\n";
    out << "auto lease = insert_lock.acquire();\n";
    out << "if (contains(t, h)) return false;\n";
    out << "masterCopy = &dataTable.insert(t);\n";
    out << "ind_" << masterIndex << ".insert(masterCopy, h.hints_" << masterIndex << ");\n";
    out << "}\n";
    for (size_t i = 0; i < numIndexes; i++) {
        if (i != masterIndex) {
            out << "ind_" << i << ".insert(masterCopy, h.hints_" << i << ");\n";
        }
    }
    out << "return true;\n";
    out << "}\n";

    out << "bool insert(const RamDomain* ramDomain) {\n";
    out << "RamDomain data[" << arity << "];\n";
    out << "std::copy(ramDomain, ramDomain + " << arity << ", data);\n";
    out << "const t_tuple& tuple = reinterpret_cast<const t_tuple&>(data);\n";
    out << "context h;\n";
    out << "return insert(tuple, h);\n";
    out << "}\n";  // end of insert(RamDomain*)

    std::vector<std::string> decls;
    std::vector<std::string> params;
    for (size_t i = 0; i < arity; i++) {
        decls.push_back("RamDomain a" + std::to_string(i));
        params.push_back("a" + std::to_string(i));
    }
    out << "bool insert(" << join(decls, ",") << ") {\n";
    out << "RamDomain data[" << arity << "] = {" << join(params, ",") << "};\n";
    out << "return insert(data);\n";
    out << "}\n";  // end of insert(RamDomain x1, RamDomain x2, ...)

    // contains methods
    out << "bool contains(const t_tuple& t, context& h) const {\n";
    out << "return ind_" << masterIndex << ".contains(&t, h.hints_" << masterIndex << ");\n";
    out << "}\n";

    out << "bool contains(const t_tuple& t) const {\n";
    out << "context h;\n";
    out << "return contains(t, h);\n";
    out << "}\n";

    // size method
    out << "std::size_t size() const {\n";
    out << "return ind_" << masterIndex << ".size();\n";
    out << "}\n";

    // find methods
    out << "iterator find(const t_tuple& t, context& h) const {\n";
    out << "return ind_" << masterIndex << ".find(&t, h.hints_" << masterIndex << ");\n";
    out << "}\n";

    out << "iterator find(const t_tuple& t) const {\n";
    out << "context h;\n";
    out << "return find(t, h);\n";
    out << "}\n";

    // empty equalRange method
    out << "range<iterator> equalRange_0(const t_tuple& t, context& h) const {\n";
    out << "return range<iterator>(ind_" << masterIndex << ".begin(),ind_" << masterIndex << ".end());\n";
    out << "}\n";

    out << "range<iterator> equalRange_0(const t_tuple& t) const {\n";
    out << "return range<iterator>(ind_" << masterIndex << ".begin(),ind_" << masterIndex << ".end());\n";
    out << "}\n";

    for (int64_t search : getMinIndexSelection().getSearches()) {
        auto& lexOrder = getMinIndexSelection().getLexOrder(search);
        size_t indNum = indexToNumMap[lexOrder];

        out << "range<iterator_" << indNum << "> equalRange_" << search;
        out << "(const t_tuple& t, context& h) const {\n";

        // count size of search pattern
        size_t indSize = 0;
        for (size_t column = 0; column < arity; column++) {
            if (((search >> column) & 1) != 0) {
                indSize++;
            }
        }

        // use the more efficient find() method for full range search
        if (indSize == arity) {
            out << "auto pos = find(t, h);\n";
            out << "auto fin = end();\n";
            out << "if (pos != fin) {fin = pos; ++fin;}\n";
            out << "return make_range(pos, fin);\n";
        } else {
            out << "t_tuple low(t); t_tuple high(t);\n";
            // check which indices to pad out
            for (size_t column = 0; column < arity; column++) {
                // if bit number column is set
                if (((search >> column) & 1) == 0) {
                    out << "low[" << column << "] = MIN_RAM_SIGNED;\n";
                    out << "high[" << column << "] = MAX_RAM_SIGNED;\n";
                }
            }
            out << "return range<iterator_" << indNum << ">(ind_" << indNum << ".lower_bound(&low, h.hints_"
                << indNum << "), ind_" << indNum << ".upper_bound(&high, h.hints_" << indNum << "));\n";
        }
        out << "}\n";

        out << "range<iterator_" << indNum << "> equalRange_" << search;
        out << "(const t_tuple& t) const {\n";
        out << "context h; return equalRange_" << search << "(t, h);\n";
        out << "}\n";
    }

    // empty method
    out << "bool empty() const {\n";
    out << "return ind_" << masterIndex << ".empty();\n";
    out << "}\n";

    // partition method
    out << "std::vector<range<iterator>> partition() const {\n";
    out << "std::vector<range<iterator>> res;\n";
    out << "for (const auto& cur : ind_" << masterIndex << ".getChunks(400)) {\n";
    out << "    res.push_back(make_range(derefIter(cur.begin()), derefIter(cur.end())));\n";
    out << "}\n";
    out << "return res;\n";
    out << "}\n";

    // purge method
    out << "void purge() {\n";
    for (size_t i = 0; i < numIndexes; i++) {
        out << "ind_" << i << ".clear();\n";
    }
    out << "dataTable.clear();\n";
    out << "}\n";

    // begin and end iterators
    out << "iterator begin() const {\n";
    out << "return ind_" << masterIndex << ".begin();\n";
    out << "}\n";

    out << "iterator end() const {\n";
    out << "return ind_" << masterIndex << ".end();\n";
    out << "}\n";

    // printHintStatistics method
    out << "void printHintStatistics(std::ostream& o, const std::string prefix) const {\n";
    for (size_t i = 0; i < numIndexes; i++) {
        out << "const auto& stats_" << i << " = ind_" << i << ".getHintStatistics();\n";
        out << "o << prefix << \"arity " << arity << " indirect b-tree index " << inds[i]
            << ": (hits/misses/total)\\n\";\n";
        out << "o << prefix << \"Insert: \" << stats_" << i << ".inserts.getHits() << \"/\" << stats_" << i
            << ".inserts.getMisses() << \"/\" << stats_" << i << ".inserts.getAccesses() << \"\\n\";\n";
        out << "o << prefix << \"Contains: \" << stats_" << i << ".contains.getHits() << \"/\" << stats_" << i
            << ".contains.getMisses() << \"/\" << stats_" << i << ".contains.getAccesses() << \"\\n\";\n";
        out << "o << prefix << \"Lower-bound: \" << stats_" << i
            << ".lower_bound.getHits() << \"/\" << stats_" << i
            << ".lower_bound.getMisses() << \"/\" << stats_" << i
            << ".lower_bound.getAccesses() << \"\\n\";\n";
        out << "o << prefix << \"Upper-bound: \" << stats_" << i
            << ".upper_bound.getHits() << \"/\" << stats_" << i
            << ".upper_bound.getMisses() << \"/\" << stats_" << i
            << ".upper_bound.getAccesses() << \"\\n\";\n";
    }
    out << "}\n";

    // end struct
    out << "};\n";
}

// -------- Brie Relation --------

/** Generate index set for a brie relation */
void SynthesiserBrieRelation::computeIndices() {
    assert(!isProvenance && "bries cannot be used with provenance");

    // Generate and set indices
    MinIndexSelection::OrderCollection inds = indices.getAllOrders();

    // generate a full index if no indices exist
    if (inds.empty()) {
        MinIndexSelection::LexOrder fullInd(getArity());
        std::iota(fullInd.begin(), fullInd.end(), 0);
        inds.push_back(fullInd);
    }

    // expand all indexes to be full
    for (auto& ind : inds) {
        if (ind.size() != getArity()) {
            // use a set as a cache for fast lookup
            std::set<int> curIndexElems(ind.begin(), ind.end());

            // expand index to be full
            for (size_t i = 0; i < getArity(); i++) {
                if (curIndexElems.find(i) == curIndexElems.end()) {
                    ind.push_back(i);
                }
            }
        }

        assert(ind.size() == getArity());
    }
    masterIndex = 0;

    computedIndices = inds;
}

/** Generate type name of a brie relation */
std::string SynthesiserBrieRelation::getTypeName() {
    std::stringstream res;
    res << "t_brie_" << getArity();

    for (auto& ind : getIndices()) {
        res << "__" << join(ind, "_");
    }

    for (auto& search : getMinIndexSelection().getSearches()) {
        res << "__" << search;
    }

    return res.str();
}

/** Generate type struct of a brie relation */
void SynthesiserBrieRelation::generateTypeStruct(std::ostream& out) {
    size_t arity = getArity();
    const auto& inds = getIndices();
    size_t numIndexes = inds.size();
    std::map<MinIndexSelection::LexOrder, int> indexToNumMap;

    // struct definition
    out << "struct " << getTypeName() << " {\n";

    // define trie structures
    for (size_t i = 0; i < inds.size(); i++) {
        if (i < getMinIndexSelection().getAllOrders().size()) {
            indexToNumMap[getMinIndexSelection().getAllOrders()[i]] = i;
        }
        out << "using t_ind_" << i << " = Trie<" << inds[i].size() << ">;\n";
        out << "t_ind_" << i << " ind_" << i << ";\n";
    }
    out << "using t_tuple = t_ind_" << masterIndex << "::entry_type;\n";

    // generate auxiliary iterators that use orderOut
    for (size_t i = 0; i < numIndexes; i++) {
        // generate auxiliary iterators which orderOut
        out << "class iterator_" << i << " : public std::iterator<std::forward_iterator_tag, t_tuple> {\n";
        out << "    using nested_iterator = typename t_ind_" << i << "::iterator;\n";
        out << "    nested_iterator nested;\n";
        out << "    t_tuple value;\n";

        out << "public:\n";
        out << "    iterator_" << i << "() = default;\n";
        out << "    iterator_" << i << "(const nested_iterator& iter) : nested(iter), value(orderOut_" << i
            << "(*iter)) {}\n";
        out << "    iterator_" << i << "(const iterator_" << i << "& other) = default;\n";
        out << "    iterator_" << i << "& operator=(const iterator_" << i << "& other) = default;\n";

        out << "    bool operator==(const iterator_" << i << "& other) const {\n";
        out << "        return nested == other.nested;\n";
        out << "    }\n";

        out << "    bool operator!=(const iterator_" << i << "& other) const {\n";
        out << "        return !(*this == other);\n";
        out << "    }\n";

        out << "    const t_tuple& operator*() const {\n";
        out << "        return value;\n";
        out << "    }\n";

        out << "    const t_tuple* operator->() const {\n";
        out << "        return &value;\n";
        out << "    }\n";

        out << "    iterator_" << i << "& operator++() {\n";
        out << "        ++nested;\n";
        out << "        value = orderOut_" << i << "(*nested);\n";
        out << "        return *this;\n";
        out << "    }\n";
        out << "};\n";
    }
    out << "using iterator = iterator_" << masterIndex << ";\n";

    // hints struct
    out << "struct context {\n";
    for (size_t i = 0; i < numIndexes; i++) {
        out << "t_ind_" << i << "::op_context hints_" << i << ";\n";
    }
    out << "};\n";
    out << "context createContext() { return context(); }\n";

    // insert methods
    out << "bool insert(const t_tuple& t) {\n";
    out << "context h;\n";
    out << "return insert(t, h);\n";
    out << "}\n";

    out << "bool insert(const t_tuple& t, context& h) {\n";
    out << "if (ind_" << masterIndex << ".insert(orderIn_" << masterIndex << "(t), h.hints_" << masterIndex
        << ")) {\n";
    for (size_t i = 0; i < numIndexes; i++) {
        if (i != masterIndex) {
            out << "ind_" << i << ".insert(orderIn_" << i << "(t), h.hints_" << i << ");\n";
        }
    }
    out << "return true;\n";
    out << "} else return false;\n";
    out << "}\n";

    out << "bool insert(const RamDomain* ramDomain) {\n";
    out << "RamDomain data[" << arity << "];\n";
    out << "std::copy(ramDomain, ramDomain + " << arity << ", data);\n";
    out << "const t_tuple& tuple = reinterpret_cast<const t_tuple&>(data);\n";
    out << "context h;\n";
    out << "return insert(tuple, h);\n";
    out << "}\n";

    // insert method
    std::vector<std::string> decls;
    std::vector<std::string> params;
    for (size_t i = 0; i < arity; i++) {
        decls.push_back("RamDomain a" + std::to_string(i));
        params.push_back("a" + std::to_string(i));
    }
    out << "bool insert(" << join(decls, ",") << ") {\nRamDomain data[";
    out << arity << "] = {" << join(params, ",") << "};\n";
    out << "return insert(data);\n";
    out << "}\n";

    // contains methods
    out << "bool contains(const t_tuple& t, context& h) const {\n";
    out << "return ind_" << masterIndex << ".contains(orderIn_" << masterIndex << "(t), h.hints_"
        << masterIndex << ");\n";
    out << "}\n";

    out << "bool contains(const t_tuple& t) const {\n";
    out << "context h;\n";
    out << "return contains(t, h);\n";
    out << "}\n";

    // size method
    out << "std::size_t size() const {\n";
    out << "return ind_" << masterIndex << ".size();\n";
    out << "}\n";

    // find methods
    if (arity > 1) {
        out << "iterator find(const t_tuple& t, context& h) const {\n";
        out << "return ind_" << masterIndex << ".find(orderIn_" << masterIndex << "(t), h.hints_"
            << masterIndex << ");\n";
        out << "}\n";

        out << "iterator find(const t_tuple& t) const {\n";
        out << "context h;\n";
        out << "return find(t, h);\n";
        out << "}\n";
    }

    // empty equalRange method
    out << "range<iterator> equalRange_0(const t_tuple& t, context& h) const {\n";
    out << "return range<iterator>(ind_" << masterIndex << ".begin(),ind_" << masterIndex << ".end());\n";
    out << "}\n";

    out << "range<iterator> equalRange_0(const t_tuple& t) const {\n";
    out << "return range<iterator>(ind_" << masterIndex << ".begin(),ind_" << masterIndex << ".end());\n";
    out << "}\n";

    // equalRange methods
    for (int64_t search : getMinIndexSelection().getSearches()) {
        auto& lexOrder = getMinIndexSelection().getLexOrder(search);
        size_t indNum = indexToNumMap[lexOrder];

        out << "range<iterator_" << indNum << "> equalRange_" << search;
        out << "(const t_tuple& t, context& h) const {\n";

        // compute size of sub-index
        size_t indSize = 0;
        for (size_t i = 0; i < arity; i++) {
            if (((search >> i) & 1) != 0) {
                indSize++;
            }
        }

        out << "auto r = ind_" << indNum << ".template getBoundaries<" << indSize << ">(orderIn_" << indNum
            << "(t), h.hints_" << indNum << ");\n";
        out << "return make_range(iterator_" << indNum << "(r.begin()), iterator_" << indNum
            << "(r.end()));\n";
        out << "}\n";

        out << "range<iterator_" << indNum << "> equalRange_" << search;
        out << "(const t_tuple& t) const {\n";
        out << "context h; return equalRange_" << search << "(t, h);\n";
        out << "}\n";
    }

    // empty method
    out << "bool empty() const {\n";
    out << "return ind_" << masterIndex << ".empty();\n";
    out << "}\n";

    // partition method
    out << "std::vector<range<iterator>> partition() const {\n";
    out << "std::vector<range<iterator>> res;\n";
    out << "for (const auto& cur : ind_" << masterIndex << ".partition(10000)) {\n";
    out << "    res.push_back(make_range(iterator(cur.begin()), iterator(cur.end())));\n";
    out << "}\n";
    out << "return res;\n";
    out << "}\n";

    // purge method
    out << "void purge() {\n";
    for (size_t i = 0; i < numIndexes; i++) {
        out << "ind_" << i << ".clear();\n";
    }
    out << "}\n";

    // begin and end iterators
    out << "iterator begin() const {\n";
    out << "return iterator_" << masterIndex << "(ind_" << masterIndex << ".begin());\n";
    out << "}\n";

    out << "iterator end() const {\n";
    out << "return iterator_" << masterIndex << "(ind_" << masterIndex << ".end());\n";
    out << "}\n";

    // TODO: finish printHintStatistics method
    out << "void printHintStatistics(std::ostream& o, const std::string prefix) const {\n";
    for (size_t i = 0; i < numIndexes; i++) {
        out << "const auto& stats_" << i << " = ind_" << i << ".getHintStatistics();\n";
        out << "o << prefix << \"arity " << arity << " brie index " << inds[i]
            << ": (hits/misses/total)\\n\";\n";
        out << "o << prefix << \"Insert: \" << stats_" << i << ".inserts.getHits() << \"/\" << stats_" << i
            << ".inserts.getMisses() << \"/\" << stats_" << i << ".inserts.getAccesses() << \"\\n\";\n";
        out << "o << prefix << \"Contains: \" << stats_" << i << ".contains.getHits() << \"/\" << stats_" << i
            << ".contains.getMisses() << \"/\" << stats_" << i << ".contains.getAccesses() << \"\\n\";\n";
        out << "o << prefix << \"Range-query: \" << stats_" << i
            << ".get_boundaries.getHits() << \"/\" << stats_" << i
            << ".get_boundaries.getMisses() << \"/\" << stats_" << i
            << ".get_boundaries.getAccesses() << \"\\n\";\n";
    }
    out << "}\n";

    // orderOut and orderIn methods for reordering tuples according to index orders
    for (size_t i = 0; i < numIndexes; i++) {
        auto ind = inds[i];
        out << "static t_tuple orderIn_" << i << "(const t_tuple& t) {\n";
        out << "t_tuple res;\n";
        for (size_t j = 0; j < ind.size(); j++) {
            out << "res[" << j << "] = t[" << ind[j] << "];\n";
        }
        out << "return res;\n";
        out << "}\n";

        out << "static t_tuple orderOut_" << i << "(const t_tuple& t) {\n";
        out << "t_tuple res;\n";
        for (size_t j = 0; j < ind.size(); j++) {
            out << "res[" << ind[j] << "] = t[" << j << "];\n";
        }
        out << "return res;\n";
        out << "}\n";
    }

    // end class
    out << "};\n";
}

// -------- Eqrel Relation --------

/** Generate index set for a eqrel relation */
void SynthesiserEqrelRelation::computeIndices() {
    assert(!isProvenance && "eqrel cannot be used with provenance");

    masterIndex = 0;
    // {1, 0} is equivalent for an eqrel
    computedIndices = {{0, 1}};
}

/** Generate type name of a eqrel relation */
std::string SynthesiserEqrelRelation::getTypeName() {
    return "t_eqrel";
}

/** Generate type struct of a eqrel relation */
void SynthesiserEqrelRelation::generateTypeStruct(std::ostream& out) {
    const auto& inds = getIndices();
    size_t numIndexes = inds.size();
    std::map<MinIndexSelection::LexOrder, int> indexToNumMap;

    // struct definition
    out << "struct " << getTypeName() << " {\n";

    // eqrel is only for binary relations
    out << "using t_tuple = ram::Tuple<RamDomain, 2>;\n";
    out << "using t_ind_" << masterIndex << " = EquivalenceRelation<t_tuple>;\n";
    out << "t_ind_" << masterIndex << " ind_" << masterIndex << ";\n";

    // generate auxiliary iterators that reorder tuples according to index orders
    // generate auxiliary iterators which orderOut
    out << "class iterator_0 : public std::iterator<std::forward_iterator_tag, t_tuple> {\n";
    out << "    using nested_iterator = typename t_ind_0::iterator;\n";
    out << "    nested_iterator nested;\n";
    out << "    t_tuple value;\n";

    out << "public:\n";
    out << "    iterator_0() = default;\n";
    out << "    iterator_0(const nested_iterator& iter) : nested(iter), value(orderOut_0(*iter)) {}\n";
    out << "    iterator_0(const iterator_0& other) = default;\n";
    out << "    iterator_0& operator=(const iterator_0& other) = default;\n";

    out << "    bool operator==(const iterator_0& other) const {\n";
    out << "        return nested == other.nested;\n";
    out << "    }\n";

    out << "    bool operator!=(const iterator_0& other) const {\n";
    out << "        return !(*this == other);\n";
    out << "    }\n";

    out << "    const t_tuple& operator*() const {\n";
    out << "        return value;\n";
    out << "    }\n";

    out << "    const t_tuple* operator->() const {\n";
    out << "        return &value;\n";
    out << "    }\n";

    out << "    iterator_0& operator++() {\n";
    out << "        ++nested;\n";
    out << "        value = orderOut_0(*nested);\n";
    out << "        return *this;\n";
    out << "    }\n";
    out << "};\n";

    out << "using iterator = iterator_" << masterIndex << ";\n";

    // Create a struct storing the context hints for each index
    out << "struct context {\n";
    out << "t_ind_" << masterIndex << "::operation_hints hints_" << masterIndex << ";\n";
    out << "};\n";
    out << "context createContext() { return context(); }\n";

    // insert methods
    out << "bool insert(const t_tuple& t) {\n";
    out << "return ind_" << masterIndex << ".insert(t[0], t[1]);\n";
    out << "}\n";

    out << "bool insert(const t_tuple& t, context& h) {\n";
    out << "return ind_" << masterIndex << ".insert(t[0], t[1], h.hints_" << masterIndex << ");\n";
    out << "}\n";

    out << "bool insert(const RamDomain* ramDomain) {\n";
    out << "RamDomain data[2];\n";
    out << "std::copy(ramDomain, ramDomain + 2, data);\n";
    out << "const t_tuple& tuple = reinterpret_cast<const t_tuple&>(data);\n";
    out << "context h;\n";
    out << "return insert(tuple, h);\n";
    out << "}\n";

    out << "bool insert(RamDomain a1, RamDomain a2) {\n";
    out << "RamDomain data[2] = {a1, a2};\n";
    out << "return insert(data);\n";
    out << "}\n";

    // extends method for eqrel
    // performs a delta extension, where we union the sets that share elements between this and other.
    //      i.e. if a in this, and a in other, union(set(this->a), set(other->a))
    out << "void extend(const " << getTypeName() << "& other) {\n";
    out << "ind_" << masterIndex << ".extend(other.ind_" << masterIndex << ");\n";
    out << "}\n";

    // contains methods
    out << "bool contains(const t_tuple& t) const {\n";
    out << "return ind_" << masterIndex << ".contains(t[0], t[1]);\n";
    out << "}\n";

    out << "bool contains(const t_tuple& t, context& h) const {\n";
    out << "return ind_" << masterIndex << ".contains(t[0], t[1]);\n";
    out << "}\n";

    // size method
    out << "std::size_t size() const {\n";
    out << "return ind_" << masterIndex << ".size();\n";
    out << "}\n";

    // find methods
    out << "iterator find(const t_tuple& t) const {\n";
    out << "return ind_" << masterIndex << ".find(orderIn_" << masterIndex << "(t));\n";
    out << "}\n";

    out << "iterator find(const t_tuple& t, context& h) const {\n";
    out << "return ind_" << masterIndex << ".find(orderIn_" << masterIndex << "(t));\n";
    out << "}\n";

    // equalRange methods, one for each of the 4 possible search patterns
    for (int i = 1; i < 4; i++) {
        out << "range<iterator> equalRange_" << i;
        out << "(const t_tuple& t, context& h) const {\n";
        // compute size of sub-index
        size_t indSize = 0;
        for (size_t column = 0; column < 2; column++) {
            if (((i >> column) & 1) != 0) {
                indSize++;
            }
        }
        out << "auto r = ind_" << masterIndex << ".template getBoundaries<" << indSize << ">(orderIn_"
            << masterIndex << "(t), h.hints_" << masterIndex << ");\n";
        out << "return make_range(iterator(r.begin()), iterator(r.end()));\n";
        out << "}\n";

        out << "range<iterator> equalRange_" << i;
        out << "(const t_tuple& t) const {\n";
        out << "context h; return equalRange_" << i << "(t, h);\n";
        out << "}\n";
    }

    // empty method
    out << "bool empty() const {\n";
    out << "return ind_" << masterIndex << ".size() == 0;\n";
    out << "}\n";

    // partition method
    out << "std::vector<range<iterator>> partition() const {\n";
    out << "std::vector<range<iterator>> res;\n";
    out << "for (const auto& cur : ind_" << masterIndex << ".partition(10000)) {\n";
    out << "    res.push_back(make_range(iterator(cur.begin()), iterator(cur.end())));\n";
    out << "}\n";
    out << "return res;\n";
    out << "}\n";

    // purge method
    out << "void purge() {\n";
    for (size_t i = 0; i < numIndexes; i++) {
        out << "ind_" << i << ".clear();\n";
    }
    out << "}\n";

    // begin and end iterators
    out << "iterator begin() const {\n";
    out << "return iterator_" << masterIndex << "(ind_" << masterIndex << ".begin());\n";
    out << "}\n";

    out << "iterator end() const {\n";
    out << "return iterator_" << masterIndex << "(ind_" << masterIndex << ".end());\n";
    out << "}\n";
 
    // printHintStatistics method
    out << "void printHintStatistics(std::ostream& o, const std::string prefix) const {\n";
    out << "o << \"eqrel index: no hint statistics supported\\n\";\n";
    out << "}\n";

   // generate orderIn and orderOut methods which reorder tuples
    // according to index orders
    for (size_t i = 0; i < numIndexes; i++) {
        auto ind = inds[i];
        out << "static t_tuple orderIn_" << i << "(const t_tuple& t) {\n";
        out << "t_tuple res;\n";
        for (size_t j = 0; j < ind.size(); j++) {
            out << "res[" << j << "] = t[" << ind[j] << "];\n";
        }
        out << "return res;\n";
        out << "}\n";

        out << "static t_tuple orderOut_" << i << "(const t_tuple& t) {\n";
        out << "t_tuple res;\n";
        for (size_t j = 0; j < ind.size(); j++) {
            out << "res[" << ind[j] << "] = t[" << j << "];\n";
        }
        out << "return res;\n";
        out << "}\n";
    }

    // end class
    out << "};\n";
}

// -------- R-Tree Relation --------

/** Generate index set for a direct indexed relation */
void SynthesiserRtreeRelation::computeIndices() {
}

/** Generate type name of a direct indexed relation */
std::string SynthesiserRtreeRelation::getTypeName() {
    std::stringstream res;
    res << "t_rtree_" << getArity();
    for (auto& search : getMinIndexSelection().getSearches()) {
        res << "__" << search;
    }
    return res.str();
}

/** Generate type struct of a direct indexed relation */
void SynthesiserRtreeRelation::generateTypeStruct(std::ostream& out) {
    size_t arity = getArity();

    // abbreviate boost namespace
    out << "namespace bg = boost::geometry;\n";
    out << "namespace bgi = boost::geometry::index;\n";

    // struct definition
    out << "struct " << getTypeName() << " {\n";
    
    // stored tuple type
    out << "using t_tuple = Tuple<RamDomain, " << arity << ">;\n";

    // using declarations for boost geometry
    out << "using point = bg::model::point<RamDomain, " << arity << " , bg::cs::cartesian>;\n";
    out << "using box = bg::model::box<point>;\n";
    out << "using value = std::pair<point, t_tuple>;\n";
    out << "using t_ind = bgi::rtree<value, bgi::linear<16>>;\n";
    out << "using const_query_iterator = t_ind::const_query_iterator;\n";

    // needed to iterate tuples not (geometry, tuple) pairs therefore transform_iterator
    // define transform functions for boost::transform_iterator 
    out << "static value::second_type get_second(value entry) { return entry.second; }\n";
    out << "static bool satisfies_any(value entry) { return true; }\n"; 
    out << "using get_second_t =  value::second_type (*)(value);\n";
    out << "using iterator = boost::transform_iterator<get_second_t, const_query_iterator>;\n";

    // need an index as member
    out << "t_ind ind;\n";
#ifdef BLOOM_F    
    // experimental bloom filter to speed up existence checks
    out << "BloomFilter bf = BloomFilter(34400000, 12);\n";
#endif
    // bloom filter statistics
    out << "mutable std::size_t bloomFrequency = 0;\n";
    out << "mutable std::size_t bloomGuesses = 0;\n";
    out << "mutable std::size_t incorrectGuesses = 0;\n";
    out << "mutable long bloomInsertTime = 0;\n";
    out << "mutable long bloomContainsTime = 0;\n";

    // total operations performed by rtree
    out << "mutable std::size_t totalFrequency = 0;\n";

    // frequency of each operation
    out << "mutable std::size_t insertFrequency = 0;\n";
    out << "mutable std::size_t containsFrequency = 0;\n";
    out << "mutable std::size_t findFrequency = 0;\n";
    out << "mutable std::size_t equalRangeFrequency = 0;\n";
    out << "mutable std::size_t sizeFrequency = 0;\n";
    out << "mutable std::size_t emptyFrequency = 0;\n";
    out << "mutable std::size_t purgeFrequency = 0;\n";
    out << "mutable std::size_t beginFrequency = 0;\n";
    out << "mutable std::size_t endFrequency = 0;\n";

    // total time spent in operations
    out << "mutable long totalTime = 0;\n";

    // cumulative time in micro seconds
    out << "mutable long insertTime = 0;\n";
    out << "mutable long containsTime = 0;\n";
    out << "mutable long findTime = 0;\n";
    out << "mutable long equalRangeTime = 0;\n";
    out << "mutable long sizeTime = 0;\n";
    out << "mutable long emptyTime = 0;\n";
    out << "mutable long purgeTime = 0;\n";
    out << "mutable long beginTime = 0;\n";
    out << "mutable long endTime = 0;\n";

    // dummy context
    // create a struct storing the context hints for each index
    out << "struct context {\n";
    out << "\n";
    out << "};\n";
    out << "context createContext() { return context(); }\n";
 
    // printHintStatistics method
    out << "void printHintStatistics(std::ostream& o, const std::string prefix) const {\n";
   
    // print number of operations
    out << "o << \"Total number of operations: \" << totalFrequency << \"\\n\\n\";\n";
   
    // bloom and rtree insert count
    out << "o << \"Number of insert() operations: \" << insertFrequency << ";
    out << "\" (\" << 100*static_cast<double>(insertFrequency)/totalFrequency << \"%)\\n\"\n;"; 
    // bloom contains count
    out << "o << \"Number of Bloom Filter contains() operations: \" << bloomFrequency << ";
    out << "\" (\" << 100*static_cast<double>(bloomFrequency)/totalFrequency << \"%)\\n\"\n;";
    // rtree contains count
    out << "o << \"Number of Rtree contains() operations: \" << containsFrequency << ";
    out << "\" (\" << 100*static_cast<double>(containsFrequency)/totalFrequency << \"%)\\n\"\n;";
    // find count 
    out << "o << \"Number of find() operations: \" << findFrequency << ";
    out << "\" (\" << 100*static_cast<double>(findFrequency)/totalFrequency << \"%)\\n\"\n;"; 
    // equalRange count 
    out << "o << \"Number of equalRange() operations: \" << equalRangeFrequency << ";
    out << "\" (\" << 100*static_cast<double>(equalRangeFrequency)/totalFrequency << \"%)\\n\"\n;";
    // size count
    out << "o << \"Number of size() operations: \" << sizeFrequency << ";
    out << "\" (\" << 100*static_cast<double>(sizeFrequency)/totalFrequency << \"%)\\n\";\n";
    // empty count
    out << "o << \"Number of empty() operations: \" << emptyFrequency << ";
    out << "\" (\" << 100*static_cast<double>(emptyFrequency)/totalFrequency << \"%)\\n\";\n";
    // purge count 
    out << "o << \"Number of purge() operations: \" << purgeFrequency << ";
    out << "\" (\" << 100*static_cast<double>(purgeFrequency)/totalFrequency << \"%)\\n\";\n";
    // insert count
    out << "o << \"Number of begin() operations: \" << beginFrequency << ";
    out << "\" (\" << 100*static_cast<double>(beginFrequency)/totalFrequency << \"%)\\n\";\n";
    // find count 
    out << "o << \"Number of end() operations: \" << endFrequency << ";
    out << "\" (\" << 100*static_cast<double>(endFrequency)/totalFrequency << \"%)\\n\";\n";

    // print total time of operations
    out << "o << \"\\nTotal time: \" << totalTime << \"us\\n\\n\";\n";
  
    // bloom insert time
    out << "o << \"Time of Bloom Filter insert() operations: \" << bloomInsertTime << ";
    out << "\"us (\" << 100*static_cast<double>(bloomInsertTime)/totalTime << \"%)\\n\";\n";
    // rtree insert time
    out << "o << \"Time of Rtree insert() operations: \" << insertTime << ";
    out << "\"us (\" << 100*static_cast<double>(insertTime)/totalTime << \"%)\\n\";\n";
    // contains time
    out << "o << \"Time of Bloom Filter contains() operations: \" << bloomContainsTime << ";
    out << "\"us (\" << 100*static_cast<double>(bloomContainsTime)/totalTime << \"%)\\n\";\n";
    // contains time
    out << "o << \"Time of Rtree contains() operations: \" << containsTime << ";
    out << "\"us (\" << 100*static_cast<double>(containsTime)/totalTime << \"%)\\n\";\n";
    // find time 
    out << "o << \"Time of find() operations: \" << findTime << ";
    out << "\"us (\" << 100*static_cast<double>(findTime)/totalTime << \"%)\\n\";\n"; 
    // equalRange time 
    out << "o << \"Time of equalRange() operations: \" << equalRangeTime << ";
    out << "\"us (\" << 100*static_cast<double>(equalRangeTime)/totalTime << \"%)\\n\";\n";
    // size time
    out << "o << \"Time of size() operations: \" << sizeTime << ";
    out << "\"us (\" << 100*static_cast<double>(sizeTime)/totalTime << \"%)\\n\";\n";
    // empty time
    out << "o << \"Time of empty() operations: \" << emptyTime << ";
    out << "\"us (\" << 100*static_cast<double>(emptyTime)/totalTime << \"%)\\n\";\n";
    // purge time 
    out << "o << \"Time of purge() operations: \" << purgeTime << ";
    out << "\"us (\" << 100*static_cast<double>(purgeTime)/totalTime << \"%)\\n\";\n";
    // insert time
    out << "o << \"Time of begin() operations: \" << beginTime << ";
    out << "\"us (\" << 100*static_cast<double>(beginTime)/totalTime << \"%)\\n\";\n";
    // find count 
    out << "o << \"Time of end() operations: \" << endTime << ";
    out << "\"us (\" << 100*static_cast<double>(endTime)/totalTime << \"%)\\n\";\n";

    // contains false positive rate
    out << "o << \"\\nFalse Positive Rate of Bloom Filter contains() operations: \" << ";
    out  << "(bloomGuesses ? 100*static_cast<double>(incorrectGuesses)/bloomGuesses : 0) << \"%\\n\";\n";
    out << "}\n";

    // need to construct a boost geometry point from a tuple
    out << "static auto get_point(const t_tuple& t) {\n";
    out << "point p;\n";
    for(size_t i=0; i<arity; ++i)
    {
    	out << "p.set<" << i << ">(t[" << i << "]);\n";
    }
    out << "return p;";
    out << "}\n";

    // contains method
    out << "bool contains(const t_tuple& t) const {\n";
     
    // bloom time
    out << "++bloomFrequency;\n";
    out << "++totalFrequency;\n";
    out << "auto start = now();\n";
#ifdef BLOOM_F
    // first check the bloom filter
    out << "bool possiblyContains = bf.possiblyContains((const uint8_t*)t.data, " << arity << "*sizeof(RamDomain));\n";
#endif

#ifndef BLOOM_F
    out << "bool possiblyContains = true;\n";
#endif

    // bloom time
    out << "auto end = now();\n";
    out << "auto elapsed = duration_in_us(start, end);\n";
    out << "bloomContainsTime += elapsed;\n";
    out << "totalTime += elapsed;\n";

    // only need to compute if it possibly contains it
    out << "bool res = false;\n";
    out << "if (possiblyContains) {\n";

#ifdef BLOOM_F
    out << "    ++bloomGuesses;\n";
#endif
    out << "    ++containsFrequency;\n";
    out << "    ++totalFrequency;\n";

    // restart timer for real contains time
    out << "    start = now();\n";

    out << "    res = (ind.qbegin(bgi::intersects(get_point(t))) != ind.qend());\n";
    
    out << "    end = now();\n";
    out << "    elapsed = duration_in_us(start, end);\n";
    out << "    containsTime += elapsed;\n";
    out << "    totalTime += elapsed;\n";
#ifdef BLOOM_F
    out << "    if (!res) {\n";
    out << "        ++incorrectGuesses;\n";
    out << "    }\n"; 
#endif
    out << "}\n";

    out << "return res;\n";
    out << "}\n";

    // contains method
    out << "bool contains(const t_tuple& t, context &hint) const {\n";
    out << "return contains(t);\n";
    out << "}\n";

    // insert methods
    out << "bool insert(const t_tuple& t) {\n";

    out << "bool res = false;\n";

    out << "if (!contains(t)){\n";

    out << "    ++insertFrequency;\n";
    out << "    ++totalFrequency;\n";
    out << "    auto start = now();\n";

    out << "	ind.insert(std::make_pair(get_point(t), t));\n";

    out << "    auto end = now();\n";
    out << "    auto elapsed = duration_in_us(start, end);\n";
    out << "    insertTime += elapsed;\n";
    out << "    totalTime += elapsed;\n";

    // insert into the bloom filter as well
    out << "    start = now();\n";
#ifdef BLOOM_F
    out << "    bf.add((const uint8_t*)t.data, " << arity << "*sizeof(RamDomain));\n";
#endif
    out << "    end = now();\n";
    out << "    elapsed = duration_in_us(start, end);\n";
    out << "    bloomInsertTime += elapsed;\n";
    out << "    totalTime += elapsed;\n";

    out << "	res = true;\n";
    out << "}\n";
 
    out << "return res;\n";
    out << "}\n";  // end of insert(t_tuple&)

    out << "bool insert(const t_tuple& t, context& h) {\n";
    out << "(void)h;\n";
    out << "return insert(t);\n";
    out << "}\n";  // end of insert(t_tuple&,context&)

    out << "bool insert(const RamDomain* ramDomain) {\n";
    out << "t_tuple t;\n";
    out << "std::copy(ramDomain,ramDomain+" << arity << ",t.data);\n";    
    out << "return insert(t);\n";
    out << "}\n";  // end of insert(RamDomain*)

    std::vector<std::string> decls;
    std::vector<std::string> params;
    for (size_t i = 0; i < arity; i++) {
        decls.push_back("RamDomain a" + std::to_string(i));
        params.push_back("a" + std::to_string(i));
    }
    out << "bool insert(" << join(decls, ",") << ") {\n";
    out << "t_tuple t  = {" << join(params, ",") << "};\n";
    out << "return insert(t);\n";
    out << "}\n";  // end of insert(RamDomain x1, RamDomain x2, ...)

    // size method
    out << "std::size_t size() const {\n";

    out << "++sizeFrequency;\n";
    out << "++totalFrequency;\n";
    out << "auto start = now();\n";

    out << "auto res = ind.size();\n";

    out << "auto end = now();\n";
    out << "auto elapsed = duration_in_us(start, end);\n";
    out << "sizeTime += elapsed;\n";
    out << "totalTime += elapsed;\n";

    out << "return res;\n";
    out << "}\n";

    // find methods
    out << "iterator find(const t_tuple& t) const {\n";

    out << "++findFrequency;\n";
    out << "++totalFrequency;\n";
    out << "auto start = now();\n";

    out << "auto res = iterator(ind.qbegin(bgi::intersects(get_point(t))), get_second);\n";

    out << "auto end = now();\n";
    out << "auto elapsed = duration_in_us(start, end);\n";
    out << "findTime += elapsed;\n";
    out << "totalTime += elapsed;\n";

    out << "return res;\n";
    out << "}\n";

    // within_range helper method (box query)
    out << "souffle::range<iterator> within_range(const t_tuple &low, const t_tuple &high) const{\n";
    out << "box b(get_point(low), get_point(high));\n";
    out << "auto lb = iterator(ind.qbegin(bgi::intersects(b)), get_second);\n";
    out << "auto ub = iterator(ind.qend(), get_second);\n";
    out << "return souffle::make_range(lb, ub);\n"; 
    out << "}\n";

    // equalRange methods for each pattern which is used to search this relation
    for (int64_t search : getMinIndexSelection().getSearches()) {
	
        out << "souffle::range<iterator> equalRange_" << search;
        out << "(const t_tuple& t) const {\n";

	out << "++equalRangeFrequency;\n";
	out << "++totalFrequency;\n";
	out << "auto start = now();\n";

        // generate lower and upper bounds for range search
        out << "t_tuple low(t); t_tuple high(t);\n";
        // check which indices to pad out
        for (size_t column = 0; column < arity; column++) {
           // if bit number column is set
           if (((search >> column) & 1) == 0) {
              out << "low[" << column << "] = MIN_RAM_SIGNED;\n";
              out << "high[" << column << "] = MAX_RAM_SIGNED;\n";
           }
        }
	out << "auto res = within_range(low,high);\n";
        	
        out << "auto end = now();\n";
        out << "auto elapsed = duration_in_us(start, end);\n";
        out << "equalRangeTime += elapsed;\n";
        out << "totalTime += elapsed;\n";

        out << "return res;\n";
        out << "}\n";


	// generate identical with hint
        out << "souffle::range<iterator> equalRange_" << search;
        out << "(const t_tuple& t, context &hint) const {\n";
        out << "return equalRange_" << search << "(t);\n";
	out << "}\n";	
    }

    // empty method
    out << "bool empty() const {\n";
 
    out << "++emptyFrequency;\n";
    out << "++totalFrequency;\n";
    out << "auto start = now();\n";

    out << "bool res = ind.empty();\n";

    out << "auto end = now();\n";
    out << "auto elapsed = duration_in_us(start, end);\n";
    out << "emptyTime += elapsed;\n";
    out << "totalTime += elapsed;\n";

    out << "return res;\n";
    out << "}\n";

    // purge method
    out << "void purge() {\n";
  
    out << "++purgeFrequency;\n";
    out << "++totalFrequency;\n";
    out << "auto start = now();\n";

    out << "ind.clear();\n";
#ifdef BLOOM_F    
    out << "bf.clear();\n";
#endif    
    out << "auto end = now();\n";
    out << "auto elapsed = duration_in_us(start, end);\n";
    out << "purgeTime += elapsed;\n";
    out << "totalTime += elapsed;\n";

    out << "}\n";

    // begin and end iterators
    out << "iterator begin() const {\n";
    
    out << "++beginFrequency;\n";
    out << "++totalFrequency;\n";
    out << "auto start = now();\n";

    out << "auto res = iterator(ind.qbegin(bgi::satisfies(satisfies_any)), get_second);\n";
    
    out << "auto end = now();\n";
    out << "auto elapsed = duration_in_us(start, end);\n";
    out << "beginTime += elapsed;\n";
    out << "totalTime += elapsed;\n";

    out << "return res;\n";
    out << "}\n";

    out << "iterator end() const {\n";
   
   
    out << "++endFrequency;\n";
    out << "++totalFrequency;\n";
    out << "auto start = now();\n";

    out << "auto res = iterator(ind.qend(), get_second);\n";

    out << "auto end = now();\n";
    out << "auto elapsed = duration_in_us(start, end);\n";
    out << "endTime += elapsed;\n";
    out << "totalTime += elapsed;\n";

    out << "return res;\n";
    out << "}\n";

    // end struct
    out << "};\n";
}


}  // end of namespace souffle
