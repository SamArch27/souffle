/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file CompiledSouffle.h
 *
 * Main include file for generated C++ classes of Souffle
 *
 ***********************************************************************/

#pragma once

#include <boost/foreach.hpp>
#include <boost/geometry.hpp>
#include <boost/geometry/geometries/box.hpp>
#include <boost/geometry/geometries/point.hpp>
#include <boost/geometry/index/rtree.hpp>
#include <boost/iterator/transform_iterator.hpp>

/*************************
 * Dependencies for R-tree
 *************************/

#include "souffle/RamTypes.h"
#include "souffle/RecordTable.h"
#include "souffle/SignalHandler.h"
#include "souffle/SouffleInterface.h"
#include "souffle/SymbolTable.h"
#include "souffle/datastructure/Brie.h"
#include "souffle/datastructure/EquivalenceRelation.h"
#include "souffle/datastructure/Table.h"
#include "souffle/io/IOSystem.h"
#include "souffle/io/WriteStream.h"
#include "souffle/utility/CacheUtil.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/EvaluatorUtil.h"
#include "souffle/utility/FileUtil.h"
#include "souffle/utility/FunctionalUtil.h"
#include "souffle/utility/MiscUtil.h"
#include "souffle/utility/ParallelUtil.h"
#include "souffle/utility/StreamUtil.h"
#include "souffle/utility/StringUtil.h"
#ifndef __EMBEDDED_SOUFFLE__
#include "souffle/CompiledOptions.h"
#include "souffle/profile/Logger.h"
#include "souffle/profile/ProfileEvent.h"
#endif
#include <array>
#include <atomic>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <exception>
#include <iostream>
#include <iterator>
#include <memory>
#include <regex>
#include <string>
#include <utility>
#include <vector>

#if defined(_OPENMP)
#include <omp.h>
#endif

namespace souffle {

extern "C" {
inline souffle::SouffleProgram* getInstance(const char* p) {
    return souffle::ProgramFactory::newInstance(p);
}
}

/**
 * Relation wrapper used internally in the generated Datalog program
 */
template <class RelType>
class RelationWrapper : public souffle::Relation {
public:
    static constexpr arity_type Arity = RelType::Arity;
    using TupleType = Tuple<RamDomain, Arity>;
    using AttrStrSeq = std::array<const char*, Arity>;

private:
    RelType& relation;
    SouffleProgram& program;
    std::string name;
    AttrStrSeq attrTypes;
    AttrStrSeq attrNames;
    const uint32_t id;
    const arity_type numAuxAttribs;

    // NB: internal wrapper. does not satisfy the `iterator` concept.
    class iterator_wrapper : public iterator_base {
        typename RelType::iterator it;
        const Relation* relation;
        tuple t;

    public:
        iterator_wrapper(uint32_t arg_id, const Relation* rel, typename RelType::iterator arg_it)
                : iterator_base(arg_id), it(std::move(arg_it)), relation(rel), t(rel) {}
        void operator++() override {
            ++it;
        }
        tuple& operator*() override {
            auto&& value = *it;
            t.rewind();
            for (std::size_t i = 0; i < Arity; i++)
                t[i] = value[i];
            return t;
        }
        iterator_base* clone() const override {
            return new iterator_wrapper(*this);
        }

    protected:
        bool equal(const iterator_base& o) const override {
            const auto& casted = asAssert<iterator_wrapper>(o);
            return it == casted.it;
        }
    };

public:
    RelationWrapper(uint32_t id, RelType& r, SouffleProgram& p, std::string name, const AttrStrSeq& t,
            const AttrStrSeq& n, arity_type numAuxAttribs)
            : relation(r), program(p), name(std::move(name)), attrTypes(t), attrNames(n), id(id),
              numAuxAttribs(numAuxAttribs) {}

    iterator begin() const override {
        return iterator(mk<iterator_wrapper>(id, this, relation.begin()));
    }
    iterator end() const override {
        return iterator(mk<iterator_wrapper>(id, this, relation.end()));
    }

    void insert(const tuple& arg) override {
        TupleType t;
        assert(&arg.getRelation() == this && "wrong relation");
        assert(arg.size() == Arity && "wrong tuple arity");
        for (std::size_t i = 0; i < Arity; i++) {
            t[i] = arg[i];
        }
        relation.insert(t);
    }
    bool contains(const tuple& arg) const override {
        TupleType t;
        assert(arg.size() == Arity && "wrong tuple arity");
        for (std::size_t i = 0; i < Arity; i++) {
            t[i] = arg[i];
        }
        return relation.contains(t);
    }
    std::size_t size() const override {
        return relation.size();
    }
    std::string getName() const override {
        return name;
    }
    const char* getAttrType(std::size_t arg) const override {
        assert(arg < Arity && "attribute out of bound");
        return attrTypes[arg];
    }
    const char* getAttrName(std::size_t arg) const override {
        assert(arg < Arity && "attribute out of bound");
        return attrNames[arg];
    }
    arity_type getArity() const override {
        return Arity;
    }
    arity_type getAuxiliaryArity() const override {
        return numAuxAttribs;
    }
    SymbolTable& getSymbolTable() const override {
        return program.getSymbolTable();
    }

    /** Eliminate all the tuples in relation*/
    void purge() override {
        relation.purge();
    }
};

/** Nullary relations */
class t_nullaries {
private:
    std::atomic<bool> data{false};

public:
    static constexpr Relation::arity_type Arity = 0;

    t_nullaries() = default;
    using t_tuple = Tuple<RamDomain, 0>;
    struct context {};
    context createContext() {
        return context();
    }
    class iterator {
        bool value;

    public:
        typedef std::forward_iterator_tag iterator_category;
        using value_type = RamDomain*;
        using difference_type = ptrdiff_t;
        using pointer = value_type*;
        using reference = value_type&;

        iterator(bool v = false) : value(v) {}

        const RamDomain* operator*() {
            return nullptr;
        }

        bool operator==(const iterator& other) const {
            return other.value == value;
        }

        bool operator!=(const iterator& other) const {
            return other.value != value;
        }

        iterator& operator++() {
            if (value) {
                value = false;
            }
            return *this;
        }
    };
    iterator begin() const {
        return iterator(data);
    }
    iterator end() const {
        return iterator();
    }
    void insert(const t_tuple& /* t */) {
        data = true;
    }
    void insert(const t_tuple& /* t */, context& /* ctxt */) {
        data = true;
    }
    void insert(const RamDomain* /* ramDomain */) {
        data = true;
    }
    bool insert() {
        bool result = data;
        data = true;
        return !result;
    }
    bool contains(const t_tuple& /* t */) const {
        return data;
    }
    bool contains(const t_tuple& /* t */, context& /* ctxt */) const {
        return data;
    }
    std::size_t size() const {
        return data ? 1 : 0;
    }
    bool empty() const {
        return !data;
    }
    void purge() {
        data = false;
    }
    void printStatistics(std::ostream& /* o */) const {}
};

/** info relations */
template <Relation::arity_type Arity_>
class t_info {
public:
    static constexpr Relation::arity_type Arity = Arity_;

    t_info() = default;
    using t_tuple = Tuple<RamDomain, Arity>;
    struct context {};
    context createContext() {
        return context();
    }
    class iterator : public std::iterator<std::forward_iterator_tag, Tuple<RamDomain, Arity>> {
        typename std::vector<Tuple<RamDomain, Arity>>::const_iterator it;

    public:
        iterator(const typename std::vector<t_tuple>::const_iterator& o) : it(o) {}

        const t_tuple operator*() {
            return *it;
        }

        bool operator==(const iterator& other) const {
            return other.it == it;
        }

        bool operator!=(const iterator& other) const {
            return !(*this == other);
        }

        iterator& operator++() {
            it++;
            return *this;
        }
    };
    iterator begin() const {
        return iterator(data.begin());
    }
    iterator end() const {
        return iterator(data.end());
    }
    void insert(const t_tuple& t) {
        insert_lock.lock();
        if (!contains(t)) {
            data.push_back(t);
        }
        insert_lock.unlock();
    }
    void insert(const t_tuple& t, context& /* ctxt */) {
        insert(t);
    }
    void insert(const RamDomain* ramDomain) {
        insert_lock.lock();
        t_tuple t;
        for (std::size_t i = 0; i < Arity; ++i) {
            t.data[i] = ramDomain[i];
        }
        data.push_back(t);
        insert_lock.unlock();
    }
    bool contains(const t_tuple& t) const {
        for (const auto& o : data) {
            if (t == o) {
                return true;
            }
        }
        return false;
    }
    bool contains(const t_tuple& t, context& /* ctxt */) const {
        return contains(t);
    }
    std::size_t size() const {
        return data.size();
    }
    bool empty() const {
        return data.size() == 0;
    }
    void purge() {
        data.clear();
    }
    void printStatistics(std::ostream& /* o */) const {}

private:
    std::vector<Tuple<RamDomain, Arity>> data;
    Lock insert_lock;
};

}  // namespace souffle
