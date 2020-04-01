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

#include <boost/geometry.hpp>
#include <boost/geometry/geometries/point.hpp>
#include <boost/geometry/geometries/box.hpp>
#include <boost/geometry/index/rtree.hpp>
#include <boost/iterator/transform_iterator.hpp>
#include <boost/foreach.hpp>

/*************************
 * Dependencies for R-tree 
*************************/

#include "souffle/Brie.h"
#include "souffle/CompiledIndexUtils.h"
#include "souffle/CompiledTuple.h"
#include "souffle/IOSystem.h"
#include "souffle/ParallelUtils.h"
#include "souffle/RWOperation.h"
#include "souffle/RamTypes.h"
#include "souffle/RecordTable.h"
#include "souffle/SignalHandler.h"
#include "souffle/SouffleInterface.h"
#include "souffle/SymbolTable.h"
#include "souffle/Table.h"
#include "souffle/Util.h"
#include "souffle/WriteStream.h"
#ifndef __EMBEDDED_SOUFFLE__
#include "souffle/CompiledOptions.h"
#include "souffle/Logger.h"
#include "souffle/ProfileEvent.h"
#endif
#include <array>
#include <atomic>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <exception>
#include <iostream>
#include <memory>
#include <regex>
#include <string>
#include <utility>
#include <vector>

#if defined(_OPENMP)
#include <omp.h>
#endif

// definitions for murmurhash
#define FORCE_INLINE inline __attribute__((always_inline))
#define ROTL64(x,y)     rotl64(x,y)
#define BIG_CONSTANT(x) (x##LLU)

namespace souffle {

extern "C" {
inline souffle::SouffleProgram* getInstance(const char* p) {
    return souffle::ProgramFactory::newInstance(p);
}
}

/**
 * Relation wrapper used internally in the generated Datalog program
 */
template <uint32_t id, class RelType, class TupleType, size_t Arity, size_t NumAuxAttributes>
class RelationWrapper : public souffle::Relation {
private:
    RelType& relation;
    SymbolTable& symTable;
    std::string name;
    std::array<const char*, Arity> tupleType;
    std::array<const char*, Arity> tupleName;

    class iterator_wrapper : public iterator_base {
        typename RelType::iterator it;
        const Relation* relation;
        tuple t;

    public:
        iterator_wrapper(uint32_t arg_id, const Relation* rel, const typename RelType::iterator& arg_it)
                : iterator_base(arg_id), it(arg_it), relation(rel), t(rel) {}
        void operator++() override {
            ++it;
        }
        tuple& operator*() override {
            t.rewind();
            for (size_t i = 0; i < Arity; i++) {
                t[i] = (*it)[i];
            }
            return t;
        }
        iterator_base* clone() const override {
            return new iterator_wrapper(*this);
        }

    protected:
        bool equal(const iterator_base& o) const override {
            const auto& casted = static_cast<const iterator_wrapper&>(o);
            return it == casted.it;
        }
    };

public:
    RelationWrapper(RelType& r, SymbolTable& s, std::string name, const std::array<const char*, Arity>& t,
            const std::array<const char*, Arity>& n)
            : relation(r), symTable(s), name(std::move(name)), tupleType(t), tupleName(n) {}
    iterator begin() const override {
        return iterator(new iterator_wrapper(id, this, relation.begin()));
    }
    iterator end() const override {
        return iterator(new iterator_wrapper(id, this, relation.end()));
    }
    void insert(const tuple& arg) override {
        TupleType t;
        assert(&arg.getRelation() == this && "wrong relation");
        assert(arg.size() == Arity && "wrong tuple arity");
        for (size_t i = 0; i < Arity; i++) {
            t[i] = arg[i];
        }
        relation.insert(t);
    }
    bool contains(const tuple& arg) const override {
        TupleType t;
        assert(arg.size() == Arity && "wrong tuple arity");
        for (size_t i = 0; i < Arity; i++) {
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
    const char* getAttrType(size_t arg) const override {
        assert(arg < Arity && "attribute out of bound");
        return tupleType[arg];
    }
    const char* getAttrName(size_t arg) const override {
        assert(arg < Arity && "attribute out of bound");
        return tupleName[arg];
    }
    size_t getArity() const override {
        return Arity;
    }
    size_t getAuxiliaryArity() const override {
        return NumAuxAttributes;
    }
    SymbolTable& getSymbolTable() const override {
        return symTable;
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
    t_nullaries() = default;
    using t_tuple = ram::Tuple<RamDomain, 0>;
    struct context {};
    context createContext() {
        return context();
    }
    class iterator : public std::iterator<std::forward_iterator_tag, RamDomain*> {
        bool value;

    public:
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
    void printHintStatistics(std::ostream& /* o */, std::string /* prefix */) const {}
};

/** info relations */
template <int Arity>
class t_info {
private:
    std::vector<ram::Tuple<RamDomain, Arity>> data;
    Lock insert_lock;

public:
    t_info() = default;
    using t_tuple = ram::Tuple<RamDomain, Arity>;
    struct context {};
    context createContext() {
        return context();
    }
    class iterator : public std::iterator<std::forward_iterator_tag, ram::Tuple<RamDomain, Arity>> {
        typename std::vector<ram::Tuple<RamDomain, Arity>>::const_iterator it;

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
        for (size_t i = 0; i < Arity; ++i) {
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
    void printHintStatistics(std::ostream& /* o */, std::string /* prefix */) const {}
};


inline uint64_t rotl64 ( uint64_t x, int8_t r )
{
  return (x << r) | (x >> (64 - r));
}

FORCE_INLINE uint64_t getblock64 ( const uint64_t * p, int i )
{
  return p[i];
}

FORCE_INLINE uint64_t fmix64 ( uint64_t k )
{
  k ^= k >> 33;
  k *= BIG_CONSTANT(0xff51afd7ed558ccd);
  k ^= k >> 33;
  k *= BIG_CONSTANT(0xc4ceb9fe1a85ec53);
  k ^= k >> 33;

  return k;
}

// hashing algorithm for the BloomFilter
void MurmurHash3_x64_128 ( const void * key, const int len,
                           const uint32_t seed, void * out )
{
  const uint8_t * data = (const uint8_t*)key;
  const int nblocks = len / 16;

  uint64_t h1 = seed;
  uint64_t h2 = seed;

  const uint64_t c1 = BIG_CONSTANT(0x87c37b91114253d5);
  const uint64_t c2 = BIG_CONSTANT(0x4cf5ad432745937f);

  //----------
  // body
const uint64_t * blocks = (const uint64_t *)(data);

  for(int i = 0; i < nblocks; i++)
  {
    uint64_t k1 = getblock64(blocks,i*2+0);
    uint64_t k2 = getblock64(blocks,i*2+1);

    k1 *= c1; k1  = ROTL64(k1,31); k1 *= c2; h1 ^= k1;

    h1 = ROTL64(h1,27); h1 += h2; h1 = h1*5+0x52dce729;

    k2 *= c2; k2  = ROTL64(k2,33); k2 *= c1; h2 ^= k2;

    h2 = ROTL64(h2,31); h2 += h1; h2 = h2*5+0x38495ab5;
  }

  //----------
  // tail

  const uint8_t * tail = (const uint8_t*)(data + nblocks*16);

  uint64_t k1 = 0;
  uint64_t k2 = 0;

  switch(len & 15)
  {
  case 15: k2 ^= ((uint64_t)tail[14]) << 48;
  case 14: k2 ^= ((uint64_t)tail[13]) << 40;
  case 13: k2 ^= ((uint64_t)tail[12]) << 32;
  case 12: k2 ^= ((uint64_t)tail[11]) << 24;
  case 11: k2 ^= ((uint64_t)tail[10]) << 16;
  case 10: k2 ^= ((uint64_t)tail[ 9]) << 8;
  case  9: k2 ^= ((uint64_t)tail[ 8]) << 0;
           k2 *= c2; k2  = ROTL64(k2,33); k2 *= c1; h2 ^= k2;

  case  8: k1 ^= ((uint64_t)tail[ 7]) << 56;
  case  7: k1 ^= ((uint64_t)tail[ 6]) << 48;
  case  6: k1 ^= ((uint64_t)tail[ 5]) << 40;
  case  5: k1 ^= ((uint64_t)tail[ 4]) << 32;
  case  4: k1 ^= ((uint64_t)tail[ 3]) << 24;
  case  3: k1 ^= ((uint64_t)tail[ 2]) << 16;
  case  2: k1 ^= ((uint64_t)tail[ 1]) << 8;
  case  1: k1 ^= ((uint64_t)tail[ 0]) << 0;
           k1 *= c1; k1  = ROTL64(k1,31); k1 *= c2; h1 ^= k1;
  };

  //----------
  // finalization

  h1 ^= len; h2 ^= len;

  h1 += h2;
  h2 += h1;

  h1 = fmix64(h1);
  h2 = fmix64(h2);

  h1 += h2;
  h2 += h1;

  ((uint64_t*)out)[0] = h1;
  ((uint64_t*)out)[1] = h2;
}


// helper function to generate 128 bit hash and split in 2
std::array<uint64_t, 2> hash(const uint8_t *data,  std::size_t len) {
    std::array<uint64_t, 2> hashValue;
    MurmurHash3_x64_128(data, len, 0, hashValue.data());
    return hashValue;
}

// helper function to retrieve the output of the nth hash function
inline uint64_t nthHash(uint8_t n, uint64_t hashA, uint64_t hashB, uint64_t filterSize) {
    return (hashA + n * hashB) % filterSize;
}


// Bloom Filter implementation
struct BloomFilter {

private:
    uint8_t m_numHashes;
    std::vector<bool> m_bits;

public:
    BloomFilter(uint64_t size, uint8_t numHashes)
          : m_bits(size),
            m_numHashes(numHashes) {}
     
    void clear()
    {
	    m_bits.assign(m_bits.size(), false);
    } 

    void add(const uint8_t *data, std::size_t len){
         // compute hash
         auto hashValues = hash(data, len);

         // combine result to set the bit at the corresponding index
         for (int n = 0; n < m_numHashes; n++) {
            m_bits[nthHash(n, hashValues[0], hashValues[1], m_bits.size())] = true;
         }
    }


    bool possiblyContains(const uint8_t *data, std::size_t len) const {
        // compute hash
        auto hashValues = hash(data, len);

        // applying the identical algorithm if we find that one of the bits is not set then it cant contain it
        for (int n = 0; n < m_numHashes; n++) {
            if (!m_bits[nthHash(n, hashValues[0], hashValues[1], m_bits.size())]) {
                 return false;
            }
        }
        // otherwise maybe it does contain it?
        return true;
    }
};


}  // namespace souffle
