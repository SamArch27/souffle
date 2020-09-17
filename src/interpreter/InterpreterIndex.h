/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2019, The Souffle Developers. All rights reserved.
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file InterpreterIndex.h
 *
 * Interpreter index with generic interface.
 *
 ***********************************************************************/
#pragma once

#include "souffle/CompiledTuple.h"
#include "souffle/RamTypes.h"
#include "souffle/utility/ContainerUtil.h"
#include <array>
#include <atomic>
#include <cassert>
#include <cstdint>
#include <cstring>
#include <iosfwd>
#include <iterator>
#include <memory>
#include <utility>
#include <vector>

namespace souffle {

/**
 * A construction-time sized tuple instance easing tuple handling
 * in non-compiled contexts.
 */
class DynTuple {
    std::vector<RamDomain> data;

public:
    DynTuple(std::size_t arity) : data(arity) {}

    std::size_t size() const {
        return data.size();
    }

    RamDomain& operator[](std::size_t i) {
        return data[i];
    }

    const RamDomain& operator[](std::size_t i) const {
        return data[i];
    }
};

/**
 * A type-erased reference to tuples. The reference does not
 * own the referenced data. It is thus very light-weight to
 * create and forward.
 */
class TupleRef {
    // The address of the first component of the tuple.
    const RamDomain* base = nullptr;

    // The size of the tuple.
    std::size_t arity = 0;

public:
    TupleRef() = default;

    /**
     * Creates a tuple reference from some externally maintained
     */
    TupleRef(const RamDomain* base, std::size_t arity) : base(base), arity(arity) {}

    /**
     * A constructor supporting the implicit conversion of
     * a tuple into a reference.
     */
    template <std::size_t Arity>
    TupleRef(const Tuple<RamDomain, Arity>& tuple) : TupleRef(&tuple[0], Arity) {}

    TupleRef(const DynTuple& tuple) : TupleRef(&tuple[0], tuple.size()) {}

    template <std::size_t Arity>
    const Tuple<RamDomain, Arity>& asTuple() const {
        assert(arity == Arity);
        return *reinterpret_cast<const Tuple<RamDomain, Arity>*>(base);
    }

    /**
     * Obtains the arity of the referenced tuple.
     */
    std::size_t size() const {
        return arity;
    }

    /*
     * Provide access to base reference.
     */
    const RamDomain* getBase() const {
        return base;
    }

    /**
     * Provides access to tuple components.
     */
    const RamDomain& operator[](std::size_t i) const {
        return base[i];
    }

    bool operator==(const TupleRef& other) const {
        if (arity != other.arity) {
            return false;
        }
        for (size_t i = 0; i < arity; ++i) {
            if (base[i] != other[i]) {
                return false;
            }
        }
        return true;
    }

    friend std::ostream& operator<<(std::ostream& out, TupleRef ref);
};

/**
 * An order to be enforced for storing tuples within
 * indexes. The order is defined by the sequence of
 * component to be considered in sorting tuples.
 */
class Order {
    using Attribute = uint32_t;
    using AttributeOrder = std::vector<Attribute>;
    AttributeOrder order;

public:
    Order() = default;
    Order(AttributeOrder pos) : order(std::move(pos)) {
        assert(valid());
    }

    // Creates a natural order for the given arity.
    static Order create(size_t arity);

    std::size_t size() const;

    /**
     * Determines whether this order is a valid order.
     */
    bool valid() const;

    template <std::size_t Arity>
    Tuple<RamDomain, Arity> encode(const Tuple<RamDomain, Arity>& entry) const {
        Tuple<RamDomain, Arity> res{};
        for (std::size_t i = 0; i < Arity; ++i) {
            res[i] = entry[order[i]];
        }
        return res;
    }

    template <std::size_t Arity>
    Tuple<RamDomain, Arity> decode(const Tuple<RamDomain, Arity>& entry) const {
        Tuple<RamDomain, Arity> res{};
        for (std::size_t i = 0; i < Arity; ++i) {
            res[order[i]] = entry[i];
        }
        return res;
    }

    const AttributeOrder& getOrder() const {
        return this->order;
    }

    bool operator==(const Order& other) const;
    bool operator!=(const Order& other) const;
    bool operator<(const Order& other) const;

    friend std::ostream& operator<<(std::ostream& out, const Order& order);
};

/**
 * An abstract perspective on a data range. A stream is a pair of iterators,
 * referencing the begin and end of a traversible sequence. A stream can only
 * be traversed once.
 */
class Stream {
public:
    // the size of the internally maintained buffer, corresponding
    // to the maximum chunk size retrieved from the source
    constexpr static int BUFFER_SIZE = 128;

    // the 'interface' for data sources
    class Source {
    public:
        virtual ~Source() = default;

        /**
         * Requests the source to retrieve the next set of elements,
         * to be stored in an array addressed by the first parameter.
         * The second parameter states an upper limit for the number
         * of elements to be retrieved.
         *
         * @return the number of elements retrieved, 0 if end has reached.
         */
        virtual int load(TupleRef* trg, int max) = 0;

        /**
         * Fill the target array in the first parameter with references to the current set of elements.
         * This is useful for cloning references to this Source. The second parameter limits the range
         * copied.
         *
         * @return the number of elements retrieved, 0 if end has reached.
         */
        virtual int reload(TupleRef* trg, int max) = 0;

        /**
         * Clone a source with the exact same state
         */
        virtual Own<Source> clone() = 0;
    };

private:
    // the source to read data from
    Own<Source> source = nullptr;

    // an internal buffer for decoded elements
    std::array<TupleRef, BUFFER_SIZE> buffer{};

    // the current position in the buffer
    int cur = 0;

    // the end of valid elements in the buffer
    int limit = 0;

public:
    Stream(Own<Source>&& src) : source(std::move(src)) {
        loadNext();
    }

    Stream() = default;

    Stream(Stream& other) = delete;

    Stream& operator=(Stream& other) = delete;

    Stream(Stream&& other)
            : source(std::move(other.source)), buffer(other.buffer), cur(other.cur), limit(other.limit) {}

    Stream& operator=(Stream&& other) {
        source = std::move(other.source);
        // only copy important data
        std::memcpy(
                &buffer[other.cur], &other.buffer[other.cur], sizeof(TupleRef) * (other.limit - other.cur));
        cur = other.cur;
        limit = other.limit;
        return *this;
    }

    template <typename S>
    Stream(Own<S>&& src) : Stream(Own<Source>(std::move(src))) {}

    Own<Stream> clone() const {
        if (source == nullptr) {
            return mk<Stream>();
        }
        auto newStream = mk<Stream>(source->clone());
        newStream->source->reload(&newStream->buffer[0], limit);
        newStream->cur = cur;
        newStream->limit = limit;
        return newStream;
    }

    /**
     * The iterator exposed by this stream to iterate through
     * its elements using a range-based for.
     */
    class Iterator : public std::iterator<std::forward_iterator_tag, TupleRef> {
        Stream* stream = nullptr;

    public:
        Iterator() = default;

        Iterator(Stream& stream) : stream(&stream) {
            if (stream.cur >= stream.limit) {
                this->stream = nullptr;
            }
        }

        Iterator& operator++() {
            ++stream->cur;
            if (stream->cur < stream->limit) {
                return *this;
            }
            stream->loadNext();
            if (stream->cur >= stream->limit) {
                stream = nullptr;
            }
            return *this;
        }

        const TupleRef& operator*() const {
            return stream->buffer[stream->cur];
        }

        bool operator!=(const Iterator& other) const {
            return stream != other.stream;
        }

        bool operator==(const Iterator& other) const {
            return stream == other.stream;
        }
    };

    // support for ranged based for loops
    Iterator begin() {
        return Iterator(*this);
    }
    Iterator end() const {
        return Iterator();
    }

private:
    /**
     * Retrieves the next chunk of elements from the source.
     */
    void loadNext() {
        limit = source->load(&buffer[0], BUFFER_SIZE);
        cur = 0;
    }
};

/**
 * A partitioned stream is a list of streams each covering a disjoint subset
 * of a specific range. The individual subsets may be processed in parallel.
 */
class PartitionedStream {
    // The internally owned list of streams maintaining a partition of the
    // overall iteration range.
    std::vector<Stream> streams;

public:
    using iterator = typename std::vector<Stream>::iterator;

    PartitionedStream(std::vector<Stream>&& streams) : streams(std::move(streams)) {}

    // -- allow PartitionStreams to be processed by for-loops --

    iterator begin() {
        return streams.begin();
    }

    iterator end() {
        return streams.end();
    }
};

/**
 * A view on a relation caching local access patterns (not thread safe!).
 * Each thread should create and use its own view for accessing relations
 * to exploit access patterns via operation hints.
 */
class IndexView {
public:
    /**
     * Tests whether the given entry is contained in this index.
     */
    virtual bool contains(const TupleRef& entry) const = 0;

    /**
     * Tests whether any element in the given range is contained in this index.
     */
    virtual bool contains(const TupleRef& low, const TupleRef& high) const = 0;

    /**
     * Obtains a stream for the given range within this index.
     */
    virtual Stream range(const TupleRef& low, const TupleRef& high) const = 0;

    /**
     * Return arity size of the index
     */
    virtual size_t getArity() const = 0;

    virtual ~IndexView() = default;
};

// A general handler type for index views.
using IndexViewPtr = Own<IndexView>;

/**
 * An index is an abstraction of a data structure
 */
class InterpreterIndex {
public:
    virtual ~InterpreterIndex() = default;

    /**
     * Requests the creation of a view on this index.
     */
    virtual IndexViewPtr createView() const = 0;

    /**
     * Obtains the arity of the given index.
     */
    virtual size_t getArity() const = 0;

    /**
     * Tests whether this index is empty or not.
     */
    virtual bool empty() const = 0;

    /**
     * Obtains the number of elements stored in this index.
     */
    virtual std::size_t size() const = 0;

    /**
     * Inserts a tuple into this index.
     */
    virtual bool insert(const TupleRef& tuple) = 0;

    /**
     * Inserts all elements of the given index.
     */
    virtual void insert(const InterpreterIndex& src) = 0;

    /**
     * Tests whether the given tuple is present in this index or not.
     */
    virtual bool contains(const TupleRef& tuple) const = 0;

    /**
     * Tests whether this index contains any tuple within the given bounds.
     */
    virtual bool contains(const TupleRef& low, const TupleRef& high) const = 0;

    /**
     * Returns a stream covering the entire index content.
     */
    virtual Stream scan() const = 0;

    /**
     * Returns a partitioned stream covering the entire index content.
     */
    virtual PartitionedStream partitionScan(int partitionCount) const = 0;

    /**
     * Returns a stream covering elements in the range [low,high)
     */
    virtual Stream range(const TupleRef& low, const TupleRef& high) const = 0;

    /**
     * Returns a partitioned stream covering elements in the range [low,high)
     */
    virtual PartitionedStream partitionRange(
            const TupleRef& low, const TupleRef& high, int partitionCount) const = 0;

    /**
     * Clears the content of this index, turning it empty.
     */
    virtual void clear() = 0;

    /**
     * Extend another index.
     *
     * This should only affect on an EqrelIndex.
     * Extend this index with another index, expanding this equivalence relation.
     * The supplied relation is the old knowledge, whilst this relation only contains
     * explicitly new knowledge. After this operation the "implicitly new tuples" are now
     * explicitly inserted this relation.
     */
    virtual void extend(InterpreterIndex*) {}
};

/**
 * A namespace enclosing utilities required by indices.
 */
namespace index_utils {

// -------- generic tuple comparator ----------

template <unsigned... Columns>
struct comparator;

template <unsigned First, unsigned... Rest>
struct comparator<First, Rest...> {
    template <typename T>
    int operator()(const T& a, const T& b) const {
        return (a[First] < b[First]) ? -1 : ((a[First] > b[First]) ? 1 : comparator<Rest...>()(a, b));
    }
    template <typename T>
    bool less(const T& a, const T& b) const {
        return a[First] < b[First] || (a[First] == b[First] && comparator<Rest...>().less(a, b));
    }
    template <typename T>
    bool equal(const T& a, const T& b) const {
        return a[First] == b[First] && comparator<Rest...>().equal(a, b);
    }
};

template <>
struct comparator<> {
    template <typename T>
    int operator()(const T&, const T&) const {
        return 0;
    }
    template <typename T>
    bool less(const T&, const T&) const {
        return false;
    }
    template <typename T>
    bool equal(const T&, const T&) const {
        return true;
    }
};

}  // namespace index_utils

/**
 * The index class is utilized as a template-meta-programming structure
 * to specify and realize indices.
 *
 * @tparam Columns ... the order in which elements of the relation to be indexed
 * 				shell be considered by this index.
 */
template <unsigned... Columns>
struct index {
    // the comparator associated to this index
    using comparator = index_utils::comparator<Columns...>;
};

/**
 * A namespace enclosing utilities required relations to handle indices.
 */
namespace index_utils {

// -- a utility extending a given index by another column --
//   e.g. index<1,0>   =>    index<1,0,2>

template <typename Index, unsigned column>
struct extend;

template <unsigned... Columns, unsigned Col>
struct extend<index<Columns...>, Col> {
    using type = index<Columns..., Col>;
};

// -- obtains a full index for a given arity --

template <unsigned arity>
struct get_full_index {
    using type = typename extend<typename get_full_index<arity - 1>::type, arity - 1>::type;
};

template <>
struct get_full_index<0> {
    using type = index<>;
};

}  // namespace index_utils

/**
 * An index wrapper for nullary indexes. For those, no complex
 * nested data structure is required.
 */
class NullaryIndex : public InterpreterIndex {
    // indicates whether the one single element is present or not.
    std::atomic<bool> present = false;

    // a source adaptation, iterating through the optionally present
    // entry in this relation.
    class Source : public Stream::Source {
        bool present;

    public:
        Source(bool present) : present(present) {}
        int load(TupleRef* buffer, int /* max */) override {
            if (!present) {
                return 0;
            }
            buffer[0] = TupleRef(nullptr, 0);
            present = false;
            return 1;
        }

        int reload(TupleRef* buffer, int /* max */) override {
            if (!present) {
            }
            buffer[0] = TupleRef(nullptr, 0);
            return 1;
        }

        Own<Stream::Source> clone() override {
            return mk<Source>(present);
        }
    };

    // The nullary index view -- does not require any hints.
    struct NullaryIndexView : public IndexView {
        const NullaryIndex& index;

        NullaryIndexView(const NullaryIndex& index) : index(index) {}

        bool contains(const TupleRef& entry) const override {
            return index.contains(entry);
        }

        bool contains(const TupleRef& low, const TupleRef& high) const override {
            return index.contains(low, high);
        }

        Stream range(const TupleRef& low, const TupleRef& high) const override {
            return index.range(low, high);
        }

        size_t getArity() const override {
            return 0;
        }
    };

public:
    size_t getArity() const override {
        return 0;
    }

    bool empty() const override {
        return !present;
    }

    std::size_t size() const override {
        return present ? 1 : 0;
    }

    IndexViewPtr createView() const override {
        return mk<NullaryIndexView>(*this);
    }

    bool insert(const TupleRef& tuple) override {
        assert(tuple.size() == 0);
        bool res = present;
        present = true;
        return res;
    }

    void insert(const InterpreterIndex& src) override {
        assert(src.getArity() == 0);
        present = present | !src.empty();
    }

    bool contains(const TupleRef& tuple) const override {
        assert(tuple.size() == 0);
        return present;
    }

    bool contains(const TupleRef&, const TupleRef&) const override {
        return present;
    }

    Stream scan() const override {
        return mk<Source>(present);
    }

    PartitionedStream partitionScan(int) const override {
        std::vector<Stream> res;
        res.push_back(scan());
        return res;
    }

    Stream range(const TupleRef& /* low */, const TupleRef& /* high */) const override {
        return scan();
    }

    PartitionedStream partitionRange(const TupleRef& low, const TupleRef& high, int) const override {
        std::vector<Stream> res;
        res.push_back(range(low, high));
        return res;
    }

    void clear() override {
        present = false;
    }
};

/**
 * A generic data structure index adapter handling the boundary
 * level order conversion as well as iteration through nested
 * data structures.
 *
 * @tparam Structure the structure to be utilized
 */
template <typename Structure>
class GenericIndex : public InterpreterIndex {
protected:
    using Entry = typename Structure::element_type;
    using Hints = typename Structure::operation_hints;
    static constexpr int Arity = Entry::arity;

    // the order to be simulated
    Order order;

    // the internal data structure
    Structure data;

    using iter = typename Structure::iterator;

    // a source adapter for streaming through data
    class Source : public Stream::Source {
        const Order& order;

        // the begin and end of the stream
        iter cur;
        iter end;

        // an internal buffer for re-ordered elements
        std::array<Entry, Stream::BUFFER_SIZE> buffer;

    public:
        Source(const Order& order, iter begin, iter end)
                : order(order), cur(std::move(begin)), end(std::move(end)) {}

        int load(TupleRef* out, int max) override {
            int c = 0;
            while (cur != end && c < max) {
                buffer[c] = order.decode(*cur);
                out[c] = buffer[c];
                ++cur;
                ++c;
            }
            return c;
        }

        int reload(TupleRef* out, int max) override {
            int c = 0;
            max = std::min(max, Stream::BUFFER_SIZE);
            while (c < max) {
                out[c] = buffer[c];
                ++c;
            }
            return c;
        }

        Own<Stream::Source> clone() override {
            auto source = mk<Source>(order, cur, end);
            source->buffer = this->buffer;
            return source;
        }
    };

    virtual souffle::range<iter> bounds(const TupleRef& low, const TupleRef& high, Hints& hints) const {
        Entry a = order.encode(low.asTuple<Arity>());
        Entry b = order.encode(high.asTuple<Arity>());
        return {data.lower_bound(a, hints), data.upper_bound(b, hints)};
    }

    // The index view associated to this view type.
    struct GenericIndexView : public IndexView {
        const GenericIndex& index;
        mutable Hints hints;

        GenericIndexView(const GenericIndex& index) : index(index) {}

        bool contains(const TupleRef& tuple) const override {
            return index.data.contains(index.order.encode(tuple.asTuple<Arity>()), hints);
        }

        bool contains(const TupleRef& low, const TupleRef& high) const override {
            return !index.bounds(low, high, hints).empty();
        }

        Stream range(const TupleRef& low, const TupleRef& high) const override {
            auto range = index.bounds(low, high, hints);
            return mk<Source>(index.order, range.begin(), range.end());
        }

        size_t getArity() const override {
            return Arity;
        }
    };

public:
    GenericIndex(Order order) : order(std::move(order)) {}

    IndexViewPtr createView() const override {
        return mk<GenericIndexView>(*this);
    }

    size_t getArity() const override {
        return Arity;
    }

    bool empty() const override {
        return data.empty();
    }

    std::size_t size() const override {
        return data.size();
    }

    bool insert(const TupleRef& tuple) override {
        return data.insert(order.encode(tuple.asTuple<Arity>()));
    }

    void insert(const InterpreterIndex& src) override {
        // TODO: make smarter
        for (const auto& cur : src.scan()) {
            insert(cur);
        }
    }

    bool contains(const TupleRef& tuple) const override {
        return GenericIndexView(*this).contains(tuple);
    }

    bool contains(const TupleRef& low, const TupleRef& high) const override {
        return GenericIndexView(*this).contains(low, high);
    }

    Stream scan() const override {
        return mk<Source>(order, data.begin(), data.end());
    }

    PartitionedStream partitionScan(int partitionCount) const override {
        auto chunks = data.partition(partitionCount);
        std::vector<Stream> res;
        res.reserve(chunks.size());
        for (const auto& cur : chunks) {
            res.push_back(mk<Source>(order, cur.begin(), cur.end()));
        }
        return res;
    }

    Stream range(const TupleRef& low, const TupleRef& high) const override {
        return GenericIndexView(*this).range(low, high);
    }

    PartitionedStream partitionRange(
            const TupleRef& low, const TupleRef& high, int partitionCount) const override {
        Hints hints;
        auto range = bounds(low, high, hints);
        std::vector<Stream> res;
        res.reserve(partitionCount);
        for (const auto& cur : range.partition(partitionCount)) {
            res.push_back(mk<Source>(order, cur.begin(), cur.end()));
        }
        return res;
    }

    void clear() override {
        data.clear();
    }
};

// The type of index factory functions.
using IndexFactory = Own<InterpreterIndex> (*)(const Order&);

// A factory for BTree based index.
Own<InterpreterIndex> createBTreeIndex(const Order&);

// A factory for BTree provenance index.
Own<InterpreterIndex> createBTreeProvenanceIndex(const Order&);

// A factory for Brie based index.
Own<InterpreterIndex> createBrieIndex(const Order&);

// A factory for indirect index.
Own<InterpreterIndex> createIndirectIndex(const Order&);

// A factory for Eqrel index.
Own<InterpreterIndex> createEqrelIndex(const Order&);

}  // end of namespace souffle
