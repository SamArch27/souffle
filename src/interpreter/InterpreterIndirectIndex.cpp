/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2019, The Souffle Developers. All rights reserved.
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file InterpreterIndirectIndex.cpp
 *
 * Interpreter index with generic interface.
 *
 ***********************************************************************/

#include "interpreter/InterpreterIndex.h"
#include "souffle/datastructure/BTree.h"
#include "souffle/utility/MiscUtil.h"
#include <algorithm>
#include <array>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <ostream>
#include <utility>
#include <vector>

namespace souffle {

/* B-Tree Indirect indexes */
class IndirectIndex : public InterpreterIndex {
public:
    using AttributeIndex = uint32_t;
    using AttributeOrder = std::vector<AttributeIndex>;
    /* lexicographical comparison operation on two tuple pointers */
    struct comparator {
        const AttributeOrder order;

        /* constructor to initialize state */
        comparator(AttributeOrder order) : order(std::move(order)) {}

        /* comparison function */
        int operator()(const TupleRef& x, const TupleRef& y) const {
            for (auto& i : order) {
                if (x[i] < y[i]) {
                    return -1;
                }
                if (x[i] > y[i]) {
                    return 1;
                }
            }
            return 0;
        }

        /* less comparison */
        bool less(const TupleRef& x, const TupleRef& y) const {
            return operator()(x, y) < 0;
        }

        /* equal comparison */
        bool equal(const TupleRef& x, const TupleRef& y) const {
            for (auto& i : order) {
                if (x[i] != y[i]) {
                    return false;
                }
            }
            return true;
        }
    };

    /* btree for storing tuple pointers with a given lexicographical order */
    using index_set = btree_multiset<TupleRef, comparator, std::allocator<TupleRef>, 512>;
    using Hints = typename index_set::operation_hints;

    class Source : public Stream::Source {
        // the begin and end of the stream
        using iter = btree_multiset<TupleRef, comparator, std::allocator<TupleRef>, 512>::iterator;
        iter cur;
        iter end;

        // an internal buffer for re-ordered elements
        std::array<TupleRef, Stream::BUFFER_SIZE> buffer;

    public:
        Source(iter begin, iter end) : cur(begin), end(end) {}

        int load(TupleRef* out, int max) override {
            int c = 0;
            while (cur != end && c < max) {
                buffer[c] = *cur;
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
            auto* source = new Source(cur, end);
            source->buffer = this->buffer;
            return Own<Stream::Source>(source);
        }
    };

    // The index view associated to this view type.
    struct IndirectIndexView : public IndexView {
        const IndirectIndex& index;
        mutable Hints hints;

        IndirectIndexView(const IndirectIndex& index) : index(index) {}

        bool contains(const TupleRef& tuple) const override {
            return index.set.contains(tuple, hints);
        }

        bool contains(const TupleRef& /* low */, const TupleRef& /* high */) const override {
            fatal("Not implemented!");
        }

        Stream range(const TupleRef& low, const TupleRef& high) const override {
            return mk<Source>(index.set.lower_bound(low, hints), index.set.upper_bound(high, hints));
        }

        size_t getArity() const override {
            return index.getArity();
        }
    };

    IndirectIndex(AttributeOrder order)
            : theOrder(std::move(order)), set(comparator(theOrder), comparator(theOrder)),
              arity(order.size()) {}

    IndexViewPtr createView() const override {
        return mk<IndirectIndexView>(*this);
    }

    size_t getArity() const override {
        return arity;
    };

    bool empty() const override {
        return set.empty();
    }

    size_t size() const override {
        return set.size();
    }

    bool insert(const TupleRef& tuple) override {
        return set.insert(tuple, operation_hints);
    }

    void insert(const InterpreterIndex& src) override {
        for (const auto& cur : src.scan()) {
            insert(cur);
        }
    }

    bool contains(const TupleRef& tuple) const override {
        return IndirectIndexView(*this).contains(tuple);
    }

    bool contains(const TupleRef& low, const TupleRef& high) const override {
        return IndirectIndexView(*this).contains(low, high);
    }

    Stream scan() const override {
        return mk<Source>(set.begin(), set.end());
    }

    PartitionedStream partitionScan(int) const override {
        assert(false && "Does only produce a single subset!");
        std::vector<Stream> res;
        res.push_back(scan());
        return res;
    }

    Stream range(const TupleRef& low, const TupleRef& high) const override {
        return IndirectIndexView(*this).range(low, high);
    }

    PartitionedStream partitionRange(const TupleRef& low, const TupleRef& high, int) const override {
        assert(false && "Does only produce a single subset!");
        std::vector<Stream> res;
        res.push_back(range(low, high));
        return res;
    }

    void clear() override {
        set.clear();
    }

private:
    /** retain the index order used to construct an object of this class */
    const AttributeOrder theOrder;

    /** set storing tuple pointers of table */
    index_set set;

    /** Operation hints */
    index_set::btree_operation_hints<1> operation_hints;

    /** Arity as the relation arity, not necessary the order size in indirect index */
    size_t arity;
};

Own<InterpreterIndex> createIndirectIndex(const Order& order) {
    assert(order.size() != 0 && "IndirectIndex does not work with nullary relation\n");
    return mk<IndirectIndex>(order.getOrder());
}

}  // namespace souffle
