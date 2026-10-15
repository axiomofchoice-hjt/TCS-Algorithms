// Compact bit vector (rank/select)
// --------------------------------------------------------------------------
// Bit vector packed into machine words with O(1) rank and select and O(n) extra
// bits (not succinct). rank uses log(n)/2-bit blocks and a popcount table;
// select encodes each log(n)-one segment Elias-Fano style and decodes it with a
// lookup table.
//
// Blog: https://axiomofchoice-hjt.github.io/pages/6b2b47/

#pragma once

#include <algorithm>
#include <cstdint>
#include <functional>
#include <iterator>
#include <type_traits>

#include "tcs/basic/bit_vector.hpp"
#include "tcs/common/assert.hpp"
#include "tcs/common/bit.hpp"

namespace tcs::ds::compact_bit_vector {

struct PackedVector {
    int64_t n_element_bits_ = 0;
    basic::BitVector data_;

    static PackedVector create(int64_t n_element_bits) {
        common::assert_or_throw(n_element_bits > 0 && n_element_bits <= common::n_machine_word_bits,
            "PackedVector::create: n_element_bits must be in [1, machine word bits]");
        return {.n_element_bits_ = n_element_bits, .data_ = basic::BitVector::create()};
    }

    uint64_t get(int64_t block_index) const {
        common::assert_or_throw(block_index >= 0 && block_index < size(),
            "PackedVector::get: block index out of range");
        return data_.load(block_index * n_element_bits_, n_element_bits_);
    }

    void set(int64_t block_index, uint64_t value) {
        common::assert_or_throw(block_index >= 0 && block_index < size(),
            "PackedVector::set: block index out of range");
        data_.store(block_index * n_element_bits_, n_element_bits_, value);
    }

    void push_back(uint64_t value) { data_.push_back(value, n_element_bits_); }

    void pop_back() { data_.pop_back(n_element_bits_); }

    int64_t size() const { return data_.size_ / n_element_bits_; }
};

struct RankIndexer {
    int64_t count_ = 0;
    int64_t n_block_bits_ = 0;
    PackedVector block_rank_;

    static RankIndexer create(const basic::BitVector& data) {
        int64_t size = data.size_;
        int64_t logn = std::max(common::ceil_log2(std::max(size, int64_t{1})), int64_t{1});
        int64_t n_block_bits = std::max(logn / 2, int64_t{1});
        int64_t n_index_bits = logn;

        auto block_rank = PackedVector::create(n_index_bits);
        int64_t count = 0;
        for (int64_t i = 0; i < size; i++) {
            bool value = data.load(i);
            if (i % n_block_bits == 0) {
                block_rank.push_back(count);
            }
            count += int64_t{value};
        }
        return {
            .count_ = count,
            .n_block_bits_ = n_block_bits,
            .block_rank_ = block_rank,
        };
    }

    int64_t operator()(
        int64_t index, const basic::BitVector& data, const PackedVector& popcount_table) const {
        common::assert_or_throw(
            index >= 0 && index <= data.size_, "RankIndexer: index out of range");
        if (index == data.size_) {
            return count_;
        }
        int64_t range =
            static_cast<int64_t>(data.load(index - (index % n_block_bits_), index % n_block_bits_));
        return static_cast<int64_t>(
            block_rank_.get(index / n_block_bits_) + popcount_table.get(range));
    }
};

struct SelectIndexer {
    static constexpr int64_t n_align_bits = 8;
    int64_t count_ = 0;
    int64_t n_ones_per_segment_ = 0;
    int64_t n_index_bits_ = 0;
    int64_t n_select_table_bits_ = 0;

    PackedVector compact_offsets_;
    basic::BitVector compact_;
    PackedVector select_table_;

    static SelectIndexer create(const basic::BitVector& data) {
        int64_t size = data.size_;
        int64_t logn = std::max(common::ceil_log2(std::max(size, int64_t{1})), int64_t{1});
        int64_t n_index_bits = logn;
        int64_t n_ones_per_segment = logn;
        int64_t count = 0;
        for (int64_t i = 0; i < size; i++) {
            count += int64_t{data.load(i)};
        }

        auto compact_offsets = PackedVector::create(n_index_bits);
        auto compact = basic::BitVector::create();
        int64_t index = 0;
        PackedVector segment = PackedVector::create(n_index_bits);
        for (int64_t i = 0; i < count; i++) {
            while (index < size && !data.load(index)) {
                index++;
            }
            segment.push_back(index);
            if ((i + 1) % n_ones_per_segment == 0 || i + 1 == count) {
                common::assert_or_throw(
                    compact.size_ / n_align_bits <= (int64_t{1} << n_index_bits) - 1,
                    "SelectIndexer: segment offset does not fit in n_index_bits");
                compact_offsets.push_back(compact.size_ / n_align_bits);
                int64_t span =
                    static_cast<int64_t>(segment.get(segment.size() - 1) - segment.get(0) + 1);
                compact.push_back(segment.get(0), n_index_bits);
                int64_t n_span_bits = common::ceil_log2(span);
                int64_t n_low_bits =
                    common::ceil_log2((span + n_ones_per_segment - 1) / n_ones_per_segment);
                int64_t high_len = (int64_t{1} << (n_span_bits - n_low_bits)) + segment.size();
                compact.push_back(n_span_bits, n_index_bits);
                compact.push_back(n_low_bits, n_index_bits);
                for (int64_t j = 0; j < high_len; j++) {
                    compact.push_back(false);
                }
                for (int64_t j = 0; j < segment.size(); j++) {
                    int64_t value =
                        static_cast<int64_t>(segment.get(j) - segment.get(0)) >> n_low_bits;
                    compact.store(compact.size_ - high_len + j + value, true);
                }
                for (int64_t j = 0; j < segment.size(); j++) {
                    int64_t value = static_cast<int64_t>(segment.get(j) - segment.get(0)) &
                                    ((int64_t{1} << n_low_bits) - 1);
                    compact.push_back(value, n_low_bits);
                }
                while (compact.size_ % n_align_bits != 0) {
                    compact.push_back(false);
                }

                segment = PackedVector::create(n_index_bits);
            }
            index++;
        }
        int64_t n_select_table_bits = std::max(logn / 2, int64_t{1});
        auto select_table = PackedVector::create(common::ceil_log2(n_select_table_bits + 1));
        for (int64_t i = 0; i < (int64_t{1} << n_select_table_bits); i++) {
            int64_t k = 0;
            for (int64_t j = 0; j < n_select_table_bits; j++) {
                if (((i >> j) & 1) == 1) {
                    select_table.push_back(j);
                    k++;
                }
            }
            while (k < n_select_table_bits) {
                select_table.push_back(n_select_table_bits);
                k++;
            }
        }

        return {.count_ = count,
            .n_ones_per_segment_ = n_ones_per_segment,
            .n_index_bits_ = n_index_bits,
            .n_select_table_bits_ = n_select_table_bits,
            .compact_offsets_ = compact_offsets,
            .compact_ = compact,
            .select_table_ = select_table};
    }

    int64_t operator()(int64_t k, const PackedVector& popcount_table) const {
        common::assert_or_throw(k >= 0 && k < count_, "SelectIndexer: k out of range");
        int64_t offset =
            static_cast<int64_t>(compact_offsets_.get(k / n_ones_per_segment_)) * n_align_bits;
        int64_t segment_first = static_cast<int64_t>(compact_.load(offset, n_index_bits_));
        offset += n_index_bits_;
        int64_t n_span_bits = static_cast<int64_t>(compact_.load(offset, n_index_bits_));
        offset += n_index_bits_;
        int64_t n_low_bits = static_cast<int64_t>(compact_.load(offset, n_index_bits_));
        offset += n_index_bits_;
        int64_t segment_index = k / n_ones_per_segment_;
        int64_t segment_size = segment_index + 1 == compact_offsets_.size()
                                   ? count_ - (segment_index * n_ones_per_segment_)
                                   : n_ones_per_segment_;
        int64_t high_len = (int64_t{1} << (n_span_bits - n_low_bits)) + segment_size;
        int64_t local_high = 0;
        int64_t segment_rank = k % n_ones_per_segment_;
        bool found = false;
        for (int64_t i = 0; i < high_len; i += n_select_table_bits_) {
            int64_t end = std::min(i + n_select_table_bits_, high_len);
            uint64_t chunk = compact_.load(offset + i, end - i);
            int64_t ones = static_cast<int64_t>(popcount_table.get(static_cast<int64_t>(chunk)));
            if (segment_rank < ones) {
                int64_t slot = (static_cast<int64_t>(chunk) * n_select_table_bits_) + segment_rank;
                local_high += static_cast<int64_t>(select_table_.get(slot)) - segment_rank;
                found = true;
                break;
            }
            segment_rank -= ones;
            local_high += end - i - ones;
        }
        common::assert_or_throw(found, "SelectIndexer: segment high bits are inconsistent");
        offset += high_len;
        offset += k % n_ones_per_segment_ * n_low_bits;
        int64_t local_low = static_cast<int64_t>(compact_.load(offset, n_low_bits));
        return segment_first + ((local_high << n_low_bits) | local_low);
    }
};

struct CompactBitVector {
    int64_t size_ = 0;
    int64_t count_ = 0;
    basic::BitVector data_;
    PackedVector popcount_table_;
    RankIndexer rank_indexer_;
    SelectIndexer select_indexer_;

    template <typename ForwardIt, typename Proj = std::identity>
    static CompactBitVector create(ForwardIt first, ForwardIt last, Proj proj = {}) {
        int64_t size = std::distance(first, last);
        auto data = basic::BitVector::create();
        for (int64_t i = 0; i < size; i++) {
            bool value = proj(*first);
            data.push_back(value);
            first++;
        }
        return create(data);
    }

    template <typename Placement>
    static CompactBitVector create(int64_t size, Placement placement) {
        static_assert(std::is_invocable_r_v<bool, Placement&, int64_t>);
        common::assert_or_throw(size >= 0, "CompactBitVector::create: size must not be negative");
        auto data = basic::BitVector::create();
        for (int64_t i = 0; i < size; i++) {
            data.push_back(placement(i));
        }
        return create(data);
    }

    static CompactBitVector create(const basic::BitVector& data) {
        int64_t size = data.size_;
        int64_t logn = std::max(common::ceil_log2(std::max(size, int64_t{1})), int64_t{1});
        int64_t n_block_bits = std::max(logn / 2, int64_t{1});
        auto popcount_table = PackedVector::create(logn);
        popcount_table.push_back(0);
        for (int64_t i = 1; i < (int64_t{1} << n_block_bits); i++) {
            popcount_table.push_back(popcount_table.get(i >> 1) + (i & 1));
        }

        auto rank_indexer = RankIndexer::create(data);
        auto select_indexer = SelectIndexer::create(data);
        return {
            .size_ = size,
            .count_ = rank_indexer.count_,
            .data_ = data,
            .popcount_table_ = popcount_table,
            .rank_indexer_ = rank_indexer,
            .select_indexer_ = select_indexer,
        };
    }

    bool get(int64_t index) const { return data_.load(index); }
    int64_t rank(int64_t index) const { return rank_indexer_(index, data_, popcount_table_); }
    int64_t select(int64_t k) const { return select_indexer_(k, popcount_table_); }
    int64_t size() const { return size_; }
    int64_t count() const { return count_; }
};
}  // namespace tcs::ds::compact_bit_vector
