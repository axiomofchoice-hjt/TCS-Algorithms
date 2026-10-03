#pragma once

#include <algorithm>
#include <bit>
#include <climits>
#include <cstdint>
#include <format>
#include <functional>
#include <iterator>
#include <source_location>
#include <stdexcept>
#include <string_view>
#include <vector>

namespace tcs::ds::compact_bit_vector {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

constexpr int64_t n_machine_word_bits = sizeof(uint64_t) * CHAR_BIT;

inline int64_t ceil_log2(int64_t x) {
    assert_or_throw(x > 0, "ceil_log2: argument must be positive");
    return std::bit_width(static_cast<uint64_t>(x) - 1);
}

struct BitVector {
    int64_t n_word_bits_ = 0;
    int64_t size_ = 0;
    std::vector<uint64_t> data_;

    static uint64_t low_mask(int64_t len) {
        assert_or_throw(len >= 0 && len <= n_machine_word_bits);
        return len == n_machine_word_bits ? ~uint64_t{0} : (uint64_t{1} << len) - 1;
    }

    static BitVector create(int64_t n_word_bits) {
        assert_or_throw(n_word_bits > 0 && n_word_bits <= n_machine_word_bits);
        return {.n_word_bits_ = n_word_bits, .size_ = 0, .data_ = {}};
    }

    bool get(int64_t index) const {
        assert_or_throw(index >= 0 && index < size_);
        return (data_[index / n_word_bits_] >> (index % n_word_bits_) & 1) == 1;
    }

    void set(int64_t index, bool value) {
        assert_or_throw(index >= 0 && index < size_);
        uint64_t& word = data_[index / n_word_bits_];
        uint64_t mask = uint64_t{1} << (index % n_word_bits_);
        word = value ? word | mask : word & ~mask;
    }

    uint64_t get_range(int64_t l, int64_t r) const {
        assert_or_throw(l >= 0 && l <= r && r <= size_);
        assert_or_throw(r - l <= n_word_bits_);
        if (l == r) {
            return 0;
        }
        int64_t off = l % n_word_bits_;
        int64_t n_low = n_word_bits_ - off;
        int64_t len = r - l;
        uint64_t low = data_[l / n_word_bits_] >> off;
        if (len <= n_low) {
            return low & low_mask(len);
        }
        return (low & low_mask(n_low)) | (data_[r / n_word_bits_] & low_mask(len - n_low)) << n_low;
    }

    void set_range(int64_t l, int64_t r, uint64_t value) {
        assert_or_throw(l >= 0 && l <= r && r <= size_);
        assert_or_throw(r - l <= n_word_bits_);
        assert_or_throw(std::bit_width(value) <= r - l);
        if (l == r) {
            return;
        }
        int64_t off = l % n_word_bits_;
        int64_t n_low = n_word_bits_ - off;
        uint64_t& low_word = data_[l / n_word_bits_];
        if (r - l <= n_low) {
            low_word = (low_word & ~(low_mask(r - l) << off)) | (value << off);
        } else {
            low_word = ((low_word & low_mask(off)) | (value << off)) & low_mask(n_word_bits_);
            uint64_t& high_word = data_[r / n_word_bits_];
            high_word = (high_word & ~low_mask(r - l - n_low)) | (value >> n_low);
        }
    }

    void push_back(bool value) {
        size_++;
        if (static_cast<int64_t>(data_.size()) * n_word_bits_ < size_) {
            data_.push_back(0);
        }
        assert_or_throw(static_cast<int64_t>(data_.size()) * n_word_bits_ >= size_);
        set(size_ - 1, value);
    }

    void pop_back() {
        assert_or_throw(size_ > 0);
        set(size_ - 1, false);
        size_--;
    }

    void push_back_range(uint64_t value, int64_t n_bits) {
        assert_or_throw(n_bits >= 0 && n_bits <= n_word_bits_);
        size_ += n_bits;
        if (static_cast<int64_t>(data_.size()) * n_word_bits_ < size_) {
            data_.push_back(0);
        }
        assert_or_throw(static_cast<int64_t>(data_.size()) * n_word_bits_ >= size_);
        set_range(size_ - n_bits, size_, value);
    }

    void pop_back_range(int64_t n_bits) {
        assert_or_throw(n_bits >= 0 && n_bits <= n_word_bits_);
        assert_or_throw(size_ >= n_bits);
        set_range(size_ - n_bits, size_, 0);
        size_ -= n_bits;
    }
};

struct PackedVector {
    int64_t n_element_bits_ = 0;
    BitVector data_;

    static PackedVector create(int64_t n_element_bits, int64_t n_word_bits) {
        assert_or_throw(n_word_bits > 0 && n_word_bits <= n_machine_word_bits);
        assert_or_throw(n_element_bits > 0 && n_element_bits <= n_word_bits);
        return {.n_element_bits_ = n_element_bits, .data_ = BitVector::create(n_word_bits)};
    }

    uint64_t get(int64_t block_index) const {
        assert_or_throw(block_index >= 0 && block_index < size());
        return data_.get_range(block_index * n_element_bits_, (block_index + 1) * n_element_bits_);
    }

    void set(int64_t block_index, uint64_t value) {
        assert_or_throw(block_index >= 0 && block_index < size());
        data_.set_range(block_index * n_element_bits_, (block_index + 1) * n_element_bits_, value);
    }

    void push_back(uint64_t value) { data_.push_back_range(value, n_element_bits_); }

    void pop_back() { data_.pop_back_range(n_element_bits_); }

    int64_t size() const { return data_.size_ / n_element_bits_; }
};

struct RankIndexer {
    int64_t count_ = 0;
    int64_t n_block_bits_ = 0;
    PackedVector block_rank_;

    static RankIndexer create(const BitVector& data) {
        int64_t size = data.size_;
        int64_t n_word_bits = data.n_word_bits_;
        int64_t logn = std::max(ceil_log2(std::max(size, int64_t{1})), int64_t{1});
        assert_or_throw(logn <= n_word_bits, "n_word_bits must be at least ceil_log2(size)");
        int64_t n_block_bits = std::max(logn / 2, int64_t{1});
        int64_t n_index_bits = logn;

        auto block_rank = PackedVector::create(n_index_bits, n_word_bits);
        int64_t count = 0;
        for (int64_t i = 0; i < size; i++) {
            bool value = data.get(i);
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
        int64_t index, const BitVector& data, const PackedVector& popcount_table) const {
        assert_or_throw(index >= 0 && index <= data.size_);
        if (index == data.size_) {
            return count_;
        }
        int64_t range =
            static_cast<int64_t>(data.get_range(index / n_block_bits_ * n_block_bits_, index));
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
    BitVector compact_;
    PackedVector select_table_;

    static SelectIndexer create(const BitVector& data) {
        int64_t n_word_bits = data.n_word_bits_;
        int64_t size = data.size_;
        int64_t logn = std::max(ceil_log2(std::max(size, int64_t{1})), int64_t{1});
        assert_or_throw(logn <= n_word_bits, "n_word_bits must be at least ceil_log2(size)");
        int64_t n_index_bits = logn;
        int64_t sparse_threshold = logn * logn;
        int64_t n_ones_per_segment = logn;
        int64_t count = 0;
        for (int64_t i = 0; i < size; i++) {
            count += int64_t{data.get(i)};
        }

        auto compact_offsets = PackedVector::create(n_index_bits, n_word_bits);
        auto compact = BitVector::create(n_word_bits);
        int64_t index = 0;
        PackedVector segment = PackedVector::create(n_index_bits, n_word_bits);
        for (int64_t i = 0; i < count; i++) {
            while (index < size && !data.get(index)) {
                index++;
            }
            segment.push_back(index);
            if ((i + 1) % n_ones_per_segment == 0 || i + 1 == count) {
                assert_or_throw(compact.size_ / n_align_bits <= (int64_t{1} << n_index_bits) - 1,
                    "segment offset does not fit in n_index_bits");
                compact_offsets.push_back(compact.size_ / n_align_bits);
                int64_t span =
                    static_cast<int64_t>(segment.get(segment.size() - 1) - segment.get(0) + 1);
                compact.push_back_range(segment.get(0), n_index_bits);
                if (span >= sparse_threshold) {
                    compact.push_back(true);
                    for (int64_t j = 0; j < segment.size(); j++) {
                        compact.push_back_range(segment.get(j) - segment.get(0), n_index_bits);
                    }
                } else {
                    compact.push_back(false);
                    int64_t n_span_bits = ceil_log2(span);
                    int64_t n_low_bits =
                        ceil_log2((span + n_ones_per_segment - 1) / n_ones_per_segment);
                    int64_t high_len = (int64_t{1} << (n_span_bits - n_low_bits)) + segment.size();
                    compact.push_back_range(n_span_bits, n_index_bits);
                    compact.push_back_range(n_low_bits, n_index_bits);
                    for (int64_t j = 0; j < high_len; j++) {
                        compact.push_back(false);
                    }
                    for (int64_t j = 0; j < segment.size(); j++) {
                        int64_t value =
                            static_cast<int64_t>(segment.get(j) - segment.get(0)) >> n_low_bits;
                        compact.set(compact.size_ - high_len + j + value, true);
                    }
                    for (int64_t j = 0; j < segment.size(); j++) {
                        int64_t value = static_cast<int64_t>(segment.get(j) - segment.get(0)) &
                                        ((int64_t{1} << n_low_bits) - 1);
                        compact.push_back_range(value, n_low_bits);
                    }
                }
                while (compact.size_ % n_align_bits != 0) {
                    compact.push_back(false);
                }

                segment = PackedVector::create(n_index_bits, n_word_bits);
            }
            index++;
        }
        int64_t n_select_table_bits = std::max(logn / 2, int64_t{1});
        auto select_table = PackedVector::create(ceil_log2(n_select_table_bits + 1), n_word_bits);
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
        assert_or_throw(k >= 0 && k < count_);
        int64_t offset =
            static_cast<int64_t>(compact_offsets_.get(k / n_ones_per_segment_)) * n_align_bits;
        int64_t segment_first =
            static_cast<int64_t>(compact_.get_range(offset, offset + n_index_bits_));
        offset += n_index_bits_;
        bool is_sparse = compact_.get(offset);
        offset++;
        if (is_sparse) {
            offset += k % n_ones_per_segment_ * n_index_bits_;
            return segment_first +
                   static_cast<int64_t>(compact_.get_range(offset, offset + n_index_bits_));
        }
        int64_t n_span_bits =
            static_cast<int64_t>(compact_.get_range(offset, offset + n_index_bits_));
        offset += n_index_bits_;
        int64_t n_low_bits =
            static_cast<int64_t>(compact_.get_range(offset, offset + n_index_bits_));
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
            uint64_t chunk = compact_.get_range(offset + i, offset + end);
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
        assert_or_throw(found, "select: segment high bits are inconsistent");
        offset += high_len;
        offset += k % n_ones_per_segment_ * n_low_bits;
        int64_t local_low = static_cast<int64_t>(compact_.get_range(offset, offset + n_low_bits));
        return segment_first + ((local_high << n_low_bits) | local_low);
    }
};

struct CompactBitVector {
    BitVector data_;
    PackedVector popcount_table_;
    RankIndexer rank_indexer_;
    SelectIndexer select_indexer_;

    template <typename ForwardIt, typename Proj = std::identity>
    static CompactBitVector create(
        ForwardIt first, ForwardIt last, int64_t n_word_bits, Proj proj = {}) {
        int64_t size = std::distance(first, last);
        auto data = BitVector::create(n_word_bits);
        for (int64_t i = 0; i < size; i++) {
            bool value = proj(*first);
            data.push_back(value);
            first++;
        }

        int64_t logn = std::max(ceil_log2(std::max(size, int64_t{1})), int64_t{1});
        int64_t n_block_bits = std::max(logn / 2, int64_t{1});
        auto popcount_table = PackedVector::create(logn, n_word_bits);
        popcount_table.push_back(0);
        for (int64_t i = 1; i < (int64_t{1} << n_block_bits); i++) {
            popcount_table.push_back(popcount_table.get(i >> 1) + (i & 1));
        }

        auto rank_indexer = RankIndexer::create(data);
        auto select_indexer = SelectIndexer::create(data);
        return {
            .data_ = data,
            .popcount_table_ = popcount_table,
            .rank_indexer_ = rank_indexer,
            .select_indexer_ = select_indexer,
        };
    }

    bool get(int64_t index) const { return data_.get(index); }
    int64_t rank(int64_t index) const { return rank_indexer_(index, data_, popcount_table_); }
    int64_t select(int64_t k) const { return select_indexer_(k, popcount_table_); }
};
}  // namespace tcs::ds::compact_bit_vector
