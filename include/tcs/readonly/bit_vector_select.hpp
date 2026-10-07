// Select by bit vectors (read-only order statistic)
// --------------------------------------------------------------------------
// Returns an iterator to the k-th smallest element of a random-access range,
// read-only. A wavelet stack of rank/select bit vectors tracks the remaining
// candidates; each round a median-of-medians pivot splits them below / at /
// above, and the pivot always leaves the candidate set. Ties break by position,
// so the result is the element a stable sort would place at k.
//
// Time-space complexity: O(n log n) time, O(n) bits of extra space under
// TCS_NO_TEMP_IMPL (O(n) words otherwise).
//
// Blog:

#pragma once

#include <algorithm>
#include <bit>
#include <climits>
#include <cstdint>
#include <format>
#include <functional>
#include <source_location>
#include <stdexcept>
#include <string_view>
#include <type_traits>
#include <utility>
#include <vector>

#ifdef TCS_NO_TEMP_IMPL
#include "tcs/ds/compact_bit_vector.hpp"
#endif

namespace tcs::readonly::bit_vector_select {
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

#ifdef TCS_NO_TEMP_IMPL
using BitVectorType = tcs::ds::compact_bit_vector::CompactBitVector;
#else
struct BitVectorStub {
    int64_t size_;
    int64_t count_;
    std::vector<bool> data_;
    std::vector<int64_t> rank_;
    std::vector<int64_t> select_;

    template <typename Placement>
    static BitVectorStub create(
        int64_t size, Placement placement, [[maybe_unused]] int64_t n_word_bits) {
        static_assert(std::is_invocable_r_v<bool, Placement&, int64_t>);
        assert_or_throw(size >= 0);
        assert_or_throw(n_word_bits > 0 && n_word_bits <= n_machine_word_bits);
        std::vector<bool> data;
        std::vector<int64_t> rank;
        std::vector<int64_t> select;
        int64_t count = 0;
        for (int64_t i = 0; i < size; i++) {
            bool value = placement(i);
            data.push_back(value);
            rank.push_back(count);
            if (value) {
                count++;
                select.push_back(i);
            }
        }
        return {.size_ = size, .count_ = count, .data_ = data, .rank_ = rank, .select_ = select};
    }
    bool get(int64_t index) const {
        assert_or_throw(index >= 0 && index < size_);
        return data_[index];
    }
    int64_t size() const { return size_; }
    int64_t count() const { return count_; }
    int64_t rank(int64_t index) const {
        assert_or_throw(index >= 0 && index <= size_);
        return index == size_ ? count_ : rank_[index];
    }
    int64_t select(int64_t k) const {
        assert_or_throw(k >= 0 && k < count_);
        return select_[k];
    }
};
using BitVectorType = BitVectorStub;
#endif

struct WaveletStack {
    int64_t size_ = 0;
    int64_t n_word_bits_ = 0;
    std::vector<BitVectorType> stack_;

    static WaveletStack create(int64_t size, int64_t n_word_bits) {
        assert_or_throw(size >= 0);
        assert_or_throw(n_word_bits > 0 && n_word_bits <= n_machine_word_bits);
        return {.size_ = size, .n_word_bits_ = n_word_bits, .stack_ = {}};
    }

    template <typename Placement>
    void update(Placement placement) {
        auto bit_vector = BitVectorType::create(
            count(),
            [this, placement](int64_t k) {
                int64_t index = select(k);
                return placement(index);
            },
            n_word_bits_);
        stack_.push_back(bit_vector);
    }

    bool get(int64_t index) const {
        assert_or_throw(index >= 0 && index < size_);
        for (const auto& bit_vector : stack_) {
            if (!bit_vector.get(index)) {
                return false;
            }
            index = bit_vector.rank(index);
        }
        return true;
    }

    int64_t size() const { return size_; }
    int64_t count() const { return stack_.empty() ? size_ : stack_.back().count(); }

    int64_t rank(int64_t index) const {
        assert_or_throw(index >= 0 && index <= size_);
        for (const auto& bit_vector : stack_) {
            index = bit_vector.rank(index);
        }
        return index;
    }

    int64_t select(int64_t k) const {
        if (stack_.empty()) {
            assert_or_throw(k >= 0 && k < size_);
        }
        for (auto it = stack_.rbegin(); it != stack_.rend(); ++it) {
            k = it->select(k);
        }
        return k;
    }
};

template <typename BitVector, typename RandomIt, typename IterProj>
RandomIt median_of_medians(const BitVector& bit_vector, RandomIt first, IterProj iter_proj) {
    int64_t size = bit_vector.size();
    int64_t n_candidates = bit_vector.count();
    assert_or_throw(size > 0 && n_candidates > 0);
    int64_t block_size = std::max(size / std::max(ceil_log2(size), int64_t{1}), int64_t{1});
    int64_t n_blocks = (n_candidates + block_size - 1) / block_size;
    std::vector<RandomIt> medians;
    for (int64_t i = 0; i < n_blocks; i++) {
        int64_t block_start = i * block_size;
        int64_t block_end = std::min(block_start + block_size, n_candidates);
        std::vector<RandomIt> buffer;
        for (int64_t j = block_start; j < block_end; j++) {
            buffer.push_back(first + bit_vector.select(j));
        }
        int64_t mid_index = (static_cast<int64_t>(buffer.size()) - 1) / 2;
        std::ranges::nth_element(buffer, buffer.begin() + mid_index, std::less{}, iter_proj);
        medians.push_back(buffer[mid_index]);
    }
    int64_t mid_index = (static_cast<int64_t>(medians.size()) - 1) / 2;
    std::ranges::nth_element(medians, medians.begin() + mid_index, std::less{}, iter_proj);
    return medians[mid_index];
}

template <typename RandomIt, typename Proj = std::identity>
RandomIt bit_vector_select(RandomIt first, RandomIt last, int64_t k, Proj proj = {}) {
    auto iter_proj = [proj](RandomIt it) { return std::pair{proj(*it), it}; };
    assert_or_throw(first < last);
    int64_t size = last - first;
    assert_or_throw(k >= 0 && k < size);
    int64_t n_word_bits = std::max(ceil_log2(size), int64_t{1});
    auto wavelet_stack = WaveletStack::create(size, n_word_bits);
    while (true) {
        RandomIt pivot_it = median_of_medians(wavelet_stack, first, iter_proj);
        int64_t pivot_rank = 0;
        for (int64_t i = 0; i < wavelet_stack.count(); i++) {
            if (iter_proj(first + wavelet_stack.select(i)) < iter_proj(pivot_it)) {
                pivot_rank++;
            }
        }
        if (pivot_rank == k) {
            return pivot_it;
        }
        if (pivot_rank < k) {
            wavelet_stack.update(
                [&](int64_t i) { return iter_proj(first + i) > iter_proj(pivot_it); });
            k -= pivot_rank + 1;
        } else {
            wavelet_stack.update(
                [&](int64_t i) { return iter_proj(first + i) < iter_proj(pivot_it); });
        }
    }
}
}  // namespace tcs::readonly::bit_vector_select
