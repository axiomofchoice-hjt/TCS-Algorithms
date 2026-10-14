// Select by bit vectors (read-only order statistic)
// --------------------------------------------------------------------------
// Returns an iterator to the k-th smallest element of a random-access range,
// read-only. A wavelet stack of rank/select bit vectors tracks the remaining
// candidates; each round a median-of-medians pivot splits them below / at /
// above, and the pivot always leaves the candidate set. Ties break by position,
// so the result is the element a stable sort would place at k.
//
// Time-space complexity: O(n) worst-case time, and O(n) bits of extra space
// (O(n / log n) machine words).
//
// Blog: https://axiomofchoice-hjt.github.io/pages/887ea0/

#pragma once

#include <algorithm>
#include <cstdint>
#include <functional>
#include <utility>
#include <vector>

#include "tcs/basic/bfprt.hpp"
#include "tcs/common/assert.hpp"
#include "tcs/common/bit.hpp"
#include "tcs/ds/compact_bit_vector.hpp"

namespace tcs::readonly::bit_vector_select {
struct WaveletStack {
    int64_t size_ = 0;
    int64_t n_word_bits_ = 0;
    std::vector<ds::compact_bit_vector::CompactBitVector> stack_;

    static WaveletStack create(int64_t size, int64_t n_word_bits) {
        common::assert_or_throw(size >= 0);
        common::assert_or_throw(n_word_bits > 0 && n_word_bits <= common::n_machine_word_bits);
        return {.size_ = size, .n_word_bits_ = n_word_bits, .stack_ = {}};
    }

    template <typename Placement>
    void update(Placement placement) {
        auto bit_vector =
            ds::compact_bit_vector::CompactBitVector::create(count(), [this, placement](int64_t k) {
                int64_t index = select(k);
                return placement(index);
            });
        stack_.push_back(bit_vector);
    }

    bool get(int64_t index) const {
        common::assert_or_throw(index >= 0 && index < size_);
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
        common::assert_or_throw(index >= 0 && index <= size_);
        for (const auto& bit_vector : stack_) {
            index = bit_vector.rank(index);
        }
        return index;
    }

    int64_t select(int64_t k) const {
        if (stack_.empty()) {
            common::assert_or_throw(k >= 0 && k < size_);
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
    common::assert_or_throw(size > 0 && n_candidates > 0);
    int64_t block_size = std::max(size / std::max(common::ceil_log2(size), int64_t{1}), int64_t{1});
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
        tcs::basic::bfprt::bfprt(
            buffer.begin(), buffer.begin() + mid_index, buffer.end(), iter_proj);
        medians.push_back(buffer[mid_index]);
    }
    int64_t mid_index = (static_cast<int64_t>(medians.size()) - 1) / 2;
    tcs::basic::bfprt::bfprt(
        medians.begin(), medians.begin() + mid_index, medians.end(), iter_proj);
    return medians[mid_index];
}

template <typename RandomIt, typename Proj = std::identity>
RandomIt bit_vector_select(RandomIt first, RandomIt last, int64_t k, Proj proj = {}) {
    auto iter_proj = [proj](RandomIt it) { return std::pair{proj(*it), it}; };
    common::assert_or_throw(first < last);
    int64_t size = last - first;
    common::assert_or_throw(k >= 0 && k < size);
    int64_t n_word_bits = std::max(common::ceil_log2(size), int64_t{1});
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
