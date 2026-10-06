#pragma once

#include <format>
#include <source_location>
#include <stdexcept>
#include <string_view>
#include <vector>

#ifdef TCS_NO_TEMP_IMPL
#include "tcs/ds/compact_bit_vector.hpp"
#else
#endif

namespace tcs::readonly::bit_vector_select {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

inline int64_t ceil_log2(int64_t x) {
    assert_or_throw(x > 0, "ceil_log2: argument must be positive");
    return std::bit_width(static_cast<uint64_t>(x) - 1);
}

template <typename Placement>
auto bit_vector_create_ref(
    int64_t size, Placement placement, [[maybe_unused]] int64_t n_word_bits) {
#ifdef TCS_NO_TEMP_IMPL
    return tcs::ds::compact_bit_vector::CompactBitVector::create(size, placement, n_word_bits);
#else
    struct BitVectorStub {
        std::vector<bool> data_;
        std::vector<int64_t> rank_;
        std::vector<int64_t> select_;

        bool get(int64_t index) const {
            assert_or_throw(index >= 0 && index < data_.size());
            return data_[index];
        }
        int64_t rank(int64_t index) const {
            assert_or_throw(index >= 0 && index <= data_.size());
            return rank_[index];
        }
        int64_t select(int64_t k) const {
            assert_or_throw(k >= 0 && k < select_.size());
            return select_[k];
        }
    };
    std::vector<bool> data;
    std::vector<int64_t> rank;
    std::vector<int64_t> select;
    int64_t cnt = 0;
    for (int64_t i = 0; i < size; i++) {
        bool value = placement(i);
        data.push_back(value);
        rank.push_back(cnt);
        if (value) {
            cnt++;
            select.push_back(i);
        }
    }
    return BitVectorStub{.data_ = data, .rank_ = rank, .select_ = select};
#endif
}

template <typename WaveletStack, typename RandomIt, typename Proj = std::identity>
RandomIt median_of_medians(
    const WaveletStack& wavelet_stack, RandomIt first, RandomIt last, Proj proj = {}) {
    assert_or_throw(first < last);
    int64_t size = last - first;
    int64_t block_size = std::max(size / ceil_log2(size), int64_t{1});
    int64_t n_blocks = (size + block_size - 1) / block_size;
    for (int64_t i = 0; i < n_blocks; i++) {
        int64_t start = i * block_size;
        int64_t end = std::min(start + block_size, size);
        std::vector<RandomIt> block;
        for (int64_t j = start; j < end; j++) {
            block.push_back(first + j);
        }
    }
}

template <typename RandomIt, typename Proj = std::identity>
RandomIt bit_vector_select(RandomIt first, RandomIt last, int64_t k, Proj proj = {}) {
    assert_or_throw(first < last);
    int64_t size = last - first;
    assert_or_throw(k >= 0 && k < size);
    int64_t n_word_bits = ceil_log2(size);
    std::vector wavelet_stack = {
        bit_vector_create_ref(size, [](int64_t) { return true; }, n_word_bits)};

    return {};
}
}  // namespace tcs::readonly::bit_vector_select
