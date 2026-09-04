// Select (read-only order statistic)
// --------------------------------------------------------------------------
// Returns an iterator to the k-th smallest element of a random-access range,
// read-only. n_layers > 1 narrows a [lower, upper] candidate range by sampling
// the densest block.
//
// Time-space complexity: O(n^(1 + 1/s)) for constant s (Frederickson 1987).
//
// Blog:

#pragma once

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <format>
#include <source_location>
#include <stdexcept>
#include <string_view>
#include <utility>

namespace tcs {
namespace readonly {
namespace constant_space_select {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

template <typename RandomIt, typename IterProj>
bool in_range(RandomIt it, RandomIt lower_it, RandomIt upper_it, IterProj iter_proj) {
    return iter_proj(it) >= iter_proj(lower_it) && iter_proj(it) <= iter_proj(upper_it);
}

template <typename RandomIt, typename IterProj>
int64_t count_in_range(
    RandomIt first, RandomIt last, RandomIt lower_it, RandomIt upper_it, IterProj iter_proj) {
    assert_or_throw(first <= last);
    int64_t result = 0;
    for (RandomIt it = first; it < last; it++) {
        if (in_range(it, lower_it, upper_it, iter_proj)) {
            result++;
        }
    }
    return result;
}

template <typename RandomIt, typename IterProj>
RandomIt min_greater(RandomIt first, RandomIt last, RandomIt pivot_it, IterProj iter_proj) {
    assert_or_throw(first <= last);
    std::optional<RandomIt> result;
    for (RandomIt it = first; it < last; it++) {
        if (iter_proj(it) > iter_proj(pivot_it) &&
            (!result.has_value() || iter_proj(it) < iter_proj(result.value()))) {
            result = it;
        }
    }
    assert_or_throw(result.has_value());
    return result.value();
}

template <typename RandomIt, typename IterProj>
RandomIt max_smaller(RandomIt first, RandomIt last, RandomIt pivot_it, IterProj iter_proj) {
    assert_or_throw(first <= last);
    std::optional<RandomIt> result;
    for (RandomIt it = first; it < last; it++) {
        if (iter_proj(it) < iter_proj(pivot_it) &&
            (!result.has_value() || iter_proj(it) > iter_proj(result.value()))) {
            result = it;
        }
    }
    assert_or_throw(result.has_value());
    return result.value();
}

template <typename RandomIt, typename IterProj>
RandomIt select_recursive(RandomIt first, RandomIt last, RandomIt lower_it, RandomIt upper_it,
    int64_t k, int64_t n_layers, IterProj iter_proj) {
    assert_or_throw(first < last);
    assert_or_throw(n_layers > 0);
    int64_t size = last - first;
    while (true) {
        int64_t n_candidates = count_in_range(first, last, lower_it, upper_it, iter_proj);
        assert_or_throw(k >= 0 && k < n_candidates);
        RandomIt pivot_it;
        if (n_layers == 1) {
            for (RandomIt it = first; it < last; it++) {
                if (in_range(it, lower_it, upper_it, iter_proj)) {
                    pivot_it = it;
                    break;
                }
            }
        } else {
            int64_t block_size =
                std::ceil(static_cast<double>(size) /
                          std::pow(n_candidates, 1.0 / static_cast<double>(n_layers)));
            int64_t n_blocks = (size + block_size - 1) / block_size;

            RandomIt max_block_start = last;
            RandomIt max_block_end = last;
            int64_t max_block_count = 0;
            for (int64_t i = 0; i < n_blocks; i++) {
                RandomIt block_start = first + (i * block_size);
                RandomIt block_end = first + std::min(size, (i + 1) * block_size);
                int64_t block_count =
                    count_in_range(block_start, block_end, lower_it, upper_it, iter_proj);
                if (block_count > max_block_count) {
                    max_block_start = block_start;
                    max_block_end = block_end;
                    max_block_count = block_count;
                }
            }
            pivot_it = select_recursive(max_block_start, max_block_end, lower_it, upper_it,
                (max_block_count - 1) / 2, n_layers - 1, iter_proj);
        }
        int64_t rank = count_in_range(first, last, lower_it, pivot_it, iter_proj) - 1;
        if (rank == k) {
            return pivot_it;
        }
        if (rank < k) {
            lower_it = min_greater(first, last, pivot_it, iter_proj);
            k -= rank + 1;
        } else {
            upper_it = max_smaller(first, last, pivot_it, iter_proj);
        }
    }
}

template <typename RandomIt, typename Proj = std::identity>
RandomIt constant_space_select(
    RandomIt first, RandomIt last, int64_t k, int64_t n_layers, Proj proj = {}) {
    assert_or_throw(k >= 0 && k < (last - first));
    auto iter_proj = [proj](RandomIt it) { return std::pair{proj(*it), it}; };
    RandomIt lower_it = first;
    RandomIt upper_it = first;
    for (RandomIt it = first; it < last; it++) {
        lower_it = std::ranges::min(lower_it, it, {}, iter_proj);
        upper_it = std::ranges::max(upper_it, it, {}, iter_proj);
    }
    return select_recursive(first, last, lower_it, upper_it, k, n_layers, iter_proj);
}
}  // namespace constant_space_select
}  // namespace readonly
}  // namespace tcs
