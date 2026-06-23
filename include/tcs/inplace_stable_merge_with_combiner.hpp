#pragma once

#include <algorithm>
#include <cmath>
#include <format>
#include <source_location>
#include <stdexcept>
#include <string_view>

namespace tcs {
namespace inplace_stable_merge_with_combiner {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

template <typename RandomIt, typename Proj = std::identity>
RandomIt inplace_stable_merge_stub(RandomIt first, RandomIt mid, RandomIt last, Proj proj = {}) {
    return std::ranges::merge(first, mid, mid, last, {}, proj);
}

template <typename RandomIt, typename Proj = std::identity>
RandomIt stable_unique_limit(RandomIt first, RandomIt last, int64_t max, Proj proj = {}) {
    RandomIt left = first;
    RandomIt right = first;
    int64_t len = 0;
    for (RandomIt iter = first; iter < last; iter++) {
        if (len < max && (left == right || proj(*(right - 1)) != proj(*iter))) {
            std::ranges::rotate(left, right, iter);
            len++;
            right = iter + 1;
            left = right - len;
        }
    }
    std::ranges::rotate(first, left, right);
    return first + len;
}

template <typename RandomIt, typename Combiner, typename Proj = std::identity>
RandomIt rotate_partition_with_combiner(RandomIt first, RandomIt last, RandomIt other_first,
    RandomIt other_last, Combiner combiner, Proj proj = {}) {
    for (RandomIt it = first; it < last; it++) {
    }
    return last;
}

template <typename RandomIt, typename Combiner, typename Proj = std::identity>
RandomIt inplace_stable_partition_with_combiner(RandomIt first, RandomIt last, RandomIt other_first,
    RandomIt other_last, Combiner combiner, Proj proj = {}) {
    int64_t len = last - first;
    int64_t block_size = std::floor(std::sqrt(len));
    // extract buffer
    RandomIt original_first = first;
    first = stable_unique_limit(first, last, block_size, proj);
    if (first - original_first == block_size) {
    } else {
        assert_or_throw(false);
    }
    return last;
}

template <typename RandomIt, typename Combiner, typename Proj = std::identity>
RandomIt inplace_stable_merge_with_combiner(
    RandomIt first, RandomIt mid, RandomIt last, Combiner combiner, Proj proj = {}) {
    assert_or_throw(first <= mid && mid <= last, "Error: invalid input");
    return mid;
}
}  // namespace inplace_stable_merge_with_combiner
}  // namespace tcs
