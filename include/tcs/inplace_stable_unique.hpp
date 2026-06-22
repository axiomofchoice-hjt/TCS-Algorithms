#pragma once

#include <algorithm>
#include <cmath>
#include <format>
#include <source_location>
#include <stdexcept>
#include <string_view>

namespace tcs {
namespace inplace_stable_unique {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
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

template <typename RandomIt, typename Proj = std::identity>
std::tuple<RandomIt, RandomIt> build_blocks(
    RandomIt first, RandomIt last, int64_t block_size, Proj proj = {}) {
    using T = std::iter_value_t<RandomIt>;
    RandomIt uniq_start = first;
    RandomIt uniq_end = first;
    RandomIt dup_start = first + block_size;
    RandomIt dup_end = first + block_size;
    std::optional<T> prev_key;
    for (RandomIt it = first + block_size; it < last; it++) {
        if (uniq_end - uniq_start == block_size) {
            std::swap(uniq_start[0], uniq_start[1]);
            uniq_start = uniq_end;
            std::ranges::rotate(dup_start, dup_end, it);
            dup_start += block_size;
            dup_end += block_size;
        }
        if (dup_end - dup_start == block_size) {
            std::ranges::rotate(uniq_start, dup_start, dup_end);
            uniq_start += block_size;
            uniq_end += block_size;
            dup_start = dup_end;
        }
        if (!prev_key || proj(*prev_key) != proj(*it)) {
            prev_key = *it;
            std::swap(*uniq_end, *it);
            uniq_end++;
        } else {
            std::swap(*dup_end, *it);
            dup_end++;
        }
    }
    std::ranges::rotate(uniq_end, dup_start, dup_end);
    std::ranges::rotate(first, last - block_size, last);
    return {uniq_start + block_size, uniq_end + block_size};
}

template <typename RandomIt, typename Proj = std::identity>
RandomIt partition_blocks(RandomIt first, RandomIt last, int64_t block_size, Proj proj = {}) {
    assert_or_throw((last - first) % block_size == 0);
    int64_t n_blocks = (last - first) / block_size;
    RandomIt mid = last;
    for (int64_t i = n_blocks - 1; i >= 0; i--) {
        if (proj(first[i * block_size]) > proj(first[(i * block_size) + 1])) {
            std::swap(first[(i * block_size)], first[(i * block_size) + 1]);
        } else {
            mid -= block_size;
            if (first + (i * block_size) != mid) {
                std::ranges::swap_ranges(first + (i * block_size), first + ((i + 1) * block_size),
                    mid, mid + block_size);
            }
        }
    }
    return mid;
}

template <typename RandomIt, typename Proj = std::identity>
void sort_blocks(RandomIt first, RandomIt last, int64_t block_size, Proj proj = {}) {
    assert_or_throw((last - first) % block_size == 0);
    for (RandomIt cur = first; cur < last; cur += block_size) {
        RandomIt min = cur;
        for (RandomIt scan = cur + block_size; scan < last; scan += block_size) {
            if (proj(*min) > proj(*scan)) {
                min = scan;
            }
        }
        if (min != cur) {
            std::ranges::swap_ranges(cur, cur + block_size, min, min + block_size);
        }
    }
}

template <typename RandomIt, typename Proj = std::identity>
RandomIt inplace_stable_unique(RandomIt first, RandomIt last, Proj proj = {}) {
    assert_or_throw(first <= last, "Error: invalid input");
    int64_t len = last - first;
    int64_t block_size = std::floor(std::sqrt(len));
    if (block_size < 2) {
        return stable_unique_limit(first, last, len, proj);
    }
    RandomIt original_first = first;
    // extract buffer
    first = stable_unique_limit(first, last, block_size, proj);
    if (first - original_first < block_size) {
        return first;
    }
    first = std::ranges::upper_bound(first, last, proj(original_first[block_size - 1]), {}, proj);
    std::ranges::rotate(original_first, original_first + block_size, first);
    first -= block_size;
    /**
     * [original_first..first] -> duplicates of buffer
     * [first..first + block_size] -> buffer
     * [first + block_size..last] -> mains
     */
    auto [tail_uniqs, tail_dups] = build_blocks(first, last, block_size, proj);
    /**
     * [original_first..first] -> duplicates of buffer
     * [first..first + block_size] -> buffer
     * [first + block_size..tail_uniqs] -> mains
     * [tail_uniqs..tail_dups] -> uniques in tail
     * [tail_dups..last] -> duplicates in tail
     */
    RandomIt mid = partition_blocks(first + block_size, tail_uniqs, block_size, proj);
    /**
     * [original_first..first] -> duplicates of buffer
     * [first..first + block_size] -> buffer
     * [first + block_size..mid] -> uniques in main
     * [mid..tail_uniqs] -> duplicates in main
     * [tail_uniqs..tail_dups] -> uniques in tail
     * [tail_dups..last] -> duplicates in tail
     */
    // sort buffer
    sort_blocks(first, first + block_size, 1, proj);
    // sort unique blocks
    sort_blocks(first + block_size, mid, block_size, proj);
    /**
     * [original_first..first] -> duplicates of buffer
     * [first..mid] -> uniques in main
     * [mid..tail_uniqs] -> duplicates in main
     * [tail_uniqs..tail_dups] -> uniques in tail
     * [tail_dups..last] -> duplicates in tail
     */
    // merge uniques in tail to uniques in main
    std::ranges::rotate(mid, tail_uniqs, tail_dups);
    mid += tail_dups - tail_uniqs;
    /**
     * [original_first..first] -> duplicates of buffer
     * [first..mid] -> uniques in main
     * [mid..last] -> duplicates in main
     */
    // merge duplicates of buffer to duplicates in main
    std::ranges::rotate(original_first, first, mid);
    mid -= first - original_first;
    return mid;
}
}  // namespace inplace_stable_unique
}  // namespace tcs
