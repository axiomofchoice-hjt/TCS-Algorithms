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
void bubble_sort(RandomIt first, RandomIt last, Proj proj = {}) {
    int64_t len = last - first;
    for (int64_t i = 0; i + 1 < len; i++) {
        for (RandomIt j = first; j < last - i - 1; j++) {
            if (proj(*j) > proj(*(j + 1))) {
                std::swap(*j, *(j + 1));
            }
        }
    }
}

template <typename RandomIt, typename Proj = std::identity>
std::tuple<RandomIt, RandomIt> homogenize_blocks(
    RandomIt first, RandomIt last, int64_t block_size, Proj proj = {}) {
    using T = std::iter_value_t<RandomIt>;
    RandomIt l1 = first;
    RandomIt l1_end = first;
    RandomIt l2 = first + block_size;
    RandomIt l2_end = first + block_size;
    std::optional<T> pre;
    for (RandomIt it = first + block_size; it < last; it++) {
        if (l1_end - l1 == block_size) {
            std::swap(l1[0], l1[1]);
            l1 = l1_end;
            std::ranges::rotate(l2, l2_end, it);
            l2 += block_size;
            l2_end += block_size;
        }
        if (l2_end - l2 == block_size) {
            std::ranges::rotate(l1, l2, l2_end);
            l1 += block_size;
            l1_end += block_size;
            l2 = l2_end;
        }
        if (!pre || proj(*pre) != proj(*it)) {
            pre = *it;
            std::swap(*l1_end, *it);
            l1_end++;
        } else {
            std::swap(*l2_end, *it);
            l2_end++;
        }
    }
    std::ranges::rotate(l1_end, l2, l2_end);
    std::ranges::rotate(first, last - block_size, last);
    return {l1 + block_size, l1_end + block_size};
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
void block_selection_sort(RandomIt first, RandomIt last, int64_t block_size, Proj proj = {}) {
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
    first = stable_unique_limit(first, last, block_size, proj);
    if (first - original_first < block_size) {
        return first;
    }
    first = std::ranges::upper_bound(first, last, proj(original_first[block_size - 1]), {}, proj);
    std::ranges::rotate(original_first, original_first + block_size, first);
    first -= block_size;
    auto [tail_l1, tail_l2] = homogenize_blocks(first, last, block_size, proj);
    RandomIt mid = partition_blocks(first + block_size, tail_l1, block_size, proj);
    bubble_sort(first, first + block_size, proj);
    block_selection_sort(first + block_size, mid, block_size, proj);
    std::ranges::rotate(mid, tail_l1, tail_l2);
    mid += tail_l2 - tail_l1;
    std::ranges::rotate(original_first, first, mid);
    mid -= first - original_first;
    return mid;
}
}  // namespace inplace_stable_unique
}  // namespace tcs
