// BFPRT — Median of Medians selection
// --------------------------------------------------------------------------
// Selects the k-th smallest element of a range by recursively choosing the
// median of medians (groups of 5) as the partition pivot, giving worst-case
// O(n) time. Uses an unstable partition and costs O(log n) extra stack space;
// tcs::inplace::unstable_select removes that stack for a strict O(1) version.
//
// Blog: https://axiomofchoice-hjt.github.io/pages/63a6df/

#pragma once

#include <algorithm>
#include <format>
#include <functional>
#include <source_location>
#include <stdexcept>
#include <string_view>

namespace tcs {
namespace bfprt {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
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
void bfprt(RandomIt first, RandomIt mid, RandomIt last, Proj proj = {}) {
    using T = std::iter_value_t<RandomIt>;
    assert_or_throw(first <= mid && mid < last);
    int64_t len = last - first;
    constexpr int64_t group_size = 5;
    if (len < group_size) {
        bubble_sort(first, last, proj);
        return;
    }
    // median of medians of each group
    for (int64_t i = 0; i + group_size <= len; i += group_size) {
        bubble_sort(first + i, first + i + group_size, proj);
        std::swap(first[i / group_size], first[i + (group_size / 2)]);
    }
    bfprt(first, first + (len / group_size / 2), first + (len / group_size), proj);
    // three-way partition
    T pivot = first[len / group_size / 2];
    RandomIt pivot_start =
        std::partition(first, last, [pivot, proj](T el) { return proj(el) < proj(pivot); });
    RandomIt pivot_end =
        std::partition(pivot_start, last, [pivot, proj](T el) { return proj(el) == proj(pivot); });
    // recurse
    if (mid < pivot_start) {
        bfprt(first, mid, pivot_start, proj);
    } else if (mid >= pivot_end) {
        bfprt(pivot_end, mid, last, proj);
    }
}
}  // namespace bfprt
}  // namespace tcs
