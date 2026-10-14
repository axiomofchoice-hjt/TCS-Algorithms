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
#include <cstdint>
#include <functional>
#include <iterator>
#include <utility>

#include "tcs/basic/bubble_sort.hpp"
#include "tcs/common/assert.hpp"

namespace tcs::basic::bfprt {
template <typename RandomIt, typename Proj = std::identity>
void bfprt(RandomIt first, RandomIt mid, RandomIt last, Proj proj = {}) {
    using T = std::iter_value_t<RandomIt>;
    common::assert_or_throw(first <= mid && mid < last, "bfprt: mid must lie in [first, last)");
    int64_t len = last - first;
    constexpr int64_t group_size = 5;
    if (len < group_size) {
        basic::bubble_sort(first, last, proj);
        return;
    }
    // median of medians of each group
    for (int64_t i = 0; i + group_size <= len; i += group_size) {
        basic::bubble_sort(first + i, first + i + group_size, proj);
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
}  // namespace tcs::basic::bfprt
