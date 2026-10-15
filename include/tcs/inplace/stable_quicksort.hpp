// In-place stable three-way quicksort
// --------------------------------------------------------------------------
// A stable three-way quicksort that partitions around a median-of-medians
// pivot. The partition/select helpers are the real O(1) in-place primitives
// from stable_partition.hpp / stable_select.hpp. Target: O(n log n) time,
// O(1) extra space.
//
// Blog: https://axiomofchoice-hjt.github.io/pages/74ae0e/

#pragma once

#include <algorithm>
#include <functional>
#include <iterator>
#include <tuple>
#include <utility>

#include "tcs/common/assert.hpp"
#include "tcs/inplace/stable_partition.hpp"
#include "tcs/inplace/stable_select.hpp"

namespace tcs::inplace::stable_quicksort {
template <typename RandomIt, typename Proj = std::identity>
std::tuple<RandomIt, RandomIt> three_way_partition(
    RandomIt first, RandomIt last, std::iter_value_t<RandomIt> pivot, Proj proj = {}) {
    using T = std::iter_value_t<RandomIt>;
    RandomIt pivot_start = stable_partition::inplace_stable_partition(
        first, last, [&](T x) { return proj(x) < proj(pivot); });
    RandomIt pivot_end = stable_partition::inplace_stable_partition(
        pivot_start, last, [&](T x) { return proj(x) == proj(pivot); });
    return {pivot_start, pivot_end};
}

template <typename RandomIt, typename Proj = std::identity>
void inplace_stable_quicksort(RandomIt first, RandomIt last, Proj proj = {}) {
    using T = std::iter_value_t<RandomIt>;
    common::assert_or_throw(first <= last, "inplace_stable_quicksort: first must not be past last");
    RandomIt tail_it = last;
    while (last - tail_it < 2) {
        if (tail_it == first) {
            return;
        }
        T max = *std::ranges::max_element(first, tail_it, {}, proj);
        tail_it = stable_partition::inplace_stable_partition(
            first, tail_it, [&](T x) { return proj(x) < proj(max); });
    }
    RandomIt left = first;
    RandomIt right = tail_it;
    while (true) {
        if (right - left > 1) {
            stable_select::inplace_stable_select(left, left + ((right - left) / 2), right, proj);
            T pivot = left[(right - left) / 2];
            auto [pivot_start, pivot_end] = three_way_partition(left, right, pivot, proj);
            std::swap(*pivot_end, *right);
            right = pivot_start;
        } else {
            common::assert_or_throw(
                right <= tail_it, "stable_quicksort: right pointer exceeds tail");
            if (right == tail_it) {
                break;
            }
            left =
                std::ranges::find_if(right + 1, last, [&](T x) { return proj(x) != proj(*right); });
            right = std::ranges::find_if(left + 1, last, [&](T x) {
                return proj(x) >= proj(*left);
            }) - 1;
            std::swap(*left, *right);
        }
    }
    common::assert_or_throw(std::ranges::is_sorted(first, last, std::less{}, proj),
        "inplace_stable_quicksort: result is not sorted");
}
}  // namespace tcs::inplace::stable_quicksort
