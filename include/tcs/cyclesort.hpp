// Cycle sort
// --------------------------------------------------------------------------
// Classic in-place cycle sort: repeatedly swaps each element into its final
// position, found by counting how many elements should precede it. Minimizes
// the number of writes to O(n) at the cost of O(n^2) comparisons, using O(1)
// extra space. Not stable — see tcs::inplace::stable_cyclesort.
//
// Blog: https://axiomofchoice-hjt.github.io/pages/e2847a/

#pragma once

#include <algorithm>
#include <cstdint>
#include <functional>
#include <iterator>
#include <tuple>
#include <utility>

#include "tcs/common/assert.hpp"

namespace tcs::cyclesort {
template <typename RandomIt, typename Proj>
std::tuple<RandomIt, RandomIt> destination_range(
    RandomIt first, RandomIt last, std::iter_value_t<RandomIt> key, Proj proj) {
    int64_t gt = 0;
    int64_t eq = 0;
    for (RandomIt it = first; it < last; ++it) {
        if (proj(key) > proj(*it)) {
            gt++;
        } else if (proj(key) == proj(*it)) {
            eq++;
        }
    }
    common::assert_or_throw(
        gt + eq <= last - first, "cyclesort: destination range exceeds the array");
    return {first + gt, first + gt + eq};
}

template <typename RandomIt, typename Proj>
void cyclesort(RandomIt first, RandomIt last, Proj proj) {
    using T = std::iter_value_t<RandomIt>;
    common::assert_or_throw(first <= last, "cyclesort: first must not be past last");
    if (last - first <= 1) {
        return;
    }

    for (RandomIt it = first; it != last; it++) {
        while (true) {
            auto [left, right] = destination_range(first, last, *it, proj);
            if (left <= it && it < right) {
                break;
            }
            std::swap(*it, *std::find_if(left, right, [&](T x) { return proj(x) != proj(*it); }));
        }
    }
    common::assert_or_throw(
        std::ranges::is_sorted(first, last, std::less{}, proj), "cyclesort: result is not sorted");
}
}  // namespace tcs::cyclesort
