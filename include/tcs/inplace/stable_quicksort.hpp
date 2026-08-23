// In-place stable three-way quicksort
// --------------------------------------------------------------------------
// A stable three-way quicksort that partitions around a median-of-medians
// pivot. The partition/select helpers come from the real O(1) in-place
// primitives in stable_partition.hpp / stable_select.hpp when TCS_NO_TEMP_IMPL
// is defined; otherwise they fall back to std-based stubs (std::stable_partition
// / std::ranges::nth_element via a temporary buffer). Target: O(n log n) time,
// O(1) extra space.
//
// Blog: https://axiomofchoice-hjt.github.io/pages/74ae0e/

#pragma once

#include <algorithm>
#include <format>
#include <functional>
#include <iterator>
#include <source_location>
#include <stdexcept>
#include <string_view>
#include <tuple>
#include <utility>

#ifdef TCS_NO_TEMP_IMPL
#include "tcs/inplace/stable_partition.hpp"
#include "tcs/inplace/stable_select.hpp"
#else
#include <vector>
#endif

namespace tcs {
namespace inplace {
namespace stable_quicksort {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

template <typename RandomIt, typename Pred>
RandomIt inplace_stable_partition_ref(RandomIt first, RandomIt last, Pred pred) {
#ifdef TCS_NO_TEMP_IMPL
    return stable_partition::inplace_stable_partition(first, last, pred);
#else
    return std::stable_partition(first, last, pred);
#endif
}

template <typename RandomIt, typename Proj = std::identity>
void inplace_stable_select_ref(RandomIt first, RandomIt mid, RandomIt last, Proj proj = {}) {
#ifdef TCS_NO_TEMP_IMPL
    return stable_select::inplace_stable_select(first, mid, last, proj);
#else
    using T = std::iter_value_t<RandomIt>;
    auto buffer = std::vector<T>(first, last);
    std::ranges::nth_element(
        buffer.begin(), buffer.begin() + (mid - first), buffer.end(), {}, proj);
    T pivot = buffer[mid - first];
    RandomIt pivot_it =
        std::stable_partition(first, last, [&](T x) { return proj(x) < proj(pivot); });
    std::stable_partition(pivot_it, last, [&](T x) { return proj(x) == proj(pivot); });
#endif
}

template <typename RandomIt, typename Proj = std::identity>
std::tuple<RandomIt, RandomIt> three_way_partition(
    RandomIt first, RandomIt last, std::iter_value_t<RandomIt> pivot, Proj proj = {}) {
    using T = std::iter_value_t<RandomIt>;
    RandomIt pivot_start =
        inplace_stable_partition_ref(first, last, [&](T x) { return proj(x) < proj(pivot); });
    RandomIt pivot_end = inplace_stable_partition_ref(
        pivot_start, last, [&](T x) { return proj(x) == proj(pivot); });
    return {pivot_start, pivot_end};
}

template <typename RandomIt, typename Proj = std::identity>
void inplace_stable_quicksort(RandomIt first, RandomIt last, Proj proj = {}) {
    using T = std::iter_value_t<RandomIt>;
    RandomIt tail_it = last;
    while (last - tail_it < 2) {
        if (tail_it == first) {
            return;
        }
        T max = *std::ranges::max_element(first, tail_it, {}, proj);
        tail_it =
            inplace_stable_partition_ref(first, tail_it, [&](T x) { return proj(x) < proj(max); });
    }
    RandomIt left = first;
    RandomIt right = tail_it;
    while (true) {
        if (right - left > 1) {
            inplace_stable_select_ref(left, left + ((right - left) / 2), right, proj);
            T pivot = left[(right - left) / 2];
            auto [pivot_start, pivot_end] = three_way_partition(left, right, pivot, proj);
            std::swap(*pivot_end, *right);
            right = pivot_start;
        } else {
            assert_or_throw(right <= tail_it);
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
}
}  // namespace stable_quicksort
}  // namespace inplace
}  // namespace tcs
