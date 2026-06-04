#pragma once

#include <algorithm>
#include <format>
#include <source_location>
#include <stdexcept>
#include <string_view>

namespace tcs {
namespace inplace_unstable_qsort {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

template <typename RandomIt, typename Proj = std::identity>
void inplace_unstable_select_stub(RandomIt first, RandomIt mid, RandomIt last, Proj proj = {}) {
    std::ranges::nth_element(first, mid, last, {}, proj);
}

template <typename RandomIt, typename Proj = std::identity>
std::tuple<RandomIt, RandomIt> three_way_partition(
    RandomIt first, RandomIt last, std::iter_value_t<RandomIt> pivot, Proj proj = {}) {
    using T = std::iter_value_t<RandomIt>;
    RandomIt pivot_start = std::partition(first, last, [&](T x) { return proj(x) < proj(pivot); });
    RandomIt pivot_end =
        std::partition(pivot_start, last, [&](T x) { return proj(x) == proj(pivot); });
    return {pivot_start, pivot_end};
}

template <typename RandomIt, typename Proj = std::identity>
void unstable_quick_sort(RandomIt first, RandomIt last, Proj proj = {}) {
    using T = std::iter_value_t<RandomIt>;
    RandomIt tail_it = last;
    while (last - tail_it < 2) {
        if (tail_it == first) {
            return;
        }
        T max = *std::ranges::max_element(first, tail_it, {}, proj);
        tail_it = std::partition(first, tail_it, [&](T x) { return proj(x) < proj(max); });
    }
    RandomIt left = first;
    RandomIt right = tail_it;
    while (true) {
        if (right - left <= 1) {
            if (right >= tail_it) {
                return;
            }
            RandomIt it1 = right + 1;
            while (proj(*it1) == proj(*right)) {
                it1++;
            }
            RandomIt it2 = it1 + 1;
            while (proj(*it2) < proj(*it1)) {
                it2++;
            }
            std::swap(*it1, *(it2 - 1));
            left = it1;
            right = it2 - 1;
        } else {
            inplace_unstable_select_stub(left, right, left + ((right - left) / 2), proj);
            T pivot = left[(right - left) / 2];
            auto [pivot_start, pivot_end] = three_way_partition(left, right, pivot, proj);
            std::swap(*pivot_end, *right);
            right = pivot_start;
        }
    }
}
}  // namespace inplace_unstable_qsort
}  // namespace tcs
