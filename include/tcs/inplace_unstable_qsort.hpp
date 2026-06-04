#pragma once

#include <algorithm>
#include <format>
#include <random>
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
std::tuple<RandomIt, RandomIt> three_way_partition(
    RandomIt first, RandomIt last, std::iter_value_t<RandomIt> pivot, Proj proj = {}) {
    using T = std::iter_value_t<RandomIt>;
    RandomIt pivot_start = std::partition(first, last, [&](T x) { return proj(x) < proj(pivot); });
    RandomIt pivot_end =
        std::partition(pivot_start, last, [&](T x) { return proj(x) == proj(pivot); });
    return {pivot_start, pivot_end};
}

constexpr int64_t kDefaultRandomSeed = 42;

template <typename RandomIt, typename Proj = std::identity>
void unstable_quick_sort(
    RandomIt first, RandomIt last, Proj proj = {}, int64_t random_seed = kDefaultRandomSeed) {
    using T = std::iter_value_t<RandomIt>;
    std::mt19937 gen(random_seed);
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
            T pivot = left[std::uniform_int_distribution<int64_t>(0, right - left - 1)(gen)];
            auto [pivot_start, pivot_end] = three_way_partition(left, right, pivot, proj);
            std::swap(*pivot_end, *right);
            right = pivot_start;
        }
    }
}
}  // namespace inplace_unstable_qsort
}  // namespace tcs
