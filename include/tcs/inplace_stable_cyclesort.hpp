#pragma once

#include <algorithm>
#include <format>
#include <source_location>
#include <stdexcept>
#include <string_view>

namespace tcs {
namespace inplace_stable_cyclesort {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

// Stub: delegates to std::stable_partition (non-in-place, O(n) extra space).
// Real in-place O(1) implementation: inplace_stable_partition.hpp
template <typename RandomIt, typename Pred>
RandomIt inplace_stable_partition_stub(RandomIt first, RandomIt last, Pred pred) {
    return std::stable_partition(first, last, pred);
}

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
    return {first + gt, first + gt + eq};
}

template <typename RandomIt, typename Proj>
RandomIt destination(RandomIt first, RandomIt last, RandomIt key, Proj proj) {
    using T = std::iter_value_t<RandomIt>;
    auto [left, right] = destination_range(first, last, *key, proj);
    if (left <= key && key < right) {
        return key;
    }
    int64_t eq = 0;
    for (RandomIt it = first; it < key; ++it) {
        if (!(left <= it && it < right) && proj(*key) == proj(*it)) {
            eq++;
        }
    }
    RandomIt res = std::find_if(left, right, [&](T x) { return proj(x) != proj(*key); });
    for (int64_t i = 0; i < eq; ++i) {
        res = std::find_if(res + 1, right, [&](T x) { return proj(x) != proj(*key); });
    }
    return res;
}

template <typename RandomIt, typename Proj>
std::optional<std::iter_value_t<RandomIt>> unordered_upper_bound(
    RandomIt first, RandomIt last, std::iter_value_t<RandomIt> key, Proj proj) {
    std::optional<std::iter_value_t<RandomIt>> result;
    for (RandomIt it = first; it != last; ++it) {
        if (proj(*it) > proj(key) && (!result || proj(*it) < proj(*result))) {
            result = *it;
        }
    }
    return result;
}

template <typename RandomIt, typename Proj>
void inplace_stable_cyclesort(RandomIt first, RandomIt last, Proj proj) {
    using T = std::iter_value_t<RandomIt>;
    if (last - first <= 1) {
        return;
    }
    for (std::optional<T> i = *std::ranges::min_element(first, last, {}, proj); i;
        i = unordered_upper_bound(first, last, *i, proj)) {
        auto [left, right] = destination_range(first, last, *i, proj);
        int64_t inner_sames = inplace_stable_partition_stub(left, right, [&](T x) {
            return proj(x) == proj(*i);
        }) - left;
        int64_t left_sames = std::count_if(first, left, [&](T x) { return proj(x) == proj(*i); });
        std::rotate(left, left + inner_sames, left + inner_sames + left_sames);
    }

    for (RandomIt it = first; it != last; ++it) {
        RandomIt dest = destination(first, last, it, proj);
        while (dest != it) {
            RandomIt next_dest = destination(first, last, dest, proj);
            std::swap(*it, *dest);
            dest = next_dest;
        }
    }
}
}  // namespace inplace_stable_cyclesort
}  // namespace tcs
