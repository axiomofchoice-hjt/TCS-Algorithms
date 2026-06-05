#pragma once

#include <algorithm>
#include <format>
#include <source_location>
#include <stdexcept>
#include <string_view>
#include <vector>

namespace tcs {
namespace inplace_stable_quicksort {
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

// Stub: copies to vector and uses std::ranges::nth_element (non-in-place, O(n) extra space).
// Real in-place O(1) implementation: inplace_stable_select.hpp
template <typename RandomIt, typename Proj = std::identity>
void inplace_stable_select_stub(RandomIt first, RandomIt mid, RandomIt last, Proj proj = {}) {
    using T = std::iter_value_t<RandomIt>;
    auto buffer = std::vector<T>(first, last);
    std::ranges::nth_element(
        buffer.begin(), buffer.begin() + (mid - first), buffer.end(), {}, proj);
    T pivot = buffer[mid - first];
    RandomIt pivot_it =
        std::stable_partition(first, last, [&](T x) { return proj(x) < proj(pivot); });
    std::stable_partition(pivot_it, last, [&](T x) { return proj(x) == proj(pivot); });
}

template <typename RandomIt, typename Proj = std::identity>
std::tuple<RandomIt, RandomIt> three_way_partition(
    RandomIt first, RandomIt last, std::iter_value_t<RandomIt> pivot, Proj proj = {}) {
    using T = std::iter_value_t<RandomIt>;
    RandomIt pivot_start =
        inplace_stable_partition_stub(first, last, [&](T x) { return proj(x) < proj(pivot); });
    RandomIt pivot_end = inplace_stable_partition_stub(
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
            inplace_stable_partition_stub(first, tail_it, [&](T x) { return proj(x) < proj(max); });
    }
    RandomIt left = first;
    RandomIt right = tail_it;
    while (true) {
        if (right - left > 1) {
            inplace_stable_select_stub(left, left + ((right - left) / 2), right, proj);
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
}  // namespace inplace_stable_quicksort
}  // namespace tcs
