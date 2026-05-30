#pragma once

#include <algorithm>
#include <format>
#include <source_location>
#include <stdexcept>
#include <string_view>

namespace tcs {
namespace bfprt {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

template <typename RandomIt>
void bfprt(RandomIt first, RandomIt mid, RandomIt last) {
    using T = typename std::iterator_traits<RandomIt>::value_type;
    assert_or_throw(first <= mid && mid < last);
    int64_t len = last - first;
    constexpr int64_t group_size = 5;
    if (len < group_size) {
        std::sort(first, last);
        return;
    }
    // median of medians of each group
    for (int64_t i = 0; i + group_size <= len; i += group_size) {
        std::sort(first + i, first + i + group_size);
        std::swap(first[i / group_size], first[i + (group_size / 2)]);
    }
    bfprt(first, first + (len / group_size / 2), first + (len / group_size));
    // three-way partition
    T pivot = first[len / group_size / 2];
    RandomIt pivot_start = std::partition(first, last, [pivot](T el) { return el < pivot; });
    RandomIt pivot_end = std::partition(pivot_start, last, [pivot](T el) { return el == pivot; });
    // recurse
    if (mid < pivot_start) {
        bfprt(first, mid, pivot_start);
    } else if (mid >= pivot_end) {
        bfprt(pivot_end, mid, last);
    }
}
}  // namespace bfprt
}  // namespace tcs
