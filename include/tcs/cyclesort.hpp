#pragma once

#include <algorithm>
#include <format>
#include <source_location>
#include <stdexcept>
#include <string_view>

namespace tcs {
namespace cyclesort {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
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
void cyclesort(RandomIt first, RandomIt last, Proj proj) {
    using T = std::iter_value_t<RandomIt>;
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
}
}  // namespace cyclesort
}  // namespace tcs
