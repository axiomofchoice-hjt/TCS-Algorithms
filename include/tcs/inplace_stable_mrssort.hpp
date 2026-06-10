#pragma once

#include <algorithm>
#include <format>
#include <source_location>
#include <stdexcept>
#include <string_view>

namespace tcs {
namespace inplace_stable_mrssort {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

template <typename RandomIt, typename Proj>
void inplace_stable_mrssort(RandomIt first, RandomIt last, Proj proj) {
    std::ranges::stable_sort(first, last, {}, proj);  // TODO
}
}  // namespace inplace_stable_mrssort
}  // namespace tcs
