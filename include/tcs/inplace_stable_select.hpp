#pragma once

#include <algorithm>
#include <format>
#include <source_location>
#include <stdexcept>
#include <string_view>

namespace tcs {
namespace inplace_stable_select {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

template <typename RandomIt>
void inplace_stable_select(RandomIt first, RandomIt mid, RandomIt last) {
    assert_or_throw(first <= mid && mid < last);
    std::stable_sort(first, last);  // TODO: implement inplace_stable_select
}
}  // namespace inplace_stable_select
}  // namespace tcs
