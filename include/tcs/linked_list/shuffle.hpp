#pragma once

#include <cstdint>
#include <format>
#include <list>
#include <source_location>
#include <stdexcept>

namespace tcs {
namespace linked_list {
namespace shuffle {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

// `rand(lo, hi)` must return a uniform integer in [lo, hi]. It is passed by
// value into every recursive call, so give it shared state through a
// reference capture (e.g. a [&] lambda wrapping an std::mt19937).
template <typename T, typename Rand>
void linked_list_shuffle(std::list<T>& list, Rand rand) {
    int64_t n = list.size();
    if (n < 2) {
        return;
    }

    int64_t left_sz = n / 2;
    int64_t right_sz = n - left_sz;

    std::list<T> left;
    left.splice(left.begin(), list, list.begin(), std::next(list.begin(), n / 2));
    std::list<T> right = std::move(list);

    linked_list_shuffle(left, rand);
    linked_list_shuffle(right, rand);

    list = {};
    while (left_sz + right_sz > 0) {
        int64_t i = rand(0, left_sz + right_sz - 1);
        if (i < left_sz) {
            list.splice(list.end(), left, left.begin(), std::next(left.begin()));
            left_sz--;
        } else {
            list.splice(list.end(), right, right.begin(), std::next(right.begin()));
            right_sz--;
        }
    }
}
}  // namespace shuffle
}  // namespace linked_list
}  // namespace tcs
