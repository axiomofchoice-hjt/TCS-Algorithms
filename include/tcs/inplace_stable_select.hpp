#pragma once

#include <algorithm>
#include <bit>
#include <cmath>
#include <format>
#include <functional>
#include <source_location>
#include <stdexcept>
#include <string_view>

namespace tcs {
namespace inplace_stable_select {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

inline int64_t ceil_log2(int64_t x) {
    assert_or_throw(x > 0);
    return std::bit_width(static_cast<uint64_t>(x) - 1);
}

template <typename RandomIt, typename Proj = std::identity>
void bubble_sort(RandomIt first, RandomIt last, Proj proj = {}) {
    int64_t len = last - first;
    for (int64_t i = 0; i + 1 < len; i++) {
        for (RandomIt j = first; j < last - i - 1; j++) {
            if (proj(*j) > proj(*(j + 1))) {
                std::swap(*j, *(j + 1));
            }
        }
    }
}

template <typename RandomIt, typename Proj = std::identity>
auto probable_major(RandomIt first, RandomIt last, Proj proj = {}) {
    using T = typename std::iterator_traits<RandomIt>::value_type;
    T major = *first;
    int64_t cnt = 1;
    for (RandomIt it = first + 1; it < last; it++) {
        if (proj(*it) == proj(major)) {
            cnt++;
        } else if (cnt > 0) {
            cnt--;
        } else {
            major = *it;
            cnt = 1;
        }
    }
    return major;
}

template <typename RandomIt, typename Proj = std::identity>
bool extract_buffer(RandomIt first, RandomIt last, int64_t buffer_len, Proj proj = {}) {
    using T = typename std::iterator_traits<RandomIt>::value_type;
    int64_t len = last - first;
    if (len < buffer_len * 2) {
        return false;
    }
    T major = probable_major(first, first + (buffer_len * 2), proj);
    if (std::ranges::count_if(first, first + (buffer_len * 2),
            [&](T x) { return proj(x) == proj(major); }) <= buffer_len) {
        bubble_sort(first, first + (buffer_len * 2), proj);
        return true;
    }
    if (std::ranges::count_if(first, last, [&](T x) { return proj(x) == proj(major); }) >
        len - buffer_len) {
        return false;
    }
    std::stable_partition(first, last, [&](T x) { return proj(x) != proj(major); });
    RandomIt major_ptr =
        std::ranges::find_if(first, last, [&](T x) { return proj(x) == proj(major); });
    std::ranges::rotate(first + buffer_len, major_ptr, major_ptr + buffer_len);
    return true;
}

template <typename RandomIt, typename Proj = std::identity>
void inplace_stable_select(RandomIt first, RandomIt mid, RandomIt last, Proj proj = {}) {
    using T = typename std::iterator_traits<RandomIt>::value_type;
    assert_or_throw(first <= mid && mid < last);
    int64_t len = last - first;
    int64_t buffer_len = static_cast<int64_t>(std::floor(std::sqrt(len))) * 2;
    if (!extract_buffer(first, last, buffer_len, proj)) {
        T major = probable_major(first, last, proj);
        std::stable_partition(first, last, [&](T x) { return proj(x) != proj(major); });
        RandomIt major_ptr =
            std::ranges::find_if(first, last, [&](T x) { return proj(x) == proj(major); });
        bubble_sort(first, major_ptr, proj);
        std::ranges::rotate(
            std::ranges::find_if(first, major_ptr, [&](T x) { return proj(x) >= proj(major); }),
            major_ptr, last);
        return;
    }
    std::ranges::stable_sort(
        first, last, {}, proj);  // TODO: implement proper inplace stable select
}
}  // namespace inplace_stable_select
}  // namespace tcs
