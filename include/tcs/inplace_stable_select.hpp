#pragma once

#include <algorithm>
#include <bit>
#include <cmath>
#include <format>
#include <functional>
#include <source_location>
#include <stdexcept>
#include <string_view>
#include <vector>

namespace tcs {
namespace inplace_stable_select {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

template <typename RandomIt, typename Pred>
void inplace_stable_partition_stub(RandomIt first, RandomIt last, Pred pred) {
    std::stable_partition(first, last, pred);
}

template <typename RandomIt, typename Pred, typename Placement>
void inplace_stable_unpartition_stub(
    RandomIt first, RandomIt last, Pred pred, Placement placement) {
    using T = typename std::iterator_traits<RandomIt>::value_type;
    RandomIt left_it = first;
    RandomIt right_it = std::find_if(first, last, [pred](T x) { return !pred(x); });
    std::vector<T> buffer;
    for (RandomIt it = first; it < last; it++) {
        if (placement(it)) {
            buffer.push_back(*left_it);
            left_it++;
        } else {
            buffer.push_back(*right_it);
            right_it++;
        }
    }
    std::ranges::copy(buffer, first);
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
    inplace_stable_partition_stub(first, last, [&](T x) { return proj(x) != proj(major); });
    RandomIt major_it =
        std::ranges::find_if(first, last, [&](T x) { return proj(x) == proj(major); });
    std::ranges::rotate(first + buffer_len, major_it, major_it + buffer_len);
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
        inplace_stable_partition_stub(first, last, [&](T x) { return proj(x) != proj(major); });
        RandomIt major_it =
            std::ranges::find_if(first, last, [&](T x) { return proj(x) == proj(major); });
        bubble_sort(first, major_it, proj);
        std::ranges::rotate(
            std::ranges::find_if(first, major_it, [&](T x) { return proj(x) >= proj(major); }),
            major_it, last);
        return;
    }
    std::ranges::stable_sort(
        first, last, {}, proj);  // TODO: implement proper inplace stable select
}
}  // namespace inplace_stable_select
}  // namespace tcs
