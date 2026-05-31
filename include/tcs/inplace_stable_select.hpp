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
RandomIt strided_min_element(RandomIt first, RandomIt last, int64_t stride, Proj proj = {}) {
    assert_or_throw((last - first) % stride == 0);
    RandomIt min_it = first;
    for (RandomIt i = first; i < last; i += stride) {
        if (proj(*i) < proj(*min_it)) {
            min_it = i;
        }
    }
    return min_it;
}

template <typename RandomIt, typename Proj = std::identity>
RandomIt strided_next_element(
    RandomIt first, RandomIt last, int64_t stride, RandomIt x, Proj proj = {}) {
    assert_or_throw((last - first) % stride == 0);
    RandomIt next_it = last;
    for (RandomIt i = first; i < last; i += stride) {
        if (std::pair{proj(*x), x} < std::pair{proj(*i), i} &&
            (next_it == last || std::pair{proj(*i), i} < std::pair{proj(*next_it), next_it})) {
            next_it = i;
        }
    }
    return next_it;
}

template <typename RandomIt, typename Proj = std::identity>
void inplace_stable_select(RandomIt first, RandomIt mid, RandomIt last, Proj proj = {}) {
    using T = typename std::iterator_traits<RandomIt>::value_type;
    assert_or_throw(first <= mid && mid < last);
    int64_t len = last - first;
    if (len < 4) {
        bubble_sort(first, last, proj);
        return;
    }
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
    RandomIt main = first + (buffer_len * 2);
    int64_t block_size = static_cast<int64_t>(std::floor(std::sqrt(len)));
    int64_t n_blocks = (last - main) / block_size;
    if (n_blocks == 0) {
        bubble_sort(first, last, proj);
        return;
    }
    for (int64_t i = 0; i < n_blocks; i++) {
        RandomIt start = main + (i * block_size);
        RandomIt end = main + ((i + 1) * block_size);
        std::ranges::stable_sort(start, end, {}, proj);  // TODO: not implemented
        T median = start[block_size / 2];
        RandomIt median_it =
            std::ranges::find_if(start, end, [&](T x) { return proj(x) == proj(median); });
        std::ranges::rotate(start, median_it, median_it + 1);
    }

    RandomIt last_aligned = main + (n_blocks * block_size);
    RandomIt median_it = strided_min_element(main, last_aligned, block_size, proj);
    for (int64_t i = 0; i < (n_blocks - 1) / 2; i++) {
        median_it = strided_next_element(main, last_aligned, block_size, median_it, proj);
    }
    T median = *median_it;
    inplace_stable_partition_stub(first, last, [&](T x) { return proj(x) < proj(median); });
    RandomIt median_start =
        std::ranges::find_if(first, last, [&](T x) { return proj(x) >= proj(median); });
    inplace_stable_partition_stub(median_start, last, [&](T x) { return proj(x) == proj(median); });
    RandomIt median_end =
        std::ranges::find_if(median_start, last, [&](T x) { return proj(x) != proj(median); });
    if (mid < median_start) {
        inplace_stable_select(first, mid, median_start, proj);
    }
    if (mid >= median_end) {
        inplace_stable_select(median_end, mid, last, proj);
    }
}
}  // namespace inplace_stable_select
}  // namespace tcs
