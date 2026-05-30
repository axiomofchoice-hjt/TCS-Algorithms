#pragma once

#include <algorithm>
#include <cmath>
#include <format>
#include <functional>
#include <source_location>
#include <stdexcept>
#include <string_view>

namespace tcs {
namespace inplace_stable_merge {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

template <typename RandomIt, typename Proj = std::identity>
std::tuple<RandomIt, RandomIt, RandomIt> merge_with_swap(
    RandomIt output, RandomIt first, RandomIt mid, RandomIt last, RandomIt labels, Proj proj = {}) {
    RandomIt left_ptr = first;
    RandomIt right_ptr = mid;
    while (left_ptr < mid && right_ptr < last) {
        if (std::pair{proj(*left_ptr), proj(labels[1])} <=
            std::pair{proj(*right_ptr), proj(labels[2])}) {
            std::swap(*output, *left_ptr);
            output++;
            left_ptr++;
        } else {
            std::swap(*output, *right_ptr);
            output++;
            right_ptr++;
        }
    }
    if (left_ptr < mid) {
        int64_t remain = mid - left_ptr;
        std::swap_ranges(left_ptr, mid, last - remain);
        std::swap(labels[1], labels[2]);
        return {output, last - remain, last};
    }
    return {output, right_ptr, last};
}

template <typename RandomIt, typename Proj = std::identity>
void inplace_merge_with_rotation_scroll_right(
    RandomIt first, RandomIt mid, RandomIt last, Proj proj = {}) {
    while (first < mid && mid < last) {
        RandomIt split_right = mid;
        while (split_right < last && proj(*split_right) < proj(*first)) {
            split_right++;
        }
        if (mid != split_right) {
            std::ranges::rotate(first, mid, split_right);
        }
        first += (split_right - mid);
        mid = split_right;
        if (mid != last) {
            first++;
            while (first < mid && proj(*first) == proj(*(first - 1))) {
                first++;
            }
        }
    }
}

template <typename RandomIt, typename Proj = std::identity>
void inplace_merge_with_rotation_scroll_left(
    RandomIt first, RandomIt mid, RandomIt last, Proj proj = {}) {
    while (first < mid && mid < last) {
        RandomIt split_left = mid;
        while (split_left > first && proj(*(split_left - 1)) > proj(*(last - 1))) {
            split_left--;
        }
        if (mid != split_left) {
            std::ranges::rotate(split_left, mid, last);
        }
        last -= (mid - split_left);
        mid = split_left;
        if (first != mid) {
            last--;
            while (mid < last && proj(*last) == proj(*(last - 1))) {
                last--;
            }
        }
    }
}

template <typename RandomIt, typename Proj = std::identity>
void inplace_merge_with_rotation(RandomIt first, RandomIt mid, RandomIt last, Proj proj = {}) {
    if (mid - first < last - mid) {  // left array scrolls right O(l * l' + r)
        inplace_merge_with_rotation_scroll_right(first, mid, last, proj);
    } else {  // right array scrolls left O(l + r * r')
        inplace_merge_with_rotation_scroll_left(first, mid, last, proj);
    }
}

template <typename RandomIt, typename Proj = std::identity>
std::tuple<RandomIt, RandomIt> inplace_merge_with_rotation_indexed(
    RandomIt first, RandomIt mid, RandomIt last, RandomIt labels, Proj proj = {}) {
    while (first < mid && mid < last) {
        RandomIt split_right = mid;
        while (split_right < last && std::pair{proj(*split_right), proj(labels[1])} <
                                         std::pair{proj(*first), proj(labels[0])}) {
            split_right++;
        }
        if (mid != split_right) {
            std::ranges::rotate(first, mid, split_right);
        }
        first += (split_right - mid);
        mid = split_right;
        if (mid != last) {
            first++;
            while (first < mid && proj(*first) == proj(*(first - 1))) {
                first++;
            }
        }
    }
    if (first != mid) {
        std::swap(labels[0], labels[1]);
    }
    return {first, last};
}

template <typename RandomIt, typename Proj = std::identity>
std::tuple<RandomIt, RandomIt, RandomIt> stable_unique_limit(
    RandomIt first, RandomIt last, int64_t max, Proj proj = {}) {
    RandomIt left = first;
    RandomIt right = first;
    int64_t len = 0;
    for (RandomIt iter = first; iter < last; iter++) {
        if (len < max && (left == right || proj(*(right - 1)) != proj(*iter))) {
            std::ranges::rotate(left, right, iter);
            len++;
            right = iter + 1;
            left = right - len;
        }
    }
    std::ranges::rotate(first, left, right);
    return {first, first + len, last};
}

template <typename RandomIt, typename Proj = std::identity>
std::tuple<RandomIt, RandomIt, RandomIt, RandomIt> stable_unique_limit(
    RandomIt first, RandomIt mid, RandomIt last, int64_t max, Proj proj = {}) {
    RandomIt original_mid;
    RandomIt original_first;
    std::tie(original_mid, mid, last) = stable_unique_limit(mid, last, max, proj);
    inplace_merge_with_rotation(first, original_mid, mid, proj);
    std::tie(original_first, first, mid) = stable_unique_limit(first, mid, max, proj);
    return {original_first, first, mid, last};
}

template <typename RandomIt, typename Proj = std::identity>
std::tuple<RandomIt, RandomIt, RandomIt, RandomIt> align_blocks_limit(RandomIt first, RandomIt mid,
    RandomIt last, int64_t block_size, int64_t n_blocks, Proj proj = {}) {
    assert_or_throw(block_size > 0 && n_blocks > 0);
    assert_or_throw(block_size * n_blocks <= static_cast<int64_t>(last - first));
    RandomIt original_mid = mid;
    RandomIt original_last = last;
    mid = first + ((mid - first) / block_size * block_size);
    inplace_merge_with_rotation(mid, original_mid, last, proj);
    last = first + (block_size * n_blocks);
    if (mid > last) {
        inplace_merge_with_rotation(last, mid, original_last, proj);
        mid = last;
    }
    return {first, mid, last, original_last};
}

template <typename RandomIt, typename Proj = std::identity>
void block_selection_sort(
    RandomIt first, RandomIt last, RandomIt labels, int64_t block_size, Proj proj = {}) {
    int64_t n_blocks = (last - first) / block_size;
    for (int64_t cur = 0; cur < n_blocks; cur++) {
        int64_t min = cur;
        for (int64_t scan = cur + 1; scan < n_blocks; scan++) {
            if (std::pair{proj(first[min * block_size]), proj(labels[min])} >
                std::pair{proj(first[scan * block_size]), proj(labels[scan])}) {
                min = scan;
            }
        }
        if (min != cur) {
            std::swap_ranges(first + (cur * block_size), first + ((cur + 1) * block_size),
                first + (min * block_size));
            std::swap(labels[cur], labels[min]);
        }
    }
}

template <typename RandomIt, typename Proj = std::identity>
void block_merge_pairwise(
    RandomIt first, RandomIt last, RandomIt labels, int64_t block_size, Proj proj = {}) {
    int64_t n_blocks = (last - first) / block_size;
    RandomIt buffer = first;
    for (int64_t i = 0; i + 2 < n_blocks; i++) {
        std::tie(buffer, std::ignore, std::ignore) = merge_with_swap(buffer, buffer + block_size,
            first + ((i + 2) * block_size), first + ((i + 3) * block_size), labels + i, proj);
    }
    std::ranges::rotate(first, buffer, buffer + block_size);
}

template <typename RandomIt, typename Proj = std::identity>
void inplace_block_merge_pairwise(
    RandomIt first, RandomIt last, RandomIt labels, int64_t block_size, Proj proj = {}) {
    int64_t n_blocks = (last - first) / block_size;
    RandomIt start = first;
    for (int64_t i = 0; i + 1 < n_blocks; i++) {
        std::tie(start, std::ignore) = inplace_merge_with_rotation_indexed(start,
            first + ((i + 1) * block_size), first + ((i + 2) * block_size), labels + i, proj);
    }
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
void inplace_stable_merge(RandomIt first, RandomIt mid, RandomIt last, Proj proj = {}) {
    assert_or_throw(first <= mid && mid <= last, "Error: invalid input");
    assert_or_throw(std::ranges::is_sorted(first, mid, std::less{}, proj), "Error: invalid input");
    assert_or_throw(std::ranges::is_sorted(mid, last, std::less{}, proj), "Error: invalid input");
    int64_t len = last - first;
    int64_t block_size = std::floor(std::sqrt(len));
    if (block_size <= 4) {
        bubble_sort(first, last, proj);
        return;
    }
    int64_t n_blocks = len / block_size;
    RandomIt buf1;
    std::tie(buf1, first, mid, last) =
        stable_unique_limit(first, mid, last, n_blocks + block_size, proj);
    // buf1 [buffer] first [left_elements] mid [right_elements]
    assert_or_throw(std::ranges::is_sorted(buf1, first, std::less{}, proj));
    int64_t buffer_len = first - buf1;
    if (buffer_len == n_blocks + block_size) {  // enough unique values
        n_blocks = (last - first) / block_size;
        RandomIt original_last;
        std::tie(first, mid, last, original_last) =
            align_blocks_limit(first, mid, last, block_size, n_blocks, proj);
        // buf1 [buffer] first [left_elements_aligned] mid
        // [right_elements_aligned] last [tail_elements] original_last
        RandomIt buf2 = first - block_size;
        block_selection_sort(first, last, buf1 + 1, block_size, proj);
        block_merge_pairwise(buf2, last, buf1, block_size, proj);
        bubble_sort(buf1, first, proj);
        inplace_merge_with_rotation(buf1, first, last, proj);
        first = buf1;
        inplace_merge_with_rotation(first, last, original_last, proj);
    } else {
        block_size = (len - buffer_len) / buffer_len;
        RandomIt original_last;
        std::tie(first, mid, last, original_last) =
            align_blocks_limit(first, mid, last, block_size, buffer_len, proj);
        block_selection_sort(first, last, buf1, block_size, proj);
        inplace_block_merge_pairwise(first, last, buf1, block_size, proj);
        bubble_sort(buf1, first, proj);
        inplace_merge_with_rotation(buf1, first, last, proj);
        first = buf1;
        inplace_merge_with_rotation(first, last, original_last, proj);
    }
}
}  // namespace inplace_stable_merge
}  // namespace tcs
