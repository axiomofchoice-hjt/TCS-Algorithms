#pragma once

#include <algorithm>
#include <cmath>
#include <format>
#include <functional>
#include <source_location>
#include <stdexcept>
#include <string_view>

namespace tcs {
namespace inplace_unstable_merge {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

template <typename RandomIt, typename Proj = std::identity>
void merge_with_swap(RandomIt output, RandomIt first, RandomIt mid, RandomIt last, Proj proj = {}) {
    RandomIt left_it = first;
    RandomIt right_it = mid;
    while (left_it < mid || right_it < last) {
        if (right_it == last || (left_it < mid && proj(*left_it) <= proj(*right_it))) {
            std::swap(*output, *left_it);
            output++;
            left_it++;
        } else {
            std::swap(*output, *right_it);
            output++;
            right_it++;
        }
    }
}

template <typename RandomIt, typename Proj = std::identity>
void inplace_merge_with_rotation(RandomIt first, RandomIt mid, RandomIt last, Proj proj = {}) {
    if (mid - first < last - mid) {
        while (first < mid && mid < last) {
            RandomIt split_right = mid;
            while (split_right < last && proj(*split_right) < proj(*first)) {
                split_right++;
            }
            std::ranges::rotate(first, mid, split_right);
            first += (split_right - mid) + 1;
            mid = split_right;
        }
    } else {
        while (first < mid && mid < last) {
            RandomIt split_left = mid;
            while (split_left > first && proj(*(split_left - 1)) > proj(*(last - 1))) {
                split_left--;
            }
            std::ranges::rotate(split_left, mid, last);
            last -= (mid - split_left) + 1;
            mid = split_left;
        }
    }
}

template <typename RandomIt, typename Proj = std::identity>
void block_selection_sort(RandomIt first, RandomIt last, int64_t block_size, Proj proj = {}) {
    for (RandomIt cur = first; cur < last; cur += block_size) {
        RandomIt min = cur;
        for (RandomIt scan = cur + block_size; scan < last; scan += block_size) {
            if (std::pair{proj(*min), proj(*(min + block_size - 1))} >
                std::pair{proj(*scan), proj(*(scan + block_size - 1))}) {
                min = scan;
            }
        }
        if (min != cur) {
            std::swap_ranges(cur, cur + block_size, min);
        }
    }
}

template <typename RandomIt, typename Proj = std::identity>
void block_merge_pairwise(RandomIt first, RandomIt last, int64_t block_size, Proj proj = {}) {
    int64_t n_blocks = (last - first) / block_size;
    for (int64_t i = 0; i + 2 < n_blocks; i++) {
        merge_with_swap(first + (i * block_size), first + ((i + 1) * block_size),
            first + ((i + 2) * block_size), first + ((i + 3) * block_size), proj);
        if (i + 3 < n_blocks) {
            std::swap_ranges(first + ((i + 1) * block_size), first + ((i + 2) * block_size),
                first + ((i + 2) * block_size));
        }
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
void inplace_unstable_merge(RandomIt first, RandomIt mid, RandomIt last, Proj proj = {}) {
    assert_or_throw(first <= mid && mid <= last, "Error: invalid input");
    assert_or_throw(std::ranges::is_sorted(first, mid, std::less{}, proj), "Error: invalid input");
    assert_or_throw(std::ranges::is_sorted(mid, last, std::less{}, proj), "Error: invalid input");
    int64_t len = last - first;
    if (len <= 1) {
        return;
    }
    int64_t left_len = mid - first;
    int64_t right_len = last - mid;
    int64_t block_size = std::floor(std::sqrt(left_len + right_len));
    int64_t left_aligned_len = left_len / block_size * block_size;
    int64_t right_aligned_len = right_len / block_size * block_size;
    int64_t aligned_len = left_aligned_len + right_aligned_len;

    std::ranges::rotate(first + left_aligned_len, mid, mid + right_aligned_len);
    block_selection_sort(first, first + aligned_len, block_size, proj);
    block_merge_pairwise(first, first + aligned_len, block_size, proj);
    bubble_sort(first + aligned_len - block_size, last, proj);
    inplace_merge_with_rotation(first, first + aligned_len - block_size, last, proj);
}
}  // namespace inplace_unstable_merge
}  // namespace tcs
