#pragma once

#include <algorithm>
#include <cmath>
#include <format>
#include <source_location>
#include <stdexcept>
#include <string_view>

namespace tcs {
namespace inplace_unstable_merge {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

template <typename T>
void merge_with_swap(T* output, T* first, T* mid, T* last) {
    T* left_ptr = first;
    T* right_ptr = mid;
    while (left_ptr < mid || right_ptr < last) {
        if (right_ptr == last || (left_ptr < mid && *left_ptr <= *right_ptr)) {
            std::swap(*output, *left_ptr);
            output++;
            left_ptr++;
        } else {
            std::swap(*output, *right_ptr);
            output++;
            right_ptr++;
        }
    }
}

template <typename T>
void inplace_merge_with_rotation(T* first, T* mid, T* last) {
    if (mid - first < last - mid) {  // left array scrolls right O(l^2 + r)
        while (first < mid && mid < last) {
            T* split_right = mid;
            while (split_right < last && *split_right < *first) {
                split_right++;
            }
            std::rotate(first, mid, split_right);
            first += (split_right - mid) + 1;
            mid = split_right;
        }
    } else {  // right array scrolls left O(l + r^2)
        while (first < mid && mid < last) {
            T* split_left = mid;
            while (split_left > first && *(split_left - 1) > *(last - 1)) {
                split_left--;
            }
            std::rotate(split_left, mid, last);
            last -= (mid - split_left) + 1;
            mid = split_left;
        }
    }
}

template <typename T>
void block_selection_sort(T* first, T* last, int64_t block_size) {
    for (T* cur = first; cur < last; cur += block_size) {
        T* min = cur;
        for (T* scan = cur + block_size; scan < last; scan += block_size) {
            if (std::pair{*min, *(min + block_size - 1)} > std::pair{*scan, *(scan + block_size - 1)}) {
                min = scan;
            }
        }
        if (min != cur) {
            std::swap_ranges(cur, cur + block_size, min);
        }
    }
}

template <typename T>
void block_merge_pairwise(T* first, T* last, int64_t block_size) {
    int64_t n_blocks = (last - first) / block_size;
    for (int64_t i = 0; i + 2 < n_blocks; i++) {
        merge_with_swap(first + (i * block_size), first + ((i + 1) * block_size), first + ((i + 2) * block_size),
            first + ((i + 3) * block_size));
        if (i + 3 < n_blocks) {
            std::swap_ranges(
                first + ((i + 1) * block_size), first + ((i + 2) * block_size), first + ((i + 2) * block_size));
        }
    }
}

template <typename T>
void bubble_sort(T* first, T* last) {
    int64_t len = last - first;
    for (int64_t i = 0; i + 1 < len; i++) {
        for (T* j = first; j < last - i - 1; j++) {
            if (*j > *(j + 1)) {
                std::swap(*j, *(j + 1));
            }
        }
    }
}

template <typename T>
void inplace_unstable_merge(T* first, T* mid, T* last) {
    assert_or_throw(first <= mid && mid <= last, "Error: invalid input");
    assert_or_throw(std::is_sorted(first, mid), "Error: invalid input");
    assert_or_throw(std::is_sorted(mid, last), "Error: invalid input");
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

    // blocking and alignment
    std::rotate(first + left_aligned_len, mid, mid + right_aligned_len);
    // inter-block sorting
    block_selection_sort(first, first + aligned_len, block_size);
    // inter-block merging
    block_merge_pairwise(first, first + aligned_len, block_size);
    // handle tail elements
    bubble_sort(first + aligned_len - block_size, last);
    inplace_merge_with_rotation(first, first + aligned_len - block_size, last);
}
}  // namespace inplace_unstable_merge
}  // namespace tcs
