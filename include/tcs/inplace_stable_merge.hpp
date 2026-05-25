#pragma once

#include <algorithm>
#include <cmath>
#include <format>
#include <source_location>
#include <stdexcept>
#include <string_view>

namespace tcs {
namespace inplace_stable_merge {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

template <typename T>
std::tuple<T*, T*, T*> merge_with_swap(T* output, T* first, T* mid, T* last, T* labels) {
    T* left_ptr = first;
    T* right_ptr = mid;
    while (left_ptr < mid && right_ptr < last) {
        if (std::pair{*left_ptr, labels[1]} <= std::pair{*right_ptr, labels[2]}) {
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

template <typename T>
void inplace_merge_with_rotation_scroll_right(T* first, T* mid, T* last) {
    while (first < mid && mid < last) {
        T* split_right = mid;
        while (split_right < last && *split_right < *first) {
            split_right++;
        }
        if (mid != split_right) {
            std::rotate(first, mid, split_right);
        }
        first += (split_right - mid);
        mid = split_right;
        if (mid != last) {
            first++;
            while (first < mid && *first == *(first - 1)) {
                first++;
            }
        }
    }
}

template <typename T>
void inplace_merge_with_rotation_scroll_left(T* first, T* mid, T* last) {
    while (first < mid && mid < last) {
        T* split_left = mid;
        while (split_left > first && *(split_left - 1) > *(last - 1)) {
            split_left--;
        }
        if (mid != split_left) {
            std::rotate(split_left, mid, last);
        }
        last -= (mid - split_left);
        mid = split_left;
        if (first != mid) {
            last--;
            while (mid < last && *last == *(last - 1)) {
                last--;
            }
        }
    }
}

template <typename T>
void inplace_merge_with_rotation(T* first, T* mid, T* last) {
    if (mid - first < last - mid) {  // left array scrolls right O(l * l' + r)
        inplace_merge_with_rotation_scroll_right(first, mid, last);
    } else {  // right array scrolls left O(l + r * r')
        inplace_merge_with_rotation_scroll_left(first, mid, last);
    }
}

template <typename T>
std::tuple<T*, T*> inplace_merge_with_rotation_indexed(T* first, T* mid, T* last, T* labels) {
    while (first < mid && mid < last) {
        T* split_right = mid;
        while (split_right < last && std::pair{*split_right, labels[1]} < std::pair{*first, labels[0]}) {
            split_right++;
        }
        if (mid != split_right) {
            std::rotate(first, mid, split_right);
        }
        first += (split_right - mid);
        mid = split_right;
        if (mid != last) {
            first++;
            while (first < mid && *first == *(first - 1)) {
                first++;
            }
        }
    }
    if (first != mid) {
        std::swap(labels[0], labels[1]);
    }
    return {first, last};
}

template <typename T>
std::tuple<T*, T*, T*> stable_unique_limit(T* first, T* last, int64_t max) {
    T* left = first;
    T* right = first;
    int64_t len = 0;
    for (T* iter = first; iter < last; iter++) {
        if (len < max && (left == right || *(right - 1) != *iter)) {
            std::rotate(left, right, iter);
            len++;
            right = iter + 1;
            left = right - len;
        }
    }
    std::rotate(first, left, right);
    return {first, first + len, last};
}

template <typename T>
std::tuple<T*, T*, T*, T*> stable_unique_limit(T* first, T* mid, T* last, int64_t max) {
    T* original_mid;
    T* original_first;
    std::tie(original_mid, mid, last) = stable_unique_limit(mid, last, max);
    inplace_merge_with_rotation(first, original_mid, mid);
    std::tie(original_first, first, mid) = stable_unique_limit(first, mid, max);
    return {original_first, first, mid, last};
}

template <typename T>
std::tuple<T*, T*, T*, T*> align_blocks_limit(T* first, T* mid, T* last, int64_t block_size, int64_t n_blocks) {
    assert_or_throw(block_size > 0 && n_blocks > 0);
    assert_or_throw(block_size * n_blocks <= static_cast<int64_t>(last - first));
    T* original_mid = mid;
    T* original_last = last;
    mid = first + ((mid - first) / block_size * block_size);
    inplace_merge_with_rotation(mid, original_mid, last);
    last = first + (block_size * n_blocks);
    if (mid > last) {
        inplace_merge_with_rotation(last, mid, original_last);
        mid = last;
    }
    return {first, mid, last, original_last};
}

template <typename T>
void block_selection_sort(T* first, T* last, T* labels, int64_t block_size) {
    int64_t n_blocks = (last - first) / block_size;
    for (int64_t cur = 0; cur < n_blocks; cur++) {
        int64_t min = cur;
        for (int64_t scan = cur + 1; scan < n_blocks; scan++) {
            if (std::pair{first[min * block_size], labels[min]} > std::pair{first[scan * block_size], labels[scan]}) {
                min = scan;
            }
        }
        if (min != cur) {
            std::swap_ranges(first + (cur * block_size), first + ((cur + 1) * block_size), first + (min * block_size));
            std::swap(labels[cur], labels[min]);
        }
    }
}

template <typename T>
void block_merge_pairwise(T* first, T* last, T* labels, int64_t block_size) {
    int64_t n_blocks = (last - first) / block_size;
    T* buffer = first;
    for (int64_t i = 0; i + 2 < n_blocks; i++) {
        std::tie(buffer, std::ignore, std::ignore) = merge_with_swap(
            buffer, buffer + block_size, first + ((i + 2) * block_size), first + ((i + 3) * block_size), labels + i);
    }
    std::rotate(first, buffer, buffer + block_size);
}

template <typename T>
void inplace_block_merge_pairwise(T* first, T* last, T* labels, int64_t block_size) {
    int64_t n_blocks = (last - first) / block_size;
    T* start = first;
    for (int64_t i = 0; i + 1 < n_blocks; i++) {
        std::tie(start, std::ignore) = inplace_merge_with_rotation_indexed(
            start, first + ((i + 1) * block_size), first + ((i + 2) * block_size), labels + i);
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
void inplace_stable_merge(T* first, T* mid, T* last) {
    assert_or_throw(first <= mid && mid <= last, "Error: invalid input");
    assert_or_throw(std::is_sorted(first, mid), "Error: invalid input");
    assert_or_throw(std::is_sorted(mid, last), "Error: invalid input");
    int64_t len = last - first;
    int64_t block_size = std::floor(std::sqrt(len));
    if (block_size <= 4) {
        bubble_sort(first, last);
        return;
    }
    int64_t n_blocks = len / block_size;
    T* buf1;
    std::tie(buf1, first, mid, last) = stable_unique_limit(first, mid, last, n_blocks + block_size);
    // buf1 [buffer] first [left_elements] mid [right_elements]
    assert_or_throw(std::is_sorted(buf1, first));
    int64_t buffer_len = first - buf1;
    if (buffer_len == n_blocks + block_size) {  // enough unique values
        n_blocks = (last - first) / block_size;
        T* original_last;
        std::tie(first, mid, last, original_last) = align_blocks_limit(first, mid, last, block_size, n_blocks);
        // buf1 [buffer] first [left_elements_aligned] mid
        // [right_elements_aligned] last [tail_elements] original_last
        T* buf2 = first - block_size;
        block_selection_sort(first, last, buf1 + 1, block_size);
        block_merge_pairwise(buf2, last, buf1, block_size);
        bubble_sort(buf1, first);
        inplace_merge_with_rotation(buf1, first, last);
        first = buf1;
        inplace_merge_with_rotation(first, last, original_last);
    } else {
        block_size = (len - buffer_len) / buffer_len;
        T* original_last;
        std::tie(first, mid, last, original_last) = align_blocks_limit(first, mid, last, block_size, buffer_len);
        block_selection_sort(first, last, buf1, block_size);
        inplace_block_merge_pairwise(first, last, buf1, block_size);
        bubble_sort(buf1, first);
        inplace_merge_with_rotation(buf1, first, last);
        first = buf1;
        inplace_merge_with_rotation(first, last, original_last);
    }
}
}  // namespace inplace_stable_merge
}  // namespace tcs
