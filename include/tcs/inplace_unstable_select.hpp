#pragma once

#include <algorithm>
#include <array>
#include <bit>
#include <climits>
#include <cstdint>
#include <utility>
#include <format>
#include <source_location>
#include <stdexcept>
#include <string_view>

namespace tcs {
namespace inplace_unstable_select {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

inline int64_t ceil_log2(int64_t x) {
    assert_or_throw(x > 0);
    return std::bit_width(static_cast<uint64_t>(x) - 1);
}

struct BitStackAttributes {
    int64_t word_bits;
    int64_t element_bits;
};

template <int64_t N>
struct BitStack {
    int64_t word_bits;
    int64_t element_bits;
    int64_t size = 0;
    std::array<uint64_t, N> storage = {};

    static BitStack create(BitStackAttributes attr) {
        assert_or_throw(attr.word_bits > 0 && attr.word_bits <= int64_t{sizeof(uint64_t) * CHAR_BIT});
        assert_or_throw(attr.element_bits > 0);
        return BitStack{.word_bits = attr.word_bits, .element_bits = attr.element_bits};
    }

    bool empty() const { return size == 0; }

    void push(uint64_t value) {
        assert_or_throw((size + 1) * element_bits <= N * word_bits);
        assert_or_throw(ceil_log2(static_cast<int64_t>(value + 1)) <= element_bits);
        for (int64_t i = 0; i < element_bits; i++) {
            int64_t bit_offset = (size * element_bits) + i;
            storage[bit_offset / word_bits] &= ~(uint64_t{1} << (bit_offset % word_bits));
            storage[bit_offset / word_bits] |= ((value >> i) & 1) << (bit_offset % word_bits);
        }
        size++;
    }

    uint64_t pop() {
        assert_or_throw(size > 0);
        size--;
        uint64_t res = 0;
        for (int64_t i = 0; i < element_bits; i++) {
            int64_t bit_offset = (size * element_bits) + i;
            res |= (storage[bit_offset / word_bits] >> (bit_offset % word_bits) & 1) << i;
        }
        return res;
    }
};

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
bool prepare_buffer(T* first, T* last, int64_t n_bits) {
    T* majority_ptr = first;
    for (T* iter = first; iter < last; iter++) {
        if (majority_ptr - first == n_bits * 2) {
            break;
        }
        if (majority_ptr < iter && *majority_ptr != *iter) {
            std::swap(*majority_ptr, *iter);
            majority_ptr += 2;
        }
    }
    return majority_ptr - first == n_bits * 2;
}

template <typename T>
bool write_buffer(T* buffer, uint64_t value, int64_t n_bits) {
    assert_or_throw(ceil_log2(static_cast<int64_t>(value + 1)) <= n_bits);

    for (int64_t i = 0; i < n_bits; i++) {
        assert_or_throw(buffer[i * 2] != buffer[(i * 2) + 1]);
        if ((buffer[i * 2] > buffer[(i * 2) + 1]) != ((value >> i) & 1)) {
            std::swap(buffer[i * 2], buffer[(i * 2) + 1]);
        }
    }
    return true;
}

template <typename T>
uint64_t read_buffer(T* buffer, int64_t n_bits) {
    uint64_t res = 0;
    for (int64_t i = 0; i < n_bits; i++) {
        assert_or_throw(buffer[i * 2] != buffer[(i * 2) + 1]);
        res |= (buffer[i * 2] > buffer[(i * 2) + 1] ? uint64_t{1} : uint64_t{0}) << i;
    }
    return res;
}

template <typename T>
void move_largest_to_end(T* first, T* mid, T* last) {
    int64_t right_size = last - mid;
    for (int64_t i = 0; i < right_size; i++) {
        std::swap(*std::max_element(first, last - i), *(last - i - 1));
    }
}

namespace Stage {
static constexpr uint64_t median_of_medians = 0;
static constexpr uint64_t partition = 1;
static constexpr uint64_t restore_right = 2;
static constexpr uint64_t restore_left = 3;
}  // namespace Stage

template <typename T>
void inplace_unstable_select(T* first, T* mid, T* last) {
    constexpr int64_t group_size = 5;
    constexpr int64_t shrink_num = (group_size + 1) / 2;  // 3
    constexpr int64_t shrink_den = group_size * 2;        // 10
    constexpr int64_t alignment = group_size * 2;         // 10
    int64_t len = last - first;
    if (len < alignment) {
        bubble_sort(first, last);
        return;
    }
    int64_t word_bits = ceil_log2(len);
    constexpr int64_t max_stage_size = 4;
    constexpr int64_t max_tail_size = 8;
    BitStack<max_stage_size> stages{word_bits, 2};
    BitStack<max_tail_size> tail_sizes{word_bits, 4};
    int64_t k = mid - first;
    stages.push(Stage::median_of_medians);
    while (!stages.empty()) {
        uint64_t stage = stages.pop();
        if (stage == Stage::median_of_medians) {
            int64_t len = last - first;
            // align to alignment
            T* tail = first + (len % alignment);
            int64_t aligned_len = tail - first;
            move_largest_to_end(first, tail, last);
            if (k >= aligned_len) {
                continue;
            }
            // median of medians of each group
            for (int64_t i = 0; i + group_size <= aligned_len; i += group_size) {
                bubble_sort(first + i, first + i + group_size);
                std::swap(first[i / group_size], first[i + (group_size / 2)]);
            }
            // prepare buffer
            T* buffer = first + (aligned_len / group_size);
            if (!prepare_buffer(buffer, tail, word_bits)) {
                T possible_majority = *(tail - 1);
                T* mid = std::partition(first, tail, [&](T x) { return x != possible_majority; });
                bubble_sort(first, mid);
                std::rotate(std::find_if(first, mid, [&](T x) { return x >= possible_majority; }), mid, tail);
                continue;
            }
            // store (k, tail_size)
            write_buffer(buffer, k, word_bits);
            stages.push(Stage::partition);
            tail_sizes.push(last - tail);
            stages.push(Stage::median_of_medians);
            k = aligned_len / group_size / 2;
            last = first + (aligned_len / group_size);
        } else if (stage == Stage::partition) {
            T pivot = first[k];
            // restore (first, last, k)
            k = read_buffer(last, word_bits);
            int64_t len = last - first;
            last += len * (group_size - 1);
            len = last - first;
            // three-way partition
            T* pivot_start = std::partition(first, last, [pivot](T el) { return el < pivot; });
            T* pivot_end = std::partition(pivot_start, last, [pivot](T el) { return el == pivot; });
            T* kth = first + k;
            if (kth < pivot_start) {
                // shrink right
                last -= len * shrink_num / shrink_den;  // len * 3 / 10
                stages.push(Stage::restore_right);
                stages.push(Stage::median_of_medians);
            } else if (kth >= pivot_end) {
                // shrink left
                first += len * shrink_num / shrink_den;  // len * 3 / 10
                k -= len * shrink_num / shrink_den;      // len * 3 / 10
                stages.push(Stage::restore_left);
                stages.push(Stage::median_of_medians);
            } else {
                last += tail_sizes.pop();
            }
        } else if (stage == Stage::restore_right) {
            // restore (first, last, k)
            int64_t len = last - first;
            assert_or_throw(len % (shrink_den - shrink_num) == 0);
            last += len * shrink_num / (shrink_den - shrink_num);
            last += tail_sizes.pop();
        } else if (stage == Stage::restore_left) {
            // restore (first, last, k)
            int64_t len = last - first;
            assert_or_throw(len % (shrink_den - shrink_num) == 0);
            first -= len * shrink_num / (shrink_den - shrink_num);
            k += len * shrink_num / (shrink_den - shrink_num);
            last += tail_sizes.pop();
        }
    }
}
}  // namespace inplace_unstable_select
}  // namespace tcs
