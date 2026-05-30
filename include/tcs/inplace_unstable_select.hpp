#pragma once

#include <algorithm>
#include <array>
#include <bit>
#include <climits>
#include <cstdint>
#include <format>
#include <functional>
#include <source_location>
#include <stdexcept>
#include <string_view>
#include <utility>

namespace tcs {
namespace inplace_unstable_select {
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
        assert_or_throw(
            attr.word_bits > 0 && attr.word_bits <= int64_t{sizeof(uint64_t) * CHAR_BIT});
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
bool prepare_buffer(RandomIt first, RandomIt last, int64_t n_bits, Proj proj = {}) {
    RandomIt majority_ptr = first;
    for (RandomIt iter = first; iter < last; iter++) {
        if (majority_ptr - first == n_bits * 2) {
            break;
        }
        if (majority_ptr < iter && proj(*majority_ptr) != proj(*iter)) {
            std::swap(*majority_ptr, *iter);
            majority_ptr += 2;
        }
    }
    return majority_ptr - first == n_bits * 2;
}

template <typename RandomIt, typename Proj = std::identity>
bool write_buffer(RandomIt buffer, uint64_t value, int64_t n_bits, Proj proj = {}) {
    assert_or_throw(ceil_log2(static_cast<int64_t>(value + 1)) <= n_bits);

    for (int64_t i = 0; i < n_bits; i++) {
        assert_or_throw(proj(buffer[i * 2]) != proj(buffer[(i * 2) + 1]));
        if ((proj(buffer[i * 2]) > proj(buffer[(i * 2) + 1])) != ((value >> i) & 1)) {
            std::swap(buffer[i * 2], buffer[(i * 2) + 1]);
        }
    }
    return true;
}

template <typename RandomIt, typename Proj = std::identity>
uint64_t read_buffer(RandomIt buffer, int64_t n_bits, Proj proj = {}) {
    uint64_t res = 0;
    for (int64_t i = 0; i < n_bits; i++) {
        assert_or_throw(proj(buffer[i * 2]) != proj(buffer[(i * 2) + 1]));
        res |= (proj(buffer[i * 2]) > proj(buffer[(i * 2) + 1]) ? uint64_t{1} : uint64_t{0}) << i;
    }
    return res;
}

template <typename RandomIt, typename Proj = std::identity>
void move_largest_to_end(RandomIt first, RandomIt mid, RandomIt last, Proj proj = {}) {
    int64_t right_size = last - mid;
    for (int64_t i = 0; i < right_size; i++) {
        std::swap(*std::ranges::max_element(first, last - i, std::less{}, proj), *(last - i - 1));
    }
}

namespace Stage {
static constexpr uint64_t median_of_medians = 0;
static constexpr uint64_t partition = 1;
static constexpr uint64_t restore_right = 2;
static constexpr uint64_t restore_left = 3;
}  // namespace Stage

template <typename RandomIt, typename Proj = std::identity>
void inplace_unstable_select(RandomIt first, RandomIt mid, RandomIt last, Proj proj = {}) {
    using T = typename std::iterator_traits<RandomIt>::value_type;
    constexpr int64_t group_size = 5;
    constexpr int64_t shrink_num = (group_size + 1) / 2;  // 3
    constexpr int64_t shrink_den = group_size * 2;        // 10
    constexpr int64_t alignment = group_size * 2;         // 10
    int64_t len = last - first;
    if (len < alignment) {
        bubble_sort(first, last, proj);
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
            RandomIt tail = first + (len % alignment);
            int64_t aligned_len = tail - first;
            move_largest_to_end(first, tail, last, proj);
            if (k >= aligned_len) {
                continue;
            }
            // median of medians of each group
            for (int64_t i = 0; i + group_size <= aligned_len; i += group_size) {
                bubble_sort(first + i, first + i + group_size, proj);
                std::swap(first[i / group_size], first[i + (group_size / 2)]);
            }
            // prepare buffer
            RandomIt buffer = first + (aligned_len / group_size);
            if (!prepare_buffer(buffer, tail, word_bits, proj)) {
                T possible_majority = *(tail - 1);
                RandomIt mid = std::partition(
                    first, tail, [&](T x) { return proj(x) != proj(possible_majority); });
                bubble_sort(first, mid, proj);
                std::ranges::rotate(std::ranges::find_if(first, mid,
                                [&](T x) { return proj(x) >= proj(possible_majority); }),
                    mid, tail);
                continue;
            }
            // store (k, tail_size)
            write_buffer(buffer, k, word_bits, proj);
            stages.push(Stage::partition);
            tail_sizes.push(last - tail);
            stages.push(Stage::median_of_medians);
            k = aligned_len / group_size / 2;
            last = first + (aligned_len / group_size);
        } else if (stage == Stage::partition) {
            T pivot = first[k];
            // restore (first, last, k)
            k = read_buffer(last, word_bits, proj);
            int64_t len = last - first;
            last += len * (group_size - 1);
            len = last - first;
            // three-way partition
            RandomIt pivot_start =
                std::partition(first, last, [&](T el) { return proj(el) < proj(pivot); });
            RandomIt pivot_end =
                std::partition(pivot_start, last, [&](T el) { return proj(el) == proj(pivot); });
            RandomIt kth = first + k;
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
