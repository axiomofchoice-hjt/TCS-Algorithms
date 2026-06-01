#pragma once

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <format>
#include <functional>
#include <ranges>
#include <source_location>
#include <stdexcept>
#include <string_view>
#include <utility>

namespace tcs {
namespace inplace_stable_select {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

// Stub: delegates to std::stable_partition (non-in-place, O(n) extra space).
// Real in-place O(1) implementation: inplace_stable_partition.hpp
template <typename RandomIt, typename Pred>
void inplace_stable_partition_stub(RandomIt first, RandomIt last, Pred pred) {
    std::stable_partition(first, last, pred);
}

// Stub: rebuilds array using a vector buffer (non-in-place, O(n) extra space).
// Real in-place O(1) implementation: inplace_stable_unpartition.hpp
template <typename RandomIt, typename Pred, typename Placement>
void inplace_stable_unpartition_stub(
    RandomIt first, RandomIt last, Pred pred, Placement placement) {
    using T = std::iter_value_t<RandomIt>;
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
std::iter_value_t<RandomIt> probable_major(RandomIt first, RandomIt last, Proj proj = {}) {
    using T = std::iter_value_t<RandomIt>;
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
    using T = std::iter_value_t<RandomIt>;
    int64_t len = last - first;
    if (len < buffer_len * 2) {
        return false;
    }
    T major = probable_major(first, first + (buffer_len * 2), proj);
    // Case 1: the majority element appears <= buffer_len times in the prefix 2*buffer_len.
    // After sorting, major elements are scattered thin enough that each i < buffer_len has
    // *(first + i) != *(first + i + buffer_len), giving us 2*buffer_len valid label pairs.
    if (std::ranges::count_if(first, first + (buffer_len * 2),
            [&](T x) { return proj(x) == proj(major); }) <= buffer_len) {
        bubble_sort(first, first + (buffer_len * 2), proj);
        return true;
    }
    // Case 2: majority is not overwhelming (count <= len - buffer_len).
    // Partition non-major to the left, then bubble-sort the buffer prefix [first, first+buffer_len)
    // so buffer elements are ordered. Insert buffer_len major elements at their sorted position
    // via rotation. This guarantees *(first + i) != *(first + i + buffer_len) because
    // buffer holds non-major and the paired region holds major.
    if (std::ranges::count_if(first, last, [&](T x) { return proj(x) == proj(major); }) <=
        len - buffer_len) {
        inplace_stable_partition_stub(first, last, [&](T x) { return proj(x) != proj(major); });
        RandomIt major_it =
            std::ranges::find_if(first, last, [&](T x) { return proj(x) == proj(major); });
        bubble_sort(first, first + buffer_len, proj);
        RandomIt major_insert_it = std::ranges::find_if(
            first, first + buffer_len, [&](T x) { return proj(x) > proj(major); });
        std::ranges::rotate(major_insert_it, major_it, major_it + buffer_len);
        return true;
    }
    return false;
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

// Returns the smallest strided element strictly greater than x. Breaks ties on key equality by
// comparing raw iterator positions, giving a total order over identical keys.
template <typename RandomIt, typename Proj = std::identity>
RandomIt strided_next_element(
    RandomIt first, RandomIt last, int64_t stride, RandomIt x, Proj proj = {}) {
    assert_or_throw(
        (last - first) % stride == 0, "strided_next_element: range must be aligned to stride");
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
RandomIt strided_topk(RandomIt first, RandomIt last, int64_t stride, int64_t k, Proj proj = {}) {
    assert_or_throw((last - first) % stride == 0);
    RandomIt median_it = strided_min_element(first, last, stride, proj);
    for (int64_t i = 0; i < k; i++) {
        median_it = strided_next_element(first, last, stride, median_it, proj);
    }
    return median_it;
}

template <typename RandomIt, typename Proj = std::identity>
std::tuple<RandomIt, RandomIt> three_way_partition(
    RandomIt first, RandomIt last, std::iter_value_t<RandomIt> pivot, Proj proj = {}) {
    using T = std::iter_value_t<RandomIt>;
    inplace_stable_partition_stub(first, last, [&](T x) { return proj(x) < proj(pivot); });
    RandomIt pivot_start =
        std::ranges::find_if(first, last, [&](T x) { return proj(x) >= proj(pivot); });
    inplace_stable_partition_stub(pivot_start, last, [&](T x) { return proj(x) == proj(pivot); });
    RandomIt pivot_end =
        std::ranges::find_if(pivot_start, last, [&](T x) { return proj(x) != proj(pivot); });
    return {pivot_start, pivot_end};
}

namespace Stage {
static constexpr uint64_t median_of_medians = 0;
static constexpr uint64_t partition = 1;
static constexpr uint64_t restore = 2;
}  // namespace Stage

struct Stack {
    std::vector<int64_t> data;
    void push(int64_t value) { data.push_back(value); }
    int64_t pop() {
        assert_or_throw(!data.empty());
        int64_t res = data.back();
        data.pop_back();
        return res;
    }
    bool empty() const { return data.empty(); }
};

template <typename RandomIt, typename Proj = std::identity>
std::iter_value_t<RandomIt> restoring_select(RandomIt first, RandomIt mid, RandomIt last,
    [[maybe_unused]] RandomIt buf, [[maybe_unused]] int64_t buffer_len, Proj proj = {}) {
    using T = std::iter_value_t<RandomIt>;
    constexpr int64_t group_size = 5;
    RandomIt original = first;
    Stack tmp;  // TODO: use buffer
    tmp.push(Stage::median_of_medians);
    tmp.push(mid - original);
    tmp.push(first - original);
    tmp.push(last - original);
    T result;
    while (!tmp.empty()) {
        RandomIt last = original + tmp.pop();
        RandomIt first = original + tmp.pop();
        int64_t k = tmp.pop();
        uint64_t stage = tmp.pop();
        if (stage == Stage::median_of_medians) {
            int64_t len = last - first;
            int64_t aligned_len = len / group_size * group_size;
            if (len < group_size) {
                result = *strided_topk(first, last, 1, k, proj);
                continue;
            }
            // median of medians of each group
            for (int64_t i = 0; i + group_size <= aligned_len; i += group_size) {
                RandomIt median_it =
                    strided_topk(first + i, first + i + group_size, 1, group_size / 2, proj);
                tmp.push(median_it - (first + i));
                std::swap(first[i / group_size], *median_it);
            }
            // recursive
            tmp.push(Stage::partition);
            tmp.push(k);
            tmp.push(first - original);
            tmp.push(last - original);
            tmp.push(Stage::median_of_medians);
            tmp.push(aligned_len / group_size / 2);
            tmp.push(first - original);
            tmp.push(first + (aligned_len / group_size) - original);
        } else if (stage == Stage::partition) {
            T pivot = result;
            int64_t len = last - first;
            int64_t aligned_len = len / group_size * group_size;
            for (int64_t i = aligned_len - group_size; i >= 0; i -= group_size) {
                std::swap(first[i / group_size], first[i + tmp.pop()]);
            }
            for (RandomIt i = first; i < last; i++) {
                tmp.push(proj(*i) < proj(pivot));
            }
            inplace_stable_partition_stub(first, last, [&](T x) { return proj(x) < proj(pivot); });
            for (RandomIt i = first; i < last; i++) {
                tmp.push(proj(*i) <= proj(pivot));
            }
            inplace_stable_partition_stub(first, last, [&](T x) { return proj(x) <= proj(pivot); });
            RandomIt pivot_start =
                std::ranges::find_if(first, last, [&](T x) { return proj(x) >= proj(pivot); });
            RandomIt pivot_end =
                std::ranges::find_if(pivot_start, last, [&](T x) { return proj(x) > proj(pivot); });
            RandomIt kth = first + k;
            // store (k, first, last)
            tmp.push(Stage::restore);
            tmp.push(k);
            tmp.push(first - original);
            tmp.push(last - original);
            if (kth < pivot_start) {
                tmp.push(Stage::median_of_medians);
                tmp.push(k);
                tmp.push(first - original);
                tmp.push(pivot_start - original);
            } else if (kth >= pivot_end) {
                first = pivot_end;
                k = kth - pivot_end;
                tmp.push(Stage::median_of_medians);
                tmp.push(kth - pivot_end);
                tmp.push(pivot_end - original);
                tmp.push(last - original);
            } else {
                result = *kth;
            }
        } else if (stage == Stage::restore) {
            int64_t len = last - first;
            auto placement = tmp.data.end() - len;
            T pivot =
                first[std::count_if(placement, placement + len, [](bool x) { return x; }) - 1];
            inplace_stable_unpartition_stub(
                first, last, [&](T x) { return proj(x) <= proj(pivot); },
                [&](RandomIt i) { return placement[i - first]; });
            for (int64_t _ : std::views::iota(0, len)) {
                tmp.pop();
            }
            placement = tmp.data.end() - len;
            inplace_stable_unpartition_stub(
                first, last, [&](T x) { return proj(x) < proj(pivot); },
                [&](RandomIt i) { return placement[i - first]; });
            for (int64_t _ : std::views::iota(0, len)) {
                tmp.pop();
            }
        }
    }
    return result;
}

template <typename RandomIt, typename Proj = std::identity>
void inplace_stable_select(RandomIt first, RandomIt mid, RandomIt last, Proj proj = {}) {
    using T = std::iter_value_t<RandomIt>;
    while (true) {
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
        assert_or_throw(std::ranges::is_sorted(first, first + (buffer_len * 2), {}, proj));
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
            T median =
                restoring_select(start, start + (block_size / 2), end, first, buffer_len, proj);
            RandomIt median_it =
                std::ranges::find_if(start, end, [&](T x) { return proj(x) == proj(median); });
            std::ranges::rotate(start, median_it, median_it + 1);
        }

        RandomIt last_aligned = main + (n_blocks * block_size);
        T median = *strided_topk(main, last_aligned, block_size, (n_blocks - 1) / 2, proj);
        auto [median_start, median_end] = three_way_partition(first, last, median, proj);
        if (mid < median_start) {
            last = median_start;
        } else if (mid >= median_end) {
            first = median_end;
        } else {
            return;
        }
    }
}
}  // namespace inplace_stable_select
}  // namespace tcs
