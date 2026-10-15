// Stable multi-way merge sort (read-only input)
// --------------------------------------------------------------------------
// Writes the stably sorted permutation of [first, last) to the output range
// starting at `output`; the input is only read, never mutated.
//
// The input is cut into at most `workspace` consecutive blocks of size
// ceil(size / workspace), merged by a heap holding the smallest not-yet-emitted
// element of each block. All scratch space is allocated here.
//
// Blog: https://axiomofchoice-hjt.github.io/pages/cbe60d/

#pragma once

#include <algorithm>
#include <cstdint>
#include <functional>
#include <optional>
#include <utility>
#include <vector>

#include "tcs/common/assert.hpp"

namespace tcs::readonly::multiway_mergesort {
template <typename RandomIt, typename IterProj>
std::optional<RandomIt> next_element(
    RandomIt first, RandomIt last, std::optional<RandomIt> filter, IterProj iter_proj) {
    common::assert_or_throw(first <= last);
    std::optional<RandomIt> res;
    for (RandomIt i = first; i != last; i++) {
        if ((!filter.has_value() || iter_proj(i) > iter_proj(*filter)) &&
            (!res.has_value() || iter_proj(i) < iter_proj(*res))) {
            res = i;
        }
    }
    return res;
}

template <typename RandomIt, typename OutputIt, typename Proj = std::identity>
void multiway_mergesort(
    RandomIt first, RandomIt last, OutputIt output, int64_t workspace, Proj proj = {}) {
    common::assert_or_throw(first <= last);
    common::assert_or_throw(workspace > 0);
    int64_t size = last - first;
    if (size == 0) {
        return;
    }
    auto iter_proj = [proj](RandomIt it) { return std::pair{proj(*it), it}; };
    int64_t block_size = (size + workspace - 1) / workspace;
    int64_t n_blocks = (size + block_size - 1) / block_size;

    std::vector<RandomIt> heap;
    for (int64_t i = 0; i < n_blocks; i++) {
        int64_t block_start = i * block_size;
        int64_t block_end = std::min(size, block_start + block_size);
        auto block_min = next_element(
            first + block_start, first + block_end, std::optional<RandomIt>{}, iter_proj);
        common::assert_or_throw(block_min.has_value());
        heap.push_back(*block_min);
    }

    std::ranges::make_heap(heap, std::greater{}, iter_proj);
    for (int64_t i = 0; i < size; i++) {
        common::assert_or_throw(!heap.empty());
        *output = *heap.front();
        ++output;
        std::ranges::pop_heap(heap, std::greater{}, iter_proj);
        RandomIt min_it = heap.back();
        heap.pop_back();
        int64_t block_id = (min_it - first) / block_size;
        int64_t block_start = block_id * block_size;
        int64_t block_end = std::min(size, block_start + block_size);
        auto block_next = next_element(
            first + block_start, first + block_end, std::optional<RandomIt>{min_it}, iter_proj);
        if (block_next.has_value()) {
            heap.push_back(*block_next);
            std::ranges::push_heap(heap, std::greater{}, iter_proj);
        }
    }
}
}  // namespace tcs::readonly::multiway_mergesort
