// Stable multi-way merge sort (read-only input)
// --------------------------------------------------------------------------
// Sorts the input range [first, last) and writes the (stably) sorted result to
// the random-access output range starting at `output`, using a caller-provided
// scratch buffer of iterators. The input range is only read, never mutated.
//
// Blog: ...

#pragma once

#include <algorithm>
#include <cstdint>
#include <format>
#include <functional>
#include <optional>
#include <source_location>
#include <stdexcept>
#include <string_view>
#include <tuple>
#include <vector>

namespace tcs::readonly::multiway_mergesort {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

template <typename RandomIt, typename IterOptProj>
std::optional<RandomIt> next_element(
    RandomIt first, RandomIt last, std::optional<RandomIt> filter, IterOptProj iter_opt_proj) {
    std::optional<RandomIt> res;
    for (RandomIt i = first; i < last; i++) {
        if ((!filter.has_value() || iter_opt_proj(i) > iter_opt_proj(filter)) &&
            iter_opt_proj(i) < iter_opt_proj(res)) {
            res = i;
        }
    }
    return res;
}

template <typename RandomIt, typename OutputIt, typename Proj = std::identity>
void multiway_mergesort(
    RandomIt first, RandomIt last, OutputIt output, int64_t workspace, Proj proj = {}) {
    assert_or_throw(first <= last);
    assert_or_throw(workspace > 0);
    int64_t size = last - first;
    if (size == 0) {
        return;
    }
    auto iter_opt_proj = [proj, first](std::optional<RandomIt> opt) {
        if (!opt.has_value()) {
            return std::tuple{true, proj(*first), first};
        }
        return std::tuple{false, proj(*opt.value()), opt.value()};
    };
    int64_t block_size = (size + workspace - 1) / workspace;
    int64_t n_blocks = (size + block_size - 1) / block_size;

    std::vector<std::optional<RandomIt>> heap;
    for (int64_t i = 0; i < n_blocks; i++) {
        int64_t start = i * block_size;
        int64_t end = std::min(size, start + block_size);
        assert_or_throw(start < end);
        heap.push_back(
            next_element(first + start, first + end, std::optional<RandomIt>{}, iter_opt_proj));
    }

    std::ranges::make_heap(heap, std::greater{}, iter_opt_proj);
    for (int64_t i = 0; i < size; i++) {
        assert_or_throw(heap[0].has_value());
        RandomIt min_it = heap[0].value();
        *output = *min_it;
        ++output;
        std::ranges::pop_heap(heap, std::greater{}, iter_opt_proj);
        int64_t block_id = (min_it - first) / block_size;
        int64_t start = block_id * block_size;
        int64_t end = std::min(size, start + block_size);
        heap.back() = next_element(
            first + start, first + end, std::optional<RandomIt>{min_it}, iter_opt_proj);
        std::ranges::push_heap(heap, std::greater{}, iter_opt_proj);
    }
}
}  // namespace tcs::readonly::multiway_mergesort
