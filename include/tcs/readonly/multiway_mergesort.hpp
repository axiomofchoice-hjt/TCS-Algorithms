// Stable multi-way merge sort (read-only input)
// --------------------------------------------------------------------------
// Sorts the input range [first, last) and writes the (stably) sorted result to
// the random-access output range starting at `output`, using a caller-provided
// scratch buffer of iterators. The input range is only read, never mutated.
//
// Blog: https://axiomofchoice-hjt.github.io/pages/1b8e07/

#pragma once

#include <algorithm>
#include <cstdint>
#include <format>
#include <functional>
#include <iterator>
#include <source_location>
#include <stdexcept>
#include <string_view>
#include <utility>

namespace tcs {
namespace readonly {
namespace multiway_mergesort {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

// Smallest element in [first, last) strictly greater than x. Ties are broken by
// iterator position, so following this repeatedly yields the elements of the
// block in ascending (key, position) order.
template <typename RandomIt, typename Proj = std::identity>
RandomIt next_element(RandomIt first, RandomIt last, RandomIt x, Proj proj = {}) {
    RandomIt next_it = last;
    for (RandomIt i = first; i < last; i++) {
        if (std::pair{proj(*x), x} < std::pair{proj(*i), i} &&
            (next_it == last || std::pair{proj(*i), i} < std::pair{proj(*next_it), next_it})) {
            next_it = i;
        }
    }
    return next_it;
}

template <typename InputIt, typename RandomIt, typename OutputIt, typename Proj = std::identity>
void multiway_mergesort(InputIt first, InputIt last, RandomIt buffer_first, RandomIt buffer_last,
    OutputIt output, Proj proj = {}) {
    assert_or_throw(first <= last);
    if (first == last) {
        return;
    }
    assert_or_throw(buffer_first < buffer_last);
    using Pointer = std::iter_value_t<RandomIt>;
    auto greater = [proj](Pointer a, Pointer b) {
        return std::pair{proj(*a), a} > std::pair{proj(*b), b};
    };
    int64_t size = last - first;
    int64_t buffer_size = buffer_last - buffer_first;
    int64_t block_size = (size + buffer_size - 1) / buffer_size;
    buffer_size = (size + block_size - 1) / block_size;
    for (int64_t i = 0; i < buffer_size; i++) {
        int64_t start = i * block_size;
        int64_t end = std::min(size, start + block_size);
        assert_or_throw(start < end);
        buffer_first[i] = std::ranges::min_element(first + start, first + end, {}, proj);
    }
    std::ranges::make_heap(buffer_first, buffer_first + buffer_size, greater);
    for (int64_t i = 0; i < size; i++) {
        auto x = buffer_first[0];
        output[i] = *x;
        std::ranges::pop_heap(buffer_first, buffer_first + buffer_size, greater);
        buffer_size--;
        int64_t block_id = (x - first) / block_size;
        int64_t start = block_id * block_size;
        int64_t end = std::min(size, start + block_size);
        auto next = next_element(first + start, first + end, x, proj);
        if (next != first + end) {
            buffer_size++;
            buffer_first[buffer_size - 1] = next;
            std::ranges::push_heap(buffer_first, buffer_first + buffer_size, greater);
        }
    }
}
}  // namespace multiway_mergesort
}  // namespace readonly
}  // namespace tcs
