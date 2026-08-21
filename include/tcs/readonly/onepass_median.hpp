#pragma once

#include <algorithm>
#include <array>
#include <cstdint>
#include <format>
#include <functional>
#include <iterator>
#include <source_location>
#include <stdexcept>
#include <string_view>

namespace tcs {
namespace readonly {
namespace onepass_median {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

template <typename RandomIt, typename Proj = std::identity>
void select_stub(RandomIt first, RandomIt mid, RandomIt last, Proj proj = {}) {
    std::ranges::nth_element(first, mid, last, {}, proj);
}

template <typename RandomIt, typename Proj = std::identity>
void select_range(RandomIt first, RandomIt left, RandomIt right, RandomIt last, Proj proj = {}) {
    select_stub(first, left, last, proj);
    select_stub(left, right, last, proj);
}

template <typename RandomIt, typename Proj = std::identity>
std::array<std::iter_value_t<RandomIt>, 2> median(RandomIt first, RandomIt last, Proj proj = {}) {
    int64_t size = last - first;
    if (size > 2) {
        select_range(first, first + ((size - 1) / 2), first + (size / 2) + 1, last, proj);
    }
    std::array<std::iter_value_t<RandomIt>, 2> result = {first[(size - 1) / 2], first[size / 2]};
    if (proj(result[0]) > proj(result[1])) {
        std::swap(result[0], result[1]);
    }
    return result;
}

template <typename ForwardIt, typename BufferIt, typename Proj = std::identity>
std::array<std::iter_value_t<ForwardIt>, 2> onepass_median(
    ForwardIt first, int64_t size, BufferIt buffer_first, BufferIt buffer_last, Proj proj = {}) {
    int64_t remain = size;
    assert_or_throw(size > 0);

    int64_t buffer_size = buffer_last - buffer_first;
    assert_or_throw(buffer_size == (size / 2) + 2);

    if (size <= 4) {
        assert_or_throw(size <= buffer_size);
        for (int64_t i = 0; i < size; i++) {
            assert_or_throw(remain > 0);
            buffer_first[i] = *first;
            first++;
            remain--;
        }
        return median(buffer_first, buffer_first + size, proj);
    }

    // initial load
    for (int64_t i = 0; i < (size / 2) + 1; i++) {
        assert_or_throw(remain > 0);
        buffer_first[i + 1] = *first;
        first++;
        remain--;
    }
    // tournament ladder: repeatedly split the loaded window so the extreme
    // elements (provably non-medians) collect at the front/back
    int64_t max_ladder_size = 1;
    while ((4 * max_ladder_size) - 2 < (size / 2) + 1) {
        max_ladder_size *= 2;
    }
    {
        BufferIt left = buffer_first + 1;
        BufferIt right = buffer_last;
        for (int64_t ladder_size = max_ladder_size; ladder_size > 0; ladder_size /= 2) {
            int64_t n_keeps = (ladder_size - 1) * 2;
            assert_or_throw(n_keeps < right - left);
            select_range(left, left + (n_keeps / 2), right - (n_keeps / 2), right, proj);
            right = std::rotate(left + (n_keeps / 2), right - (n_keeps / 2), right);
        }
        assert_or_throw(left == right);
    }
    // elimination: read new elements into the vacated front, then drop the
    // current extremes (upper/lower "quartiles") from the candidate window
    BufferIt candidates = buffer_first + 1;
    while (true) {
        int64_t n_loads = std::min(remain, candidates - buffer_first);
        for (int64_t i = 0; i < n_loads; i++) {
            assert_or_throw(remain > 0);
            candidates--;
            *candidates = *first;
            first++;
            remain--;
        }
        if (remain == 0) {
            break;
        }
        int64_t n_drops = n_loads * 2;
        assert_or_throw(buffer_size >= n_drops + (size % 2 == 0 ? 2 : 1));
        BufferIt left = candidates;
        BufferIt right = buffer_last;
        select_range(left, left + (n_drops / 2), right - (n_drops / 2), right, proj);
        candidates = std::rotate(left + (n_drops / 2), right - (n_drops / 2), right);
    }
    // final selection
    return median(candidates, buffer_last, proj);
}
}  // namespace onepass_median
}  // namespace readonly
}  // namespace tcs
