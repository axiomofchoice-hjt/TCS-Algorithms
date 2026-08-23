// One-pass median (minimum-space median)
// --------------------------------------------------------------------------
// Computes the median of a forward range by reading each element exactly
// once, using only floor(n / 2) + 2 elements of buffer space, in O(n) time.
// The buffer is sized independently, so the range itself stays read-only.
//
// The per-window selection comes from the real O(1) in-place primitive in
// unstable_select.hpp when TCS_NO_TEMP_IMPL is defined; otherwise it falls
// back to std::ranges::nth_element.
//
// Blog: https://axiomofchoice-hjt.github.io/pages/c8ca67/

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
#include <utility>

#ifdef TCS_NO_TEMP_IMPL
#include "tcs/inplace/unstable_select.hpp"
#endif

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
void inplace_unstable_select_ref(RandomIt first, RandomIt mid, RandomIt last, Proj proj = {}) {
#ifdef TCS_NO_TEMP_IMPL
    return inplace::unstable_select::inplace_unstable_select(first, mid, last, proj);
#else
    std::ranges::nth_element(first, mid, last, {}, proj);
#endif
}

template <typename RandomIt, typename Proj = std::identity>
void select_range(RandomIt first, RandomIt left, RandomIt right, RandomIt last, Proj proj = {}) {
    if (left != last) {
        inplace_unstable_select_ref(first, left, last, proj);
    }
    if (right != last) {
        inplace_unstable_select_ref(left, right, last, proj);
    }
}

template <typename RandomIt, typename Proj = std::identity>
std::array<std::iter_value_t<RandomIt>, 2> median(RandomIt first, RandomIt last, Proj proj = {}) {
    int64_t size = last - first;
    assert_or_throw(size > 0, "onepass_median: size must be positive");
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
    auto next = [&]() {
        assert_or_throw(remain > 0, "onepass_median: reading past the end of the input");
        std::iter_value_t<ForwardIt> value = *first;
        first++;
        remain--;
        return value;
    };

    assert_or_throw(size > 0, "onepass_median: size must be positive");

    int64_t buffer_size = buffer_last - buffer_first;
    assert_or_throw(
        buffer_size == (size / 2) + 2, "onepass_median: buffer must be exactly size/2 + 2 cells");

    if (size <= 4) {
        assert_or_throw(size <= buffer_size, "onepass_median: buffer too small for the input");
        for (int64_t i = 0; i < size; i++) {
            buffer_first[i] = next();
        }
        return median(buffer_first, buffer_first + size, proj);
    }

    // initial load
    for (int64_t i = 0; i < (size / 2) + 1; i++) {
        buffer_first[i + 1] = next();
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
            assert_or_throw(n_keeps < right - left, "onepass_median: ladder exceeds the window");
            select_range(left, left + (n_keeps / 2), right - (n_keeps / 2), right, proj);
            right = std::rotate(left + (n_keeps / 2), right - (n_keeps / 2), right);
        }
        assert_or_throw(left == right, "onepass_median: ladder did not converge");
    }
    // elimination: read new elements into the vacated front, then drop the
    // current extremes (upper/lower "quartiles") from the candidate window
    BufferIt candidates = buffer_first + 1;
    while (true) {
        int64_t n_loads = std::min(remain, candidates - buffer_first);
        for (int64_t i = 0; i < n_loads; i++) {
            candidates--;
            *candidates = next();
        }
        if (remain == 0) {
            break;
        }
        int64_t n_drops = n_loads * 2;
        int64_t n_candidates = std::min((n_loads * 4) - 1, buffer_last - candidates);
        if (n_candidates == buffer_last - candidates) {
            assert_or_throw(n_candidates >= n_drops + (size % 2 == 0 ? 2 : 1),
                "onepass_median: candidate window is too small");
        }
        BufferIt left = candidates;
        BufferIt right = buffer_first + n_candidates;
        select_range(left, left + (n_drops / 2), right - (n_drops / 2), right, proj);
        candidates = std::rotate(left + (n_drops / 2), right - (n_drops / 2), right);
    }
    return median(candidates, buffer_last, proj);
}
}  // namespace onepass_median
}  // namespace readonly
}  // namespace tcs
