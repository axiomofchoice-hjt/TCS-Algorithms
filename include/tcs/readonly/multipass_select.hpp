#pragma once

#include <algorithm>
#include <bit>
#include <format>
#include <iterator>
#include <optional>
#include <source_location>
#include <stdexcept>
#include <string_view>

#ifdef TCS_NO_TEMP_IMPL
#include "tcs/inplace/unstable_select.hpp"
#endif

namespace tcs {
namespace readonly {
namespace multipass_select {
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

inline int64_t calc_height(int64_t size, int64_t block_size) {
    return std::bit_width(static_cast<uint64_t>((size + block_size - 1) / block_size));
}

inline std::optional<int64_t> calc_block_size(int64_t size, int64_t buffer_size) {
    int64_t block_size = 2;
    while (block_size <= calc_height(size, block_size) * 2) {
        block_size += 2;
    }
    // The working region cannot hold the sampler for this size; this is not an
    // error here — return std::nullopt and let the caller decide how to react.
    if (calc_height(size, block_size) * block_size > buffer_size) {
        return std::nullopt;
    }
    while (calc_height(size, block_size + 2) * (block_size + 2) <= buffer_size) {
        block_size += 2;
    }
    return block_size;
}

template <typename RandomIt, typename Proj = std::identity>
inline RandomIt thin_and_merge(
    RandomIt first, RandomIt valid_it, int64_t block_size, Proj proj = {}) {
    if (valid_it <= first) {
        return valid_it;
    }
    for (int64_t i = 1; i < valid_it - first; i += 2) {
        first[i / 2] = first[i];
    }
    valid_it = first + ((valid_it - first) / 2);
    if (valid_it > first + (block_size / 2)) {
        std::ranges::merge(first, first + (block_size / 2), first + (block_size / 2), valid_it,
            valid_it, {}, proj, proj);
        std::ranges::copy(valid_it, valid_it + (valid_it - first), first);
    }
    return valid_it;
}

template <typename RandomIt, typename Proj = std::identity>
struct Sampler {
    RandomIt first;
    RandomIt last;
    int64_t valid;
    int64_t size;
    int64_t block_size;
    int64_t block_id;
    Proj proj;

    static Sampler create(RandomIt first, RandomIt last, int64_t block_size, Proj proj) {
        return {first, last, 0, 0, block_size, 0, proj};
    }

    void append(std::optional<std::iter_value_t<RandomIt>> value) {
        if (value) {
            assert_or_throw(valid < last - first);
            assert_or_throw(valid == size);
            first[valid] = *value;
            valid++;
        }
        assert_or_throw(size < last - first + block_size);
        size++;

        if (size % block_size == 0) {
            if (valid > size - block_size) {
                std::ranges::sort(first + (size - block_size), first + valid, {}, proj);
            }
            block_id++;
            int64_t step = std::countr_zero(static_cast<uint64_t>(block_id));
            for (int64_t i = 0; i < step; i++) {
                assert_or_throw(size >= block_size * 2);
                valid = thin_and_merge(
                            first + (size - (block_size * 2)), first + valid, block_size, proj) -
                        first;
                size -= block_size;
            }
        }
    }
};

template <typename ForwardIt, typename RandomIt, typename Proj = std::identity>
void onepass(ForwardIt first, int64_t size, int64_t k, RandomIt buffer_first, RandomIt buffer_last,
    bool has_lower_bound, bool has_upper_bound, Proj proj = {}) {
    RandomIt lower_bound = buffer_last;
    RandomIt upper_bound = buffer_last + 1;
    ForwardIt input_it = first;
    // `lo`: elements at-or-below the lower filter (originally lt + n_lower_bounds).
    // `hi`: elements at-or-above the upper filter (originally gt + n_upper_bounds).
    // Elements strictly between the filters go to the buffer.
    int64_t lo = 0;
    int64_t hi = 0;
    RandomIt buffer_it = buffer_first;
    for (int64_t i = 0; i < size; i++) {
        auto input = *input_it;
        if (has_lower_bound && proj(input) <= proj(*lower_bound)) {
            lo++;
        } else if (has_upper_bound && proj(input) >= proj(*upper_bound)) {
            hi++;
        } else {
            assert_or_throw(buffer_it < buffer_last);
            *buffer_it = *input_it;
            buffer_it++;
        }
        input_it++;
    }
    assert_or_throw(lo - 1 <= k && k <= size - hi);
    if (k < lo) {
        // The k-th element coincides with the lower filter: the answer is
        // `lower_bound`.  Setting *upper_bound = *lower_bound publishes it, and
        // we must stop here — computing the buffer index below would be negative.
        *upper_bound = *lower_bound;
        return;
    }
    if (k >= size - hi) {
        // The k-th element coincides with the upper filter; likewise publish and
        // stop rather than reading before the buffer.
        *lower_bound = *upper_bound;
        return;
    }
    inplace_unstable_select_ref(buffer_first, buffer_first + k - lo, buffer_it, proj);
    *lower_bound = *upper_bound = buffer_first[k - lo];
}

template <typename ForwardIt, typename RandomIt, typename Proj = std::identity>
std::tuple<bool, bool, int64_t> narrow(ForwardIt first, int64_t size, int64_t k,
    RandomIt buffer_first, RandomIt buffer_last, bool has_lower_bound, bool has_upper_bound,
    int64_t population, Proj proj = {}) {
    if (population <= buffer_last - buffer_first) {
        onepass(first, size, k, buffer_first, buffer_last, has_lower_bound, has_upper_bound, proj);
        return {true, true, 0};
    }
    auto block_size_opt = calc_block_size(population, buffer_last - buffer_first);
    assert_or_throw(
        block_size_opt.has_value(), "working buffer too small for the sampler at this population");
    int64_t block_size = *block_size_opt;
    int64_t height = calc_height(population, block_size);
    RandomIt lower_bound = buffer_last;
    RandomIt upper_bound = buffer_last + 1;
    assert_or_throw(block_size > 0 && block_size % 2 == 0 && block_size > height);
    assert_or_throw((population + block_size - 1) / block_size <= (1 << height));
    if (block_size == 1) {
        assert_or_throw(false, "no impl");
    }
    ForwardIt input_it = first;
    // `lo`: elements at-or-below the lower filter (originally lt + n_lower_bounds).
    // `hi`: elements at-or-above the upper filter (originally gt + n_upper_bounds).
    // Elements strictly between the filters are fed to the sampler.
    int64_t lo = 0;
    int64_t hi = 0;
    auto sampler = Sampler<RandomIt, Proj>::create(buffer_first, buffer_last, block_size, proj);
    for (int64_t i = 0; i < size; i++) {
        auto input = *input_it;
        if (has_lower_bound && proj(input) <= proj(*lower_bound)) {
            lo++;
        } else if (has_upper_bound && proj(input) >= proj(*upper_bound)) {
            hi++;
        } else {
            sampler.append(*input_it);
        }
        input_it++;
    }
    assert_or_throw(sampler.block_id <= (1 << height));
    while (sampler.block_id < (1 << height)) {
        sampler.append(std::nullopt);
    }

    assert_or_throw(population >= size - lo - hi);
    assert_or_throw(lo - 1 <= k && k <= size - hi);
    if (k < lo) {
        // The k-th element coincides with the lower filter; no sampling needed.
        *upper_bound = *lower_bound;
        return {true, true, 0};
    }
    if (k >= size - hi) {
        // The k-th element coincides with the upper filter.
        *lower_bound = *upper_bound;
        return {true, true, 0};
    }

    // The paper works in descending order for the k-th *highest* element:
    // filters are the u-th and v-th sample elements from the top, with
    //   u = ceil(k/2^r) - r  (greatest int with k-1 >= M_{ru})
    //   v = ceil(k/2^r)      (least  int with k-1 <= L_{rv})
    // Here the storage is ascending and we select the k-th *smallest*
    // (0-indexed), so the mirror maps "rank from top" to "rank from bottom"
    // (R = k_eff + 1) and "index from top" to "index from bottom".
    int64_t k_eff = k - lo;
    int64_t pw = (1 << height);
    int64_t upper_sample = ((k_eff + 1 + pw - 1) / pw) - 1;  // ceil((k_eff+1)/pw) - 1
    int64_t lower_sample = upper_sample - height;            // and minus r further
    if (lower_sample >= 0) {
        assert_or_throw(lower_sample < sampler.valid);
        *lower_bound = buffer_first[lower_sample];
        has_lower_bound = true;
    }
    if (upper_sample < sampler.valid) {
        assert_or_throw(upper_sample >= 0);
        *upper_bound = buffer_first[upper_sample];
        has_upper_bound = true;
    }
    // (2r-1)*2^r bounds the between-filter cohort; the paper's model assumes
    // distinct elements, so this clamp is valid there.
    population = std::min(size - lo - hi, ((2 * height) - 1) * (1 << height));
    return {has_lower_bound, has_upper_bound, population};
}

template <typename ForwardIt, typename RandomIt, typename Proj = std::identity>
std::iter_value_t<ForwardIt> multipass_select(ForwardIt first, int64_t size, int64_t k,
    RandomIt buffer_first, RandomIt buffer_last, Proj proj = {}) {
    bool has_lower_bound = false;
    bool has_upper_bound = false;
    int64_t population = size;
    while (population > 0) {
        std::tie(has_lower_bound, has_upper_bound, population) = narrow(first, size, k,
            buffer_first, buffer_last - 2, has_lower_bound, has_upper_bound, population, proj);
    }
    return *(buffer_last - 2);
}
}  // namespace multipass_select
}  // namespace readonly
}  // namespace tcs
