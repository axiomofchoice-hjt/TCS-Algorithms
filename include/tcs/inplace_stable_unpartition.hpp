#pragma once

#include <algorithm>
#include <array>
#include <bit>
#include <climits>
#include <cmath>
#include <format>
#include <functional>
#include <source_location>
#include <stdexcept>
#include <string_view>

namespace tcs {
namespace inplace_stable_unpartition {
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

template <typename RandomIt, typename Placement>
int64_t count_if_placement_equals(RandomIt first, RandomIt last, int key, Placement placement) {
    int64_t cnt = 0;
    for (RandomIt it = first; it < last; it++) {
        if (placement(it) == key) {
            cnt++;
        }
    }
    return cnt;
}

template <typename RandomIt, typename Proj = std::identity, typename Placement>
void check_partition_consistency(RandomIt first, RandomIt last, Proj proj, Placement placement,
    const std::source_location& loc = std::source_location::current()) {
    using T = std::iter_value_t<RandomIt>;
    static_assert(std::is_invocable_v<Proj, T>);
    static_assert(std::is_invocable_v<Placement, RandomIt>);
    assert_or_throw(std::ranges::count_if(first, last, proj) ==
                        count_if_placement_equals(first, last, 1, placement),
        "empty message", loc);
}

template <typename RandomIt, typename Proj = std::identity, typename Placement>
void dehomogenize_blocks(
    RandomIt first, RandomIt last, int64_t block_size, Proj proj, Placement placement) {
    using T = std::iter_value_t<RandomIt>;
    assert_or_throw((last - first) % block_size == 0);
    int64_t n_blocks = (last - first) / block_size;
    for (int64_t i = 0; i + 2 <= n_blocks; i++) {
        RandomIt left = first + (i * block_size);
        RandomIt mid = left + block_size;
        RandomIt right = mid + block_size;
        RandomIt split01 = std::ranges::find_if(left, mid, proj);
        assert_or_throw(std::ranges::is_sorted(left, mid, {}, proj));
        assert_or_throw(
            std::ranges::all_of(mid, right, [proj, mid](T x) { return proj(x) == proj(*mid); }));
        int64_t cnt0_left = count_if_placement_equals(left, mid, 0, placement);
        if (split01 < left + cnt0_left) {
            assert_or_throw(proj(*mid) == 0);
            std::ranges::rotate(split01, mid, mid + (left + cnt0_left - split01));
            std::ranges::rotate(mid, mid + (left + cnt0_left - split01), right);
        } else if (split01 > left + cnt0_left) {
            assert_or_throw(proj(*mid) == 1);
            std::ranges::rotate(left + cnt0_left, split01, mid + (split01 - left - cnt0_left));
        }
    }
}

struct StorageAttributes {
    int64_t n_bits;
    int64_t element_bits;
};

struct WordStorage {
    int64_t n_bits;
    int64_t element_bits;
    uint64_t word;

    static WordStorage create(StorageAttributes attr) {
        assert_or_throw(attr.n_bits <= static_cast<int64_t>(sizeof(uint64_t) * CHAR_BIT));
        return WordStorage{.n_bits = attr.n_bits, .element_bits = attr.element_bits, .word = 0};
    }

    uint64_t get(int64_t index) const {
        assert_or_throw(index < n_bits / element_bits);
        return (word >> (index * element_bits)) & ((uint64_t{1} << element_bits) - 1);
    }

    void set(int64_t index, uint64_t value) {
        assert_or_throw(index < n_bits / element_bits);
        assert_or_throw(value < (uint64_t{1} << element_bits));
        auto slot_mask = ((uint64_t{1} << element_bits) - 1) << (index * element_bits);
        word = (word & ~slot_mask) | (value << (index * element_bits));
    }

    void reset() { word = 0; }
};

template <typename RandomIt, typename Proj = std::identity>
struct BufferStorage {
    RandomIt buf0;
    RandomIt buf1;
    int64_t n_bits;
    int64_t element_bits;
    Proj proj;

    using T = std::iter_value_t<RandomIt>;
    static_assert(std::is_invocable_v<Proj, T>);

    static BufferStorage create(StorageAttributes attr, RandomIt buf0, RandomIt buf1, Proj proj) {
        return BufferStorage{.buf0 = buf0,
            .buf1 = buf1,
            .n_bits = attr.n_bits,
            .element_bits = attr.element_bits,
            .proj = proj};
    }

    uint64_t get(int64_t index) const {
        assert_or_throw(index < n_bits / element_bits);
        uint64_t res = 0;
        for (int64_t i = 0; i < element_bits; i++) {
            res |= uint64_t(proj(buf0[(index * element_bits) + i])) << i;
        }
        return res;
    }

    void set(int64_t index, uint64_t value) {
        assert_or_throw(index < n_bits / element_bits);
        assert_or_throw(value < (uint64_t{1} << element_bits));
        for (int64_t i = 0; i < element_bits; i++) {
            if (uint64_t(proj(buf0[(index * element_bits) + i])) != ((value >> i) & 1)) {
                std::swap(buf0[(index * element_bits) + i], buf1[(index * element_bits) + i]);
            }
        }
    }

    void reset() {
        for (int64_t i = 0; i < n_bits / element_bits; i++) {
            set(i, 0);
        }
    }
};

template <typename RandomIt, typename Proj = std::identity, typename Placement>
void inplace_01_split(
    RandomIt first, RandomIt split, RandomIt last, Proj proj, Placement placement) {
    check_partition_consistency(first, last, proj, placement);
    RandomIt mid = std::ranges::find_if(first, last, proj);
    RandomIt l = first + count_if_placement_equals(first, split, 0, placement);
    RandomIt r = split + count_if_placement_equals(split, last, 0, placement);
    assert_or_throw(l <= mid && mid <= r);
    std::ranges::rotate(l, mid, r);
}

template <typename RandomIt, typename Proj = std::identity, typename Placement>
std::tuple<RandomIt, RandomIt, RandomIt, RandomIt> extract_buffer(
    RandomIt first, RandomIt last, Proj proj, Placement placement, int64_t buffer_len) {
    check_partition_consistency(first, last, proj, placement);
    std::array<int64_t, 2> cnt = {};
    for (RandomIt it = first; it < last; it++) {
        cnt[placement(it)]++;
        if (cnt[0] >= buffer_len && cnt[1] >= buffer_len) {
            break;
        }
    }
    if (cnt[0] >= buffer_len && cnt[1] >= buffer_len) {
        inplace_01_split(first, first + cnt[0] + cnt[1], last, proj, placement);
        return {first, first + cnt[0], first + cnt[0] + cnt[1], last};
    }
    return {first, first, first, last};
}

template <typename RandomIt, typename Proj = std::identity, typename Placement>
void unpartition_with_rotation(RandomIt first, RandomIt last, Proj proj, Placement placement) {
    RandomIt mid = std::ranges::find_if(first, last, proj);
    if (mid - first < last - mid) {
        RandomIt zero_start = first;
        int64_t n_zeros = mid - first;
        for (RandomIt it = first; it < last; it++) {
            if (placement(it) == 0) {
                std::ranges::rotate(zero_start, zero_start + n_zeros, it + n_zeros);
                zero_start = it + 1;
                n_zeros--;
            }
        }
    } else {
        RandomIt one_end = last;
        int64_t n_ones = last - mid;
        for (RandomIt it = last; it > first; it--) {
            if (placement(it - 1) == 1) {
                std::ranges::rotate(it - n_ones, one_end - n_ones, one_end);
                one_end = it - 1;
                n_ones--;
            }
        }
    }
}

template <typename RandomIt, typename Storage, typename Proj = std::identity, typename Placement>
void merge_blocks_impl(RandomIt first, RandomIt last, int64_t block_size, Storage& storage,
    Proj proj, Placement placement) {
    check_partition_consistency(first, last, proj, placement);
    int64_t n_blocks = (last - first) / block_size;
    if (n_blocks <= 2) {
        return;
    }
    RandomIt homogenized = first + block_size;
    RandomIt mid = std::ranges::find_if(homogenized, last, proj);
    auto block0_cnt1 = std::ranges::count_if(first, homogenized, proj);
    std::array<int64_t, 2> counters = {block_size - block0_cnt1, block0_cnt1};
    std::array<int64_t, 2> pointers = {1, (mid - first) / block_size};
    int64_t global_pos = 1;
    storage.set(0, 0);
    auto update = [&](RandomIt left, RandomIt right) {
        int64_t cnt0_placement = count_if_placement_equals(left, right, 0, placement);
        if (counters[0] <= cnt0_placement && pointers[0] < (mid - first) / block_size) {
            storage.set(pointers[0], global_pos);
            pointers[0]++;
            global_pos++;
            counters[0] += block_size;
        } else {
            assert_or_throw(pointers[1] < n_blocks);
            storage.set(pointers[1], global_pos);
            pointers[1]++;
            global_pos++;
            counters[1] += block_size;
        }
        counters[0] -= cnt0_placement;
        counters[1] -= block_size - cnt0_placement;
    };
    for (int64_t i = 0; i < n_blocks - 1; i++) {
        update(first + (i * block_size), first + ((i + 1) * block_size));
    }
    for (int64_t i = 0; i < n_blocks; i++) {
        for (int64_t j = storage.get(i); j != i;) {
            std::swap_ranges(
                first + (i * block_size), first + ((i + 1) * block_size), first + (j * block_size));
            int next = storage.get(j);
            storage.set(j, j);
            j = next;
        }
        storage.set(i, i);
    }
    storage.reset();
}

template <typename RandomIt, typename Proj = std::identity, typename Placement>
void merge_blocks_using_word(RandomIt first, RandomIt last, int64_t block_size, Proj proj,
    Placement placement, int64_t word_bits) {
    assert_or_throw((last - first) % block_size == 0);
    int64_t n_blocks = (last - first) / block_size;
    if (n_blocks <= 2) {
        return;
    }
    int64_t element_bits = ceil_log2(n_blocks);
    assert_or_throw(n_blocks * element_bits <= word_bits,
        std::format("{} {} {}", n_blocks, element_bits, word_bits));
    assert_or_throw(word_bits <= static_cast<int64_t>(sizeof(uint64_t) * CHAR_BIT));
    auto storage = WordStorage::create({.n_bits = word_bits, .element_bits = element_bits});
    merge_blocks_impl(first, last, block_size, storage, proj, placement);
}

template <typename RandomIt, typename Proj = std::identity, typename Placement>
void merge_blocks_using_buffer(RandomIt first, RandomIt last, int64_t block_size, RandomIt buf0,
    RandomIt buf1, int64_t buffer_len, Proj proj, Placement placement) {
    assert_or_throw((last - first) % block_size == 0);
    int64_t n_blocks = (last - first) / block_size;
    if (n_blocks <= 2) {
        return;
    }
    int64_t element_bits = ceil_log2(n_blocks);
    assert_or_throw(n_blocks * element_bits <= buffer_len,
        std::format("{} {} {}", n_blocks, element_bits, buffer_len));
    auto storage = BufferStorage<RandomIt, Proj>::create(
        {.n_bits = buffer_len, .element_bits = element_bits}, buf0, buf1, proj);
    merge_blocks_impl(first, last, block_size, storage, proj, placement);
}

template <typename RandomIt, typename Proj = std::identity, typename Placement>
void inplace_stable_01_unpartition(RandomIt first, RandomIt last, Proj proj, Placement placement) {
    check_partition_consistency(first, last, proj, placement);
    if (last - first <= 1) {
        return;
    }
    int64_t len = last - first;
    int64_t max_word_bits = ceil_log2(len);
    int64_t buffer_len = std::floor(std::sqrt(len));
    int64_t max_blocks_for_word = 1;
    while ((max_blocks_for_word + 1) * ceil_log2(max_blocks_for_word + 1) <= max_word_bits) {
        max_blocks_for_word++;
    }
    int64_t max_blocks_for_buffer = 1;
    while ((max_blocks_for_buffer + 1) * ceil_log2(max_blocks_for_buffer + 1) <= buffer_len) {
        max_blocks_for_buffer++;
    }
    // buffer area
    RandomIt buf0;
    RandomIt buf1;
    std::tie(buf0, buf1, first, last) = extract_buffer(first, last, proj, placement, buffer_len);
    if (buf0 == first) {  // failed branch
        unpartition_with_rotation(first, last, proj, placement);
        return;
    }
    len = last - first;
    int64_t merge_size = max_blocks_for_word * max_blocks_for_word * max_blocks_for_buffer *
                         max_blocks_for_buffer * max_blocks_for_buffer;
    assert_or_throw(merge_size >= len);
    // inter-block unpartition, using buffer as counter and marker, merge_size divided by (sqrtn /
    // logn)
    for (int64_t step = 0; step < 3; step++) {
        int64_t block_size = merge_size / max_blocks_for_buffer;
        for (int64_t start = 0; start < len; start += merge_size) {
            int64_t end = std::min(start + merge_size, len);
            int64_t end_l2_aligned = end / block_size * block_size;
            inplace_01_split(first + start, first + end_l2_aligned, first + end, proj, placement);
            auto mid = std::ranges::find_if(first + start, first + end_l2_aligned, proj) - first;
            if (mid % block_size != 0) {
                std::ranges::rotate(first + start + (mid % block_size), first + mid,
                    first + ((mid + block_size - 1) / block_size * block_size));
            }
            merge_blocks_using_buffer(first + start, first + end_l2_aligned, block_size, buf0, buf1,
                buffer_len, proj, placement);
            dehomogenize_blocks(first + start, first + end_l2_aligned, block_size, proj, placement);
        }
        merge_size = block_size;
    }
    // inter-block unpartition, using word as counter and marker, merge_size divided by (logn /
    // loglogn)
    for (int64_t step = 0; step < 2; step++) {
        int64_t block_size = merge_size / max_blocks_for_word;
        for (int64_t start = 0; start < len; start += merge_size) {
            int64_t end = std::min(start + merge_size, len);
            int64_t end_l2_aligned = end / block_size * block_size;
            inplace_01_split(first + start, first + end_l2_aligned, first + end, proj, placement);
            auto mid = std::ranges::find_if(first + start, first + end_l2_aligned, proj) - first;
            if (mid % block_size != 0) {
                std::ranges::rotate(first + start + (mid % block_size), first + mid,
                    first + ((mid + block_size - 1) / block_size * block_size));
            }
            merge_blocks_using_word(
                first + start, first + end_l2_aligned, block_size, proj, placement, max_word_bits);
            dehomogenize_blocks(first + start, first + end_l2_aligned, block_size, proj, placement);
        }
        merge_size = block_size;
    }
    // unpartition buffer
    unpartition_with_rotation(buf0, first, proj, placement);
}

template <typename RandomIt, typename Pred, typename Placement>
void inplace_stable_unpartition(RandomIt first, RandomIt last, Pred pred, Placement placement) {
    using T = std::iter_value_t<RandomIt>;
    static_assert(std::is_invocable_r_v<bool, Pred, T>);
    static_assert(std::is_invocable_r_v<bool, Placement, RandomIt>);
    inplace_stable_01_unpartition(
        first, last, [pred](T x) { return pred(x) ? 0 : 1; },
        [placement](RandomIt x) { return placement(x) ? 0 : 1; });
}
}  // namespace inplace_stable_unpartition
}  // namespace tcs
