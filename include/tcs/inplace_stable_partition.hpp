#include <algorithm>
#include <bit>
#include <climits>
#include <cmath>
#include <format>
#include <source_location>
#include <stdexcept>
#include <string_view>

namespace tcs {
namespace inplace_stable_partition {
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

template <typename T, typename Pred>
std::tuple<T*, T*, T*> stable_collect_first_n(T* first, T* last, int64_t n, Pred pred) {
    static_assert(std::is_invocable_r_v<bool, Pred, T>);
    T* collect = first;
    int64_t count = 0;
    for (T* iter = first; iter < last; iter++) {
        if (count < n && pred(*iter)) {
            std::rotate(collect, collect + count, iter);
            collect = iter - count;
            count++;
        }
    }
    std::rotate(first, collect, collect + count);
    return {first, first + count, last};
}

template <typename T, typename Proj>
void homogenize_blocks(T* first, T* last, int64_t block_size, Proj proj) {
    static_assert(std::is_invocable_v<Proj, T>);
    assert_or_throw((last - first) % block_size == 0);
    int64_t n_blocks = (last - first) / block_size;
    for (int64_t i = 0; i + 2 <= n_blocks; i++) {
        T* left = first + (i * block_size);
        T* mid = left + block_size;
        T* right = mid + block_size;
        assert_or_throw(std::is_sorted(left, mid, [proj](T a, T b) { return proj(a) < proj(b); }));
        assert_or_throw(std::is_sorted(mid, right, [proj](T a, T b) { return proj(a) < proj(b); }));
        T* split_left = std::find_if(left, mid, proj);
        T* split_right = std::find_if(mid, right, proj);
        int64_t n_zeros = (split_left - left) + (split_right - mid);
        if (n_zeros >= block_size) {
            std::rotate(split_left, mid, split_right);
        } else {
            std::rotate(left, split_left, mid);
            split_left = mid - split_left + left;
            std::rotate(split_left, split_right, split_right + (mid - split_left));
        }
    }
}

template <typename T, typename Pred>
int64_t block_count_if(T* first, T* last, int64_t block_size, Pred pred) {
    static_assert(std::is_invocable_r_v<bool, Pred, T>);
    assert_or_throw((last - first) % block_size == 0);
    int64_t n_blocks = (last - first) / block_size;
    int64_t res = 0;
    for (int64_t i = 0; i < n_blocks; i++) {
        if (pred(first[i * block_size])) {
            res++;
        }
    }
    return res;
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

template <typename T, typename Proj>
struct BufferStorage {
    T* buf0;
    T* buf1;
    int64_t n_bits;
    int64_t element_bits;
    Proj proj;

    static_assert(std::is_invocable_v<Proj, T>);

    static BufferStorage create(StorageAttributes attr, T* buf0, T* buf1, Proj proj) {
        return BufferStorage{
            .buf0 = buf0, .buf1 = buf1, .n_bits = attr.n_bits, .element_bits = attr.element_bits, .proj = proj};
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

template <typename T, typename Proj, typename Storage>
void sort_blocks_impl(T* first, T* last, int64_t block_size, Proj proj, Storage& storage) {
    static_assert(std::is_invocable_v<Proj, T>);
    int64_t n_blocks = (last - first) / block_size;
    if (n_blocks <= 1) {
        return;
    }
    int64_t n_zeros = block_count_if(first, last, block_size, [&proj](T x) { return proj(x) == 0; });
    std::array<int64_t, 2> pointers = {0, n_zeros};
    for (int64_t i = 0; i < n_blocks; i++) {
        int64_t key = proj(first[i * block_size]);
        storage.set(i, pointers[key]);
        pointers[key]++;
    }
    for (int64_t i = 0; i < n_blocks; i++) {
        for (int64_t j = storage.get(i); j != i;) {
            std::swap_ranges(first + (i * block_size), first + ((i + 1) * block_size), first + (j * block_size));
            int next = storage.get(j);
            storage.set(j, j);
            j = next;
        }
        storage.set(i, i);
    }
    storage.reset();
}

template <typename T, typename Proj>
void sort_blocks_using_word(T* first, T* last, int64_t block_size, Proj proj, int64_t word_bits) {
    static_assert(std::is_invocable_v<Proj, T>);
    assert_or_throw((last - first) % block_size == 0);
    int64_t n_blocks = (last - first) / block_size;
    if (n_blocks <= 1) {
        return;
    }
    int64_t element_bits = ceil_log2(n_blocks);
    assert_or_throw(n_blocks * element_bits <= word_bits, std::format("{} {} {}", n_blocks, element_bits, word_bits));
    auto storage = WordStorage::create({.n_bits = word_bits, .element_bits = element_bits});
    sort_blocks_impl(first, last, block_size, proj, storage);
}

template <typename T, typename Proj>
void sort_blocks_using_buffer(T* first, T* last, int64_t block_size, T* buf0, T* buf1, int64_t buffer_len, Proj proj) {
    static_assert(std::is_invocable_v<Proj, T>);
    assert_or_throw((last - first) % block_size == 0);
    int64_t n_blocks = (last - first) / block_size;
    if (n_blocks <= 1) {
        return;
    }
    int64_t element_bits = ceil_log2(n_blocks);
    assert_or_throw(n_blocks * element_bits <= buffer_len, std::format("{} {} {}", n_blocks, element_bits, buffer_len));
    auto storage =
        BufferStorage<T, Proj>::create({.n_bits = buffer_len, .element_bits = element_bits}, buf0, buf1, proj);
    sort_blocks_impl(first, last, block_size, proj, storage);
}

template <typename T, typename Proj>
void inplace_01_merge(T* first, T* last, Proj proj) {
    static_assert(std::is_invocable_v<Proj, T>);
    T* split_left = std::find_if(first, last, proj);
    T* mid = std::find_if(split_left, last, [proj](T x) { return proj(x) == 0; });
    T* split_right = std::find_if(mid, last, proj);
    std::rotate(split_left, mid, split_right);
    assert_or_throw(std::is_sorted(first, last, [proj](T a, T b) { return proj(a) < proj(b); }));
}

template <typename T, typename Proj>
void inplace_stable_01_partition(T* first, T* last, Proj proj) {
    static_assert(std::is_invocable_v<Proj, T>);
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
    T* buf0;
    std::tie(buf0, first, last) = stable_collect_first_n(first, last, buffer_len, [proj](T x) { return proj(x) == 0; });
    if (first - buf0 < buffer_len) {
        return;
    }
    T* buf1;
    std::tie(buf1, first, last) = stable_collect_first_n(first, last, buffer_len, [proj](T x) { return proj(x) == 1; });
    if (first - buf1 < buffer_len) {
        std::rotate(buf1, first, last);
        return;
    }
    len = last - first;
    int64_t block_size = 1;
    // inter-block sorting, using word as counter and marker
    for (int64_t step = 0; step < 2; step++) {
        int64_t merge_size = block_size * max_blocks_for_word;
        for (int64_t start = 0; start < len; start += merge_size) {
            int64_t end = std::min(start + merge_size, len);
            int64_t end_l2_aligned = end / block_size * block_size;
            int64_t mid = std::max(start, end_l2_aligned - block_size);
            homogenize_blocks(first + start, first + end_l2_aligned, block_size, proj);
            sort_blocks_using_word(first + start, first + mid, block_size, proj, max_word_bits);
            inplace_01_merge(first + start, first + end_l2_aligned, proj);
            inplace_01_merge(first + start, first + end, proj);
        }
        block_size = merge_size;
    }
    // inter-block sorting, using buffer as counter and marker
    for (int64_t step = 0; step < 3; step++) {
        int64_t merge_size = block_size * max_blocks_for_buffer;
        for (int64_t start = 0; start < len; start += merge_size) {
            int64_t end = std::min(start + merge_size, len);
            int64_t end_l2_aligned = end / block_size * block_size;
            int64_t mid = std::max(start, end_l2_aligned - block_size);
            homogenize_blocks(first + start, first + end_l2_aligned, block_size, proj);
            sort_blocks_using_buffer(first + start, first + mid, block_size, buf0, buf1, buffer_len, proj);
            inplace_01_merge(first + start, first + end_l2_aligned, proj);
            inplace_01_merge(first + start, first + end, proj);
        }
        block_size = merge_size;
    }
    assert_or_throw(block_size >= len);

    inplace_01_merge(buf0, last, proj);
}

template <typename T, typename Pred>
void inplace_stable_partition(T* first, T* last, Pred pred) {
    static_assert(std::is_invocable_r_v<bool, Pred, T>);
    inplace_stable_01_partition(first, last, [pred](T x) { return pred(x) ? 0 : 1; });
}
}  // namespace inplace_stable_partition
}  // namespace tcs
