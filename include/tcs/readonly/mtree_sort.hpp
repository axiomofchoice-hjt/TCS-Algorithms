// M-tree sort (read-only input)
// --------------------------------------------------------------------------
// Writes the stably sorted permutation of [first, last) to `output`, reading
// the input only. The range is cut into at most `workspace` blocks and a full
// binary tree is built over them; each node stores which child holds its
// subtree minimum (state) and in which sub-block it lies (mu), so a pop costs
// O(n / workspace^2) plus the O(log workspace) tree walk.
//
// Time-space complexity: T * S = O(n^2) for Θ(log n) <= S <= Θ(n / log n),
// where S is the workspace budget in bits.

#pragma once

#include <algorithm>
#include <bit>
#include <climits>
#include <cstdint>
#include <format>
#include <functional>
#include <optional>
#include <source_location>
#include <stdexcept>
#include <string_view>
#include <tuple>
#include <vector>

namespace tcs::readonly::mtree_sort {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

constexpr int64_t n_machine_word_bits = sizeof(uint64_t) * CHAR_BIT;

inline int64_t ceil_log2(int64_t x) {
    assert_or_throw(x > 0, "ceil_log2: argument must be positive");
    return std::bit_width(static_cast<uint64_t>(x) - 1);
}

struct BitVector {
    int64_t n_word_bits_ = 0;
    int64_t size_ = 0;
    std::vector<uint64_t> data_;

    static uint64_t low_mask(int64_t len) {
        assert_or_throw(len >= 0 && len <= n_machine_word_bits);
        return len == n_machine_word_bits ? ~uint64_t{0} : (uint64_t{1} << len) - 1;
    }

    static BitVector create(int64_t n_word_bits) {
        assert_or_throw(n_word_bits > 0 && n_word_bits <= n_machine_word_bits);
        return {.n_word_bits_ = n_word_bits, .size_ = 0, .data_ = {}};
    }

    int64_t size() const { return size_; }

    void resize(int64_t new_size) {
        assert_or_throw(new_size >= 0);
        data_.resize((new_size + n_word_bits_ - 1) / n_word_bits_, 0);
        if (new_size % n_word_bits_ != 0) {
            data_.back() &= low_mask(new_size % n_word_bits_);
        }
        size_ = new_size;
    }

    uint64_t load(int64_t pos, int64_t len) const {
        assert_or_throw(pos >= 0 && len >= 0 && pos + len <= size_);
        assert_or_throw(len <= n_word_bits_);
        if (len == 0) {
            return 0;
        }
        int64_t off = pos % n_word_bits_;
        int64_t n_low = n_word_bits_ - off;
        uint64_t low = data_[pos / n_word_bits_] >> off;
        if (len <= n_low) {
            return low & low_mask(len);
        }
        return (low & low_mask(n_low)) | (data_[(pos + len) / n_word_bits_] & low_mask(len - n_low))
                                             << n_low;
    }

    void store(int64_t pos, int64_t len, uint64_t value) {
        assert_or_throw(pos >= 0 && len >= 0 && pos + len <= size_);
        assert_or_throw(len <= n_word_bits_);
        assert_or_throw(std::bit_width(value) <= len);
        if (len == 0) {
            return;
        }
        int64_t off = pos % n_word_bits_;
        int64_t n_low = n_word_bits_ - off;
        uint64_t& low_word = data_[pos / n_word_bits_];
        if (len <= n_low) {
            low_word = (low_word & ~(low_mask(len) << off)) | (value << off);
        } else {
            low_word = ((low_word & low_mask(off)) | (value << off)) & low_mask(n_word_bits_);
            uint64_t& high_word = data_[(pos + len) / n_word_bits_];
            high_word = (high_word & ~low_mask(len - n_low)) | (value >> n_low);
        }
    }
};

template <typename RandomIt, typename IterOptProj>
struct MTreeAttributes {
    RandomIt first;
    RandomIt last;
    int64_t height;
    int64_t root_sub_block_size;
    int64_t n_word_bits;
    IterOptProj iter_opt_proj;
};

template <typename RandomIt, typename IterOptProj>
struct MTree {
    RandomIt first_ = {};
    RandomIt last_ = {};
    std::optional<RandomIt> filter_ = {};
    int64_t height_ = 0;
    int64_t n_blocks_ = 0;
    int64_t root_sub_block_size_ = 0;
    int64_t block_size_ = 0;
    BitVector state_;
    BitVector mu_;
    IterOptProj iter_opt_proj_;

    int64_t data_offset(int64_t level, int64_t offset) const {
        assert_or_throw(level >= 0 && level <= height_);
        assert_or_throw(offset >= 0 && offset <= (int64_t{1} << level));
        return ((height_ - level + 2) * (int64_t{1} << level)) - height_ - 2 +
               (offset * (height_ - level));
    }

    static MTree create(MTreeAttributes<RandomIt, IterOptProj> attrs) {
        auto [first, last, height, root_sub_block_size, n_word_bits, iter_opt_proj] = attrs;
        int64_t n_blocks = int64_t{1} << height;
        int64_t block_size = root_sub_block_size * n_blocks;
        int64_t capacity = block_size * n_blocks;
        auto state = BitVector::create(n_word_bits);
        auto mu = BitVector::create(n_word_bits);
        assert_or_throw(first < last && last - first <= capacity);
        MTree tree{
            .first_ = first,
            .last_ = last,
            .filter_ = std::nullopt,
            .height_ = height,
            .n_blocks_ = n_blocks,
            .root_sub_block_size_ = root_sub_block_size,
            .block_size_ = block_size,
            .state_ = state,
            .mu_ = mu,
            .iter_opt_proj_ = iter_opt_proj,
        };
        tree.state_.resize(tree.data_offset(height, 0));
        tree.mu_.resize(tree.data_offset(height, 0));
        for (int64_t level = height - 1; level >= 0; level--) {
            for (int64_t i = 0; i < (int64_t{1} << level); i++) {
                tree.update(level, i);
            }
        }
        return tree;
    }

    std::tuple<int64_t, int64_t> range(int64_t level, int64_t offset) const {
        assert_or_throw(level >= 0 && level <= height_);
        assert_or_throw(offset >= 0 && offset < (int64_t{1} << level));
        int64_t n_sub_blocks = int64_t{1} << (height_ - level);
        int64_t off = data_offset(level, offset);
        int64_t len = height_ - level;
        int64_t state_v = state_.load(off, len);
        int64_t mu_v = mu_.load(off, len);
        int64_t l = (((offset * n_sub_blocks) + state_v) * block_size_) +
                    (mu_v * block_size_ / n_sub_blocks);
        int64_t r = l + (block_size_ / n_sub_blocks);
        return {l, r};
    }

    std::optional<RandomIt> min(int64_t level, int64_t offset) const {
        assert_or_throw(level >= 0 && level <= height_);
        assert_or_throw(offset >= 0 && offset < (int64_t{1} << level));
        auto [l, r] = range(level, offset);
        std::optional<RandomIt> res;
        for (int64_t i = l; i < r; i++) {
            if (i < last_ - first_ &&
                (!filter_.has_value() || iter_opt_proj_(first_ + i) > iter_opt_proj_(filter_)) &&
                iter_opt_proj_(first_ + i) < iter_opt_proj_(res)) {
                res = first_ + i;
            }
        }
        return res;
    }

    void update(int64_t level, int64_t offset) {
        assert_or_throw(level >= 0 && level < height_);
        assert_or_throw(offset >= 0 && offset < (int64_t{1} << level));
        auto lchild_min = min(level + 1, offset * 2);
        auto rchild_min = min(level + 1, (offset * 2) + 1);
        int64_t n_level_nodes = int64_t{1} << level;
        int64_t off = data_offset(level, offset);
        int64_t len = height_ - level;
        if (!lchild_min.has_value() && !rchild_min.has_value()) {
            state_.store(off, len, 0);
            mu_.store(off, len, 0);
        } else if (iter_opt_proj_(lchild_min) < iter_opt_proj_(rchild_min)) {
            int64_t child_off = data_offset(level + 1, offset * 2);
            int64_t child_len = len - 1;
            state_.store(off, len, state_.load(child_off, child_len));
            mu_.store(off, len,
                (mu_.load(child_off, child_len) << 1) |
                    ((lchild_min.value() - first_) / root_sub_block_size_ % n_blocks_ /
                        n_level_nodes % 2));
        } else {
            int64_t child_off = data_offset(level + 1, (offset * 2) + 1);
            int64_t child_len = len - 1;
            state_.store(off, len,
                state_.load(child_off, child_len) | (int64_t{1} << (height_ - level - 1)));
            mu_.store(off, len,
                (mu_.load(child_off, child_len) << 1) |
                    ((rchild_min.value() - first_) / root_sub_block_size_ % n_blocks_ /
                        n_level_nodes % 2));
        }
    }

    std::optional<RandomIt> min() const { return min(0, 0); }

    void pop() {
        filter_ = min();
        int64_t block_id = (filter_.value() - first_) / block_size_;
        for (int64_t level = height_ - 1; level >= 0; level--) {
            update(level, block_id >> (height_ - level));
        }
    }
};

template <typename RandomIt, typename OutputIt, typename Proj = std::identity>
void mtree_sort(RandomIt first, RandomIt last, OutputIt output, int64_t workspace, Proj proj = {}) {
    assert_or_throw(first <= last);
    assert_or_throw(workspace > 0);
    int64_t size = last - first;
    if (size == 0) {
        return;
    }
    workspace = std::min(workspace, size);
    auto iter_opt_proj = [proj, first](std::optional<RandomIt> opt) {
        if (!opt.has_value()) {
            return std::tuple{true, proj(*first), first};
        }
        return std::tuple{false, proj(*opt.value()), opt.value()};
    };
    int64_t height = std::max(ceil_log2(workspace), int64_t{1});
    int64_t n_blocks = int64_t{1} << height;
    int64_t root_sub_block_size = (size + (n_blocks * n_blocks) - 1) / (n_blocks * n_blocks);
    int64_t n_word_bits = std::max(ceil_log2(size), int64_t{1});

    auto tree = MTree<RandomIt, decltype(iter_opt_proj)>::create(MTreeAttributes{.first = first,
        .last = first + size,
        .height = height,
        .root_sub_block_size = root_sub_block_size,
        .n_word_bits = n_word_bits,
        .iter_opt_proj = iter_opt_proj});
    for (int64_t i = 0; i < size; i++) {
        std::optional<RandomIt> min_opt = tree.min();
        assert_or_throw(min_opt.has_value());
        tree.pop();
        *output = *min_opt.value();
        ++output;
    }
}
}  // namespace tcs::readonly::mtree_sort
