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
#include <cstdint>
#include <functional>
#include <optional>
#include <tuple>

#include "tcs/basic/bit_vector.hpp"
#include "tcs/common/assert.hpp"
#include "tcs/common/bit.hpp"

namespace tcs::readonly::mtree_sort {
template <typename RandomIt, typename IterOptProj>
struct MTreeAttributes {
    RandomIt first;
    RandomIt last;
    int64_t height;
    int64_t root_sub_block_size;
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
    basic::BitVector state_;
    basic::BitVector mu_;
    IterOptProj iter_opt_proj_;

    int64_t data_offset(int64_t level, int64_t offset) const {
        common::assert_or_throw(level >= 0 && level <= height_);
        common::assert_or_throw(offset >= 0 && offset <= (int64_t{1} << level));
        return ((height_ - level + 2) * (int64_t{1} << level)) - height_ - 2 +
               (offset * (height_ - level));
    }

    static MTree create(MTreeAttributes<RandomIt, IterOptProj> attrs) {
        auto [first, last, height, root_sub_block_size, iter_opt_proj] = attrs;
        int64_t n_blocks = int64_t{1} << height;
        int64_t block_size = root_sub_block_size * n_blocks;
        int64_t capacity = block_size * n_blocks;
        auto state = basic::BitVector::create();
        auto mu = basic::BitVector::create();
        common::assert_or_throw(first < last && last - first <= capacity);
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
        common::assert_or_throw(level >= 0 && level <= height_);
        common::assert_or_throw(offset >= 0 && offset < (int64_t{1} << level));
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
        common::assert_or_throw(level >= 0 && level <= height_);
        common::assert_or_throw(offset >= 0 && offset < (int64_t{1} << level));
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
        common::assert_or_throw(level >= 0 && level < height_);
        common::assert_or_throw(offset >= 0 && offset < (int64_t{1} << level));
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
    common::assert_or_throw(first <= last);
    common::assert_or_throw(workspace > 0);
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
    int64_t height = std::max(common::ceil_log2(workspace), int64_t{1});
    int64_t n_blocks = int64_t{1} << height;
    int64_t root_sub_block_size = (size + (n_blocks * n_blocks) - 1) / (n_blocks * n_blocks);

    auto tree = MTree<RandomIt, decltype(iter_opt_proj)>::create(MTreeAttributes{.first = first,
        .last = first + size,
        .height = height,
        .root_sub_block_size = root_sub_block_size,
        .iter_opt_proj = iter_opt_proj});
    for (int64_t i = 0; i < size; i++) {
        std::optional<RandomIt> min_opt = tree.min();
        tree.pop();
        common::assert_or_throw(min_opt.has_value());
        *output = *min_opt.value();
        ++output;
    }
}
}  // namespace tcs::readonly::mtree_sort
