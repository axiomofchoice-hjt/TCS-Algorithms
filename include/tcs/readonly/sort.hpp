#pragma once

#include <algorithm>
#include <bit>
#include <climits>
#include <cstdint>
#include <format>
#include <functional>
#include <optional>
#include <source_location>
#include <tuple>
#include <vector>

namespace tcs::readonly::sort {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

constexpr int64_t n_machine_word_bits = sizeof(uint64_t) * CHAR_BIT;

inline int64_t floor_log2(int64_t x) {
    assert_or_throw(x > 0, "ceil_log2: argument must be positive");
    return std::bit_width(static_cast<uint64_t>(x)) - 1;
}

inline int64_t ceil_log2(int64_t x) {
    assert_or_throw(x > 0, "ceil_log2: argument must be positive");
    return std::bit_width(static_cast<uint64_t>(x) - 1);
}

struct BitVector {
    int64_t n_word_bits_ = 0;
    int64_t size_ = 0;
    std::vector<uint64_t> data_;

    static BitVector create(int64_t size, int64_t n_word_bits) {
        assert_or_throw(n_word_bits > 0 && n_word_bits <= n_machine_word_bits);
        auto data = std::vector<uint64_t>((size + n_word_bits - 1) / n_word_bits, 0);
        return {.n_word_bits_ = n_word_bits, .size_ = size, .data_ = data};
    }

    bool get(int64_t index) const {
        assert_or_throw(index >= 0 && index < size_);
        return (data_[index / n_word_bits_] >> (index % n_word_bits_) & 1) == 1;
    }

    void set(int64_t index, bool value) {
        assert_or_throw(index >= 0 && index < size_);
        uint64_t& word = data_[index / n_word_bits_];
        uint64_t mask = uint64_t{1} << (index % n_word_bits_);
        word = value ? word | mask : word & ~mask;
    }
};

template <typename RandomIt, typename IterOptProj>
struct MTreeAttributes {
    RandomIt first;
    RandomIt last;
    int64_t height;
    int64_t sub_block_size;
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
    int64_t sub_block_size_ = 0;
    int64_t block_size_ = 0;
    BitVector state_;
    BitVector mu_;
    IterOptProj iter_opt_proj;

    static MTree create(MTreeAttributes<RandomIt, IterOptProj> attrs) {
        int64_t n_blocks = int64_t{1} << attrs.height;
        int64_t block_size = attrs.sub_block_size * n_blocks;
        int64_t size = block_size * n_blocks;
        auto state = BitVector::create(n_blocks, attrs.n_word_bits);
        auto mu = BitVector::create(n_blocks, attrs.n_word_bits);
        assert_or_throw(attrs.first < attrs.last && attrs.last - attrs.first <= size);
        MTree tree{
            .first_ = attrs.first,
            .last_ = attrs.last,
            .filter_ = std::nullopt,
            .height_ = attrs.height,
            .n_blocks_ = n_blocks,
            .sub_block_size_ = attrs.sub_block_size,
            .block_size_ = block_size,
            .state_ = state,
            .mu_ = mu,
            .iter_opt_proj = attrs.iter_opt_proj,
        };
        for (int64_t node_id = n_blocks - 1; node_id >= 1; node_id--) {
            tree.update(node_id);
        }
        return tree;
    }

    std::tuple<int64_t, int64_t> range(int64_t node_id) const {
        assert_or_throw(node_id >= 1 && node_id < n_blocks_ * 2);
        int64_t mu = 0;
        int64_t mu_range = 1;
        while (node_id < n_blocks_) {
            mu |= int64_t{mu_.get(node_id)} * mu_range;
            mu_range <<= 1;
            node_id = (node_id * 2) + int64_t{state_.get(node_id)};
        }
        int64_t l = ((node_id - n_blocks_) * block_size_) + (mu * block_size_ / mu_range);
        int64_t r = l + (block_size_ / mu_range);
        return {l, r};
    }

    std::optional<RandomIt> min(int64_t node_id) const {
        assert_or_throw(node_id >= 1 && node_id < n_blocks_ * 2);
        auto [l, r] = range(node_id);
        std::optional<RandomIt> res;
        for (int64_t i = l; i < r; i++) {
            if (i < last_ - first_ &&
                (!filter_.has_value() || iter_opt_proj(first_ + i) > iter_opt_proj(filter_)) &&
                iter_opt_proj(first_ + i) < iter_opt_proj(res)) {
                res = first_ + i;
            }
        }
        return res;
    }

    void update(int64_t node_id) {
        assert_or_throw(node_id >= 1 && node_id < n_blocks_);
        auto l_min = min(node_id * 2);
        auto r_min = min((node_id * 2) + 1);
        int64_t hid = floor_log2(node_id);
        int64_t level_block_size = int64_t{1} << hid;
        if (!l_min.has_value() && !r_min.has_value()) {
            state_.set(node_id, false);
            mu_.set(node_id, false);
        } else if (iter_opt_proj(l_min) < iter_opt_proj(r_min)) {
            state_.set(node_id, false);
            mu_.set(node_id,
                (l_min.value() - first_) / sub_block_size_ % n_blocks_ / level_block_size % 2 == 1);
        } else {
            state_.set(node_id, true);
            mu_.set(node_id,
                (r_min.value() - first_) / sub_block_size_ % n_blocks_ / level_block_size % 2 == 1);
        }
    }

    std::optional<RandomIt> min() const { return min(1); }

    void pop() {
        filter_ = min();
        int64_t node_id = (n_blocks_ + ((filter_.value() - first_) / block_size_)) >> 1;
        while (node_id >= 1) {
            update(node_id);
            node_id >>= 1;
        }
    }
};

template <typename RandomIt, typename OutputIt, typename Proj = std::identity>
void sort(RandomIt first, RandomIt last, OutputIt output, int64_t workspace, Proj proj = {}) {
    assert_or_throw(first <= last);
    assert_or_throw(workspace > 0);
    int64_t size = last - first;
    if (size == 0) {
        return;
    }
    if (size == 1) {
        *output = *first;
        return;
    }
    auto iter_opt_proj = [proj, first](std::optional<RandomIt> opt) {
        if (!opt.has_value()) {
            return std::tuple{true, proj(*first), first};
        }
        return std::tuple{false, proj(*opt.value()), opt.value()};
    };
    int64_t logn = std::max(ceil_log2(size), int64_t{1});
    int64_t height = std::max(ceil_log2(logn), int64_t{1});
    int64_t n_blocks = int64_t{1} << height;
    int64_t sub_block_size = std::max(size / (workspace * n_blocks), int64_t{1});
    int64_t block_size = sub_block_size * n_blocks;
    int64_t sub_vector = block_size * n_blocks;
    int64_t n_sub_vectors = (size + sub_vector - 1) / sub_vector;
    int64_t n_word_bits = logn;

    std::vector<std::optional<RandomIt>> heap;
    std::vector<MTree<RandomIt, decltype(iter_opt_proj)>> trees;
    for (int64_t i = 0; i < n_sub_vectors; i++) {
        int64_t block_start = i * sub_vector;
        int64_t block_end = std::min(size, block_start + sub_vector);
        auto tree = MTree<RandomIt, decltype(iter_opt_proj)>::create(
            MTreeAttributes{.first = first + block_start,
                .last = first + block_end,
                .height = height,
                .sub_block_size = sub_block_size,
                .n_word_bits = n_word_bits,
                .iter_opt_proj = iter_opt_proj});
        heap.push_back(tree.min());
        trees.push_back(std::move(tree));
    }
    std::ranges::make_heap(heap, std::greater{}, iter_opt_proj);
    for (int64_t i = 0; i < size; i++) {
        assert_or_throw(heap[0].has_value());
        auto x = heap[0].value();
        *output = *x;
        ++output;
        std::ranges::pop_heap(heap, std::greater{}, iter_opt_proj);
        int64_t sub_vector_id = (x - first) / sub_vector;
        trees[sub_vector_id].pop();
        heap.back() = trees[sub_vector_id].min();
        std::ranges::push_heap(heap, std::greater{}, iter_opt_proj);
    }
}
}  // namespace tcs::readonly::sort
