#pragma once

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <format>
#include <optional>
#include <ranges>
#include <source_location>
#include <vector>

namespace tcs {
namespace ds {
namespace scapegoat_table {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

template <typename T, typename Proj = std::identity>
struct ScapegoatTable {
    static constexpr double tau_root = 0.25;
    static constexpr double tau_leaf = 0.75;
    static constexpr int64_t max_capacity = 1048576;

    int64_t capacity_ = 0;
    int64_t block_size_ = 0;
    int64_t n_blocks_ = 0;
    int64_t height_ = 0;
    std::vector<int64_t> counts_{0};  // counts_[0] is placeholder
    std::vector<T> data_;
    Proj proj_;
    ScapegoatTable(Proj proj = {}) : proj_(proj) {};

    double tau(int64_t level) const {
        return tau_root + ((tau_leaf - tau_root) * static_cast<double>(level) / height_);
    }
    bool genuine(int64_t index) const {
        return index == capacity_ - 1 || proj_(data_[index]) != proj_(data_[index + 1]);
    }

    static std::tuple<int64_t, int64_t, int64_t, int64_t> dimensions(int64_t size) {
        assert_or_throw(size <= max_capacity);
        int64_t block_size = 1;
        int64_t capacity = 0;
        while (true) {
            capacity = block_size;
            while (capacity < (int64_t{1} << block_size)) {
                capacity *= 2;
            }
            if (capacity >= size) {
                break;
            }
            block_size++;
        }
        int64_t n_blocks = capacity / block_size;
        int64_t height = std::bit_width(uint64_t(n_blocks)) - 1;
        return {capacity, block_size, n_blocks, height};
    }

    void redistribute(int64_t l, int64_t r, std::span<T> keys) {
        if (keys.empty()) {
            return;
        }
        int64_t len = (r - l) * block_size_;
        assert_or_throw(static_cast<int64_t>(keys.size()) <= len);
        for (int64_t i = 0; i < len; i++) {
            data_[(l * block_size_) + i] = keys[i * keys.size() / len];
        }
        assert_or_throw(proj_(keys.back()) == proj_(data_[(r * block_size_) - 1]));
    }

    std::vector<T> genuine_keys(int64_t l, int64_t r) const {
        std::vector<T> keys;
        for (int64_t i = l * block_size_; i < r * block_size_; i++) {
            if (genuine(i)) {
                keys.push_back(data_[i]);
            }
        }
        return keys;
    }

    void update_counts(int64_t l, int64_t r) {
        for (int64_t i = l; i < r; i++) {
            counts_[n_blocks_ + i] =
                std::ranges::count_if(std::views::iota(i * block_size_, (i + 1) * block_size_),
                    [this](int64_t index) { return genuine(index); });
        }
        for (int64_t level = height_ - 1; level >= 0; level--) {
            l /= 2;
            r = (r + 1) / 2;
            for (int64_t i = l; i < r; i++) {
                counts_[(1 << level) + i] =
                    counts_[((1 << level) + i) * 2] + counts_[(((1 << level) + i) * 2) + 1];
            }
        }
    }

    void assign(int64_t size, T value) {
        std::tie(capacity_, block_size_, n_blocks_, height_) = dimensions(size);
        data_.assign(capacity_, value);
        counts_.assign(n_blocks_ * 2, 0);
        update_counts(0, n_blocks_);
    }

    void resize(int64_t size) {
        auto keys = genuine_keys(0, n_blocks_);
        std::tie(capacity_, block_size_, n_blocks_, height_) = dimensions(size);
        data_.resize(capacity_, T{});
        counts_.assign(n_blocks_ * 2, 0);
        redistribute(0, n_blocks_, keys);
        update_counts(0, n_blocks_);
    }

    void rebalance(int64_t block_idx) {
        int64_t flatten_level = -1;
        int64_t i = block_idx;
        for (int64_t level = height_; level >= 0; level--) {
            counts_[(1 << level) + i]++;
            if (flatten_level == -1 &&
                counts_[(1 << level) + i] < (1 << (height_ - level)) * block_size_ * tau(level)) {
                flatten_level = level;
            }
            i /= 2;
        }
        if (flatten_level >= 0 && flatten_level < height_) {
            int64_t len = (1 << (height_ - flatten_level));
            auto keys = genuine_keys(block_idx / len * len, ((block_idx / len) + 1) * len);
            redistribute(block_idx / len * len, ((block_idx / len) + 1) * len, keys);
            update_counts(block_idx / len * len, ((block_idx / len) + 1) * len);
        }
        if (flatten_level == -1) {
            resize(std::ceil(counts_[1] / tau(0) * 2));
        }
    }

    void insert(T value) {
        if (data_.empty()) {
            assign(2, value);
            return;
        }
        int64_t index = std::ranges::lower_bound(data_, proj_(value), {}, proj_) - data_.begin();
        // exist
        if (index < capacity_ && proj_(data_[index]) == proj_(value)) {
            return;
        }
        int64_t right = index;
        while (right < capacity_ && genuine(right)) {
            right++;
        }
        if (right < capacity_) {
            std::ranges::copy_backward(
                data_.begin() + index, data_.begin() + right, data_.begin() + right + 1);
            data_[index] = value;
            rebalance(right / block_size_);
            return;
        }
        int64_t left = index - 1;
        while (left >= 0 && genuine(left)) {
            left--;
        }
        if (left >= 0) {
            std::ranges::copy(
                data_.begin() + left + 1, data_.begin() + index, data_.begin() + left);
            data_[index - 1] = value;
            rebalance(left / block_size_);
            return;
        }
        assert_or_throw(false);
    }

    bool contains(const T& value) const {
        return std::ranges::binary_search(data_, proj_(value), {}, proj_);
    }

    std::optional<T> lower_bound(const T& value) const {
        auto it = std::ranges::lower_bound(data_, proj_(value), {}, proj_);
        if (it == data_.end()) {
            return std::nullopt;
        }
        return *it;
    }
};
}  // namespace scapegoat_table
}  // namespace ds
}  // namespace tcs
