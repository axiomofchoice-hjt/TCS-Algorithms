#pragma once

#include <algorithm>
#include <cmath>
#include <iterator>
#include <optional>
#include <vector>

#include "tcs/basic/bfprt.hpp"
#include "tcs/common/bit.hpp"

namespace tcs::readonly::multipass_select {
template <typename T, typename Proj>
std::vector<T> quartiles(std::vector<T> data, int64_t n_quartiles, Proj proj) {
    int64_t size = data.size();
    common::assert_or_throw(size % n_quartiles == 0);
    for (int64_t i = 0; i < n_quartiles; i++) {
        basic::bfprt::bfprt(data.begin() + (size / n_quartiles * i),
            data.begin() + (size / n_quartiles * (i + 1)) - 1, data.end(), proj);
        data[i] = data[(size / n_quartiles * (i + 1)) - 1];
    }
    data.erase(data.begin() + n_quartiles, data.end());
    return std::move(data);
}

template <typename T>
std::vector<T> thin(std::vector<T> data) {
    int64_t size = data.size();
    common::assert_or_throw(size % 2 == 0);
    for (int64_t i = 1; i < size; i += 2) {
        data[i / 2] = data[i];
    }
    data.erase(data.begin() + (size / 2), data.end());
    return std::move(data);
}

template <typename T, typename Proj>
std::vector<T> merge(std::vector<T> data0, std::vector<T> data1, Proj proj) {
    int64_t size0 = data0.size();
    std::ranges::copy(data1, std::back_inserter(data0));
    std::ranges::inplace_merge(data0, data0.begin() + size0, {}, proj);
    return std::move(data0);
}

template <typename T, typename Proj = std::identity>
struct Sampler {
    struct Block {
        int64_t level_ = 0;
        std::vector<T> data_;
    };
    int64_t min_block_size_ = 0;
    int64_t n_quartiles_ = 0;
    int64_t spacing_level_ = 0;
    std::vector<Block> blocks_;
    std::optional<T> max_;
    Proj proj_;

    int64_t n_blocks() const { return blocks_.size(); }

    static Sampler create(
        int64_t min_block_size, int64_t n_quartiles, int64_t spacing_level, Proj proj) {
        common::assert_or_throw(min_block_size >= 1 &&
                                (min_block_size & (min_block_size - 1)) == 0 &&
                                n_quartiles % 2 == 0);
        return {.min_block_size_ = min_block_size,
            .n_quartiles_ = n_quartiles,
            .spacing_level_ = spacing_level,
            .blocks_ = {},
            .max_ = std::nullopt,
            .proj_ = proj};
    }

    void append(T value) {
        if (!max_.has_value() || proj_(max_.value()) < proj_(value)) {
            max_ = value;
        }
        if (blocks_.empty() || blocks_.back().level_ != -1) {
            blocks_.push_back({.level_ = -1, .data_ = {}});
        }
        blocks_.back().data_.push_back(value);
        if (blocks_.back().level_ == -1 &&
            static_cast<int64_t>(blocks_.back().data_.size()) == min_block_size_ * n_quartiles_) {
            blocks_.back().data_ = quartiles(std::move(blocks_.back().data_), n_quartiles_, proj_);
            blocks_.back().level_++;
        }
        while (n_blocks() >= 2) {
            auto& a = blocks_[n_blocks() - 2];
            auto& b = blocks_[n_blocks() - 1];
            if (a.level_ == b.level_ && a.level_ < spacing_level_) {
                a.data_ = merge(std::move(a.data_), std::move(b.data_), proj_);
                a.level_++;
                blocks_.pop_back();
                continue;
            }
            if (a.level_ == b.level_ && a.level_ >= spacing_level_) {
                a.data_ = thin(std::move(a.data_));
                b.data_ = thin(std::move(b.data_));
                a.data_ = merge(std::move(a.data_), std::move(b.data_), proj_);
                a.level_++;
                blocks_.pop_back();
                continue;
            }
            break;
        }
    }

    std::tuple<int64_t, std::vector<T>> finalize() {
        common::assert_or_throw(!blocks_.empty());
        common::assert_or_throw(max_.has_value());
        while (blocks_.size() > 1 || blocks_[0].level_ < spacing_level_) {
            append(max_.value());
        }
        return {blocks_[0].level_, std::move(blocks_[0].data_)};
    }
};

template <typename ForwardIt, typename Proj = std::identity>
std::iter_value_t<ForwardIt> onepass(ForwardIt first, int64_t size, int64_t k,
    std::optional<std::iter_value_t<ForwardIt>> lower_bound,
    std::optional<std::iter_value_t<ForwardIt>> upper_bound, Proj proj = {}) {
    using T = std::iter_value_t<ForwardIt>;
    ForwardIt input_it = first;
    std::vector<std::iter_value_t<ForwardIt>> buffer;
    int64_t lo = 0;
    int64_t hi = 0;
    for (int64_t i = 0; i < size; i++) {
        T input = *input_it;
        if (lower_bound.has_value() && proj(input) <= proj(lower_bound.value())) {
            lo++;
        } else if (upper_bound.has_value() && proj(input) >= proj(upper_bound.value())) {
            hi++;
        } else {
            buffer.push_back(input);
        }
        ++input_it;
    }
    common::assert_or_throw(k >= lo - 1 && k <= size - hi);
    if (k == lo - 1) {
        return lower_bound.value();
    }
    if (k == size - hi) {
        return upper_bound.value();
    }
    basic::bfprt::bfprt(buffer.begin(), buffer.begin() + k - lo, buffer.end(), proj);
    return buffer[k - lo];
}

template <typename ForwardIt, typename Proj = std::identity>
std::tuple<std::optional<std::iter_value_t<ForwardIt>>, std::optional<std::iter_value_t<ForwardIt>>,
    int64_t>
narrow(ForwardIt first, int64_t size, int64_t k,
    std::optional<std::iter_value_t<ForwardIt>> lower_bound,
    std::optional<std::iter_value_t<ForwardIt>> upper_bound, int64_t population, int64_t workspace,
    Proj proj = {}) {
    using T = std::iter_value_t<ForwardIt>;
    if (population <= workspace) {
        auto res = onepass(first, size, k, lower_bound, upper_bound, proj);
        return {res, res, 0};
    }
    auto n_quartiles = std::max(common::bit_ceil(size / population), int64_t{4});
    auto min_block_size =
        std::max(common::bit_floor(workspace / common::ceil_log2(size) / n_quartiles), int64_t{1});
    {
        int64_t q = population / n_quartiles;
        min_block_size = std::min(min_block_size,
            std::max(common::bit_floor(static_cast<int64_t>(std::sqrt(q))), int64_t{1}));
    }
    auto spacing_level = common::ceil_log2(min_block_size);
    ForwardIt input_it = first;
    int64_t lo = 0;
    int64_t hi = 0;
    auto sampler =
        Sampler<T, decltype(proj)>::create(min_block_size, n_quartiles, spacing_level, proj);
    for (int64_t i = 0; i < size; i++) {
        T input = *input_it;
        if (lower_bound.has_value() && proj(input) <= proj(lower_bound.value())) {
            lo++;
        } else if (upper_bound.has_value() && proj(input) >= proj(upper_bound.value())) {
            hi++;
        } else {
            sampler.append(input);
        }
        ++input_it;
    }
    common::assert_or_throw(population >= size - lo - hi);
    common::assert_or_throw(lo - 1 <= k && k <= size - hi);
    if (k == lo - 1) {
        return {lower_bound, lower_bound, 0};
    }
    if (k == size - hi) {
        return {upper_bound, upper_bound, 0};
    }
    auto [level, samples] = sampler.finalize();

    int64_t height = level - spacing_level;
    int64_t pw = int64_t{1} << level;
    int64_t upper_sample = (k - lo) / pw;
    int64_t lower_sample = upper_sample - height - (min_block_size - 1);
    if (lower_sample >= 0) {
        common::assert_or_throw(lower_sample < static_cast<int64_t>(samples.size()));
        lower_bound = samples[lower_sample];
    }
    if (upper_sample < static_cast<int64_t>(samples.size())) {
        common::assert_or_throw(upper_sample >= 0);
        upper_bound = samples[upper_sample];
    }
    population =
        std::min(size - lo - hi, std::max<int64_t>(0, ((2 * height) + (2 * min_block_size) - 3) *
                                                          min_block_size * (int64_t{1} << height)));
    return {lower_bound, upper_bound, population};
}

template <typename ForwardIt, typename Proj = std::identity>
std::iter_value_t<ForwardIt> multipass_select(
    ForwardIt first, int64_t size, int64_t k, int64_t workspace, Proj proj = {}) {
    using T = std::iter_value_t<ForwardIt>;
    std::optional<T> lower_bound;
    std::optional<T> upper_bound;
    int64_t population = size;
    while (population > 0) {
        std::tie(lower_bound, upper_bound, population) =
            narrow(first, size, k, lower_bound, upper_bound, population, workspace, proj);
    }
    return lower_bound.value();
}
}  // namespace tcs::readonly::multipass_select
