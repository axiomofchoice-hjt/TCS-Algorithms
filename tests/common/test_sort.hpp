#pragma once

#include <algorithm>
#include <random>
#include <ranges>

#include "common/test_array.hpp"
#include "common/utest.hpp"

struct TestSortParam {
    int64_t size;
    int64_t max_key;
    int64_t repeat;
};

template <typename Func>
auto gen_random_sort_test(Func func, bool stable, int seed) {
    return [=](TestSortParam param) {
        std::mt19937 gen(seed);
        std::uniform_int_distribution<int64_t> key_dist(1, param.max_key);

        for ([[maybe_unused]] int64_t i : std::views::iota(0, param.repeat)) {
            auto arr = std::views::iota(0, param.size) | std::views::transform([&](int64_t i) {
                return IndexedElement{key_dist(gen), i};
            }) | std::ranges::to<TestArray>();

            auto expected = arr;
            std::ranges::stable_sort(expected, {}, IndexedElement::proj);

            func(arr);

            if (stable) {
                utest::assert_or_throw(arr.is_stable());
            }
            utest::assert_or_throw(arr == expected);
        }
    };
}
