#include <algorithm>
#include <random>
#include <ranges>
#include <vector>

#include "common_test.hpp"
#include "tcs/inplace_stable_merge.hpp"
#include "utest.hpp"

namespace {

struct TestParam {
    int64_t size;
    int64_t left_size;
    int64_t max_key;
    int64_t repeat;
};

constexpr int kRandomSeed = 42;
constexpr int64_t kSweepMaxSize = 100;

constexpr TestParam kCases[] = {
    {20, 10, 10, 20},
    {50, 25, 20, 20},
    {100, 10, 10, 20},
    {100, 40, 10, 20},
    {100, 90, 10, 20},
    {100, 10, 30, 20},
    {100, 40, 30, 20},
    {100, 90, 30, 20},
    {100, 10, 100, 20},
    {100, 40, 100, 20},
    {100, 90, 100, 20},
    {1000, 500, 1000, 20},
    {1000, 500, 10, 20},
    {10000, 5000, 5000, 2},
    {100000, 50000, 50000, 1},
    {1000, 500, 1, 1},    // all elements share the same key
    {1000, 0, 10, 1},     // empty left half
    {1000, 1000, 10, 1},  // empty right half
    {1000, 0, 1, 1},      // empty left half, single key
    {1000, 1000, 1, 1},   // empty right half, single key
};

void random_test(const TestParam& param) {
    std::mt19937 gen(kRandomSeed);
    std::uniform_int_distribution<int64_t> key_dist(1, param.max_key);

    for ([[maybe_unused]] int64_t i : std::views::iota(0, param.repeat)) {
        auto arr = std::views::iota(0, param.size) | std::views::transform([&](int64_t) {
            return IndexedElement{key_dist(gen), 0};
        }) | std::ranges::to<std::vector<IndexedElement>>();

        std::ranges::sort(arr.begin(), arr.begin() + param.left_size, {}, IndexedElement::proj);
        std::ranges::sort(arr.begin() + param.left_size, arr.end(), {}, IndexedElement::proj);

        for (auto [i, el] : arr | std::views::enumerate) {
            el.index = static_cast<int64_t>(i);
        }

        auto expected = arr;
        std::ranges::inplace_merge(
            expected, expected.begin() + param.left_size, {}, IndexedElement::proj);

        tcs::inplace_stable_merge::inplace_stable_merge(
            arr.begin(), arr.begin() + param.left_size, arr.end(), IndexedElement::proj);

        utest::assert_or_throw(is_stable(arr));
        utest::assert_or_throw(
            std::ranges::equal(arr, expected, {}, IndexedElement::proj, IndexedElement::proj));
    }
}

auto sweep = utest::test("inplace_stable_merge", "[inplace_stable_merge]", [] {
    for (int64_t n = 0; n <= kSweepMaxSize; n++) {
        random_test({.size = n, .left_size = n / 2, .max_key = kSweepMaxSize, .repeat = 2});
    }
});

auto random = utest::test("inplace_stable_merge", "[inplace_stable_merge]", [] {
    for (const auto& param : kCases) {
        random_test(param);
    }
});
}  // namespace
