#include <algorithm>
#include <random>
#include <ranges>
#include <vector>

#include "common_test.hpp"
#include "tcs/inplace_unstable_merge.hpp"
#include "utest.hpp"

namespace {
struct TestParam {
    int64_t total_size;
    int64_t left_size;
    int64_t max_key;
    int64_t repeat_count;
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

    for ([[maybe_unused]] int64_t i : std::views::iota(0, param.repeat_count)) {
        auto arr = std::views::iota(0, param.total_size) | std::views::transform([&](int64_t) {
            return IndexedElement{key_dist(gen), 0};
        }) | std::ranges::to<std::vector<IndexedElement>>();

        std::ranges::sort(arr.begin(), arr.begin() + param.left_size, {}, IndexedElement::proj);
        std::ranges::sort(arr.begin() + param.left_size, arr.end(), {}, IndexedElement::proj);

        auto expected = arr;
        std::ranges::inplace_merge(
            expected, expected.begin() + param.left_size, {}, IndexedElement::proj);

        tcs::inplace_unstable_merge::inplace_unstable_merge(
            arr.begin(), arr.begin() + param.left_size, arr.end(), IndexedElement::proj);

        utest::assert_or_throw(
            std::ranges::equal(arr, expected, {}, IndexedElement::proj, IndexedElement::proj));
    }
}

auto sweep = utest::test("inplace_unstable_merge size sweep", "[inplace_unstable_merge]", [] {
    for (int64_t n = 0; n <= kSweepMaxSize; n++) {
        random_test(
            {.total_size = n, .left_size = n / 2, .max_key = kSweepMaxSize, .repeat_count = 2});
    }
});

auto random = utest::test("inplace_unstable_merge random tests", "[inplace_unstable_merge]", [] {
    for (const auto& param : kCases) {
        random_test(param);
    }
});
}  // namespace
