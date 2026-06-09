#include <algorithm>
#include <random>
#include <ranges>
#include <vector>

#include "common_test.hpp"
#include "tcs/inplace_stable_select.hpp"
#include "utest.hpp"

namespace {

struct TestParam {
    int64_t size;
    int64_t k;
    int64_t max_key;
    int64_t repeat;
};

constexpr int kRandomSeed = 42;
constexpr int64_t kSweepMaxSize = 100;

constexpr TestParam kCases[] = {
    {20, 10, 10, 10},
    {50, 25, 20, 10},
    {100, 10, 10, 10},
    {100, 40, 10, 10},
    {100, 90, 10, 10},
    {100, 10, 30, 10},
    {100, 40, 30, 10},
    {100, 90, 30, 10},
    {100, 10, 100, 10},
    {100, 40, 100, 10},
    {100, 90, 100, 10},
    {1000, 500, 1000, 10},
    {1000, 500, 10, 10},
    {10000, 5000, 5000, 2},
    {100000, 50000, 50000, 1},
    {1000, 500, 1, 1},     // all elements share the same key
    {1000, 0, 1000, 1},    // k = 0 (minimum)
    {1000, 999, 1000, 1},  // k = n-1 (maximum)
    {1000, 0, 1, 1},       // k = 0, single key
    {1000, 999, 1, 1},     // k = n-1, single key
};

void random_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    std::uniform_int_distribution<int64_t> key_dist(1, param.max_key);

    for ([[maybe_unused]] int64_t i : std::views::iota(0, param.repeat)) {
        auto arr = std::views::iota(0, param.size) | std::views::transform([&](int64_t i) {
            return IndexedElement{key_dist(gen), i};
        }) | std::ranges::to<std::vector<IndexedElement>>();

        auto expected = arr;
        std::ranges::stable_sort(expected, {}, IndexedElement::proj);

        tcs::inplace_stable_select::inplace_stable_select(
            arr.begin(), arr.begin() + param.k, arr.end(), IndexedElement::proj);

        utest::assert_or_throw(
            IndexedElement::proj(arr[param.k]) == IndexedElement::proj(expected[param.k]));
        utest::assert_or_throw(is_stable(arr));
        std::ranges::sort(arr, {}, IndexedElement::proj);
        utest::assert_or_throw(
            std::ranges::equal(arr, expected, {}, IndexedElement::proj, IndexedElement::proj));
    }
}

auto sweep = utest::register_test([] {
    for (int64_t n = 1; n <= kSweepMaxSize; n++) {
        utest::test("inplace_stable_select", "sweep", random_test,
            TestParam{.size = n, .k = n / 2, .max_key = kSweepMaxSize, .repeat = 2});
        utest::test("inplace_stable_select", "sweep", random_test,
            TestParam{.size = n, .k = 0, .max_key = kSweepMaxSize, .repeat = 1});
        utest::test("inplace_stable_select", "sweep", random_test,
            TestParam{.size = n, .k = n - 1, .max_key = kSweepMaxSize, .repeat = 1});
    }
});

auto random = utest::register_test([] {
    for (const auto& param : kCases) {
        utest::test("inplace_stable_select", "kCases", random_test, param);
    }
});
}  // namespace
