#include <algorithm>
#include <random>
#include <ranges>
#include <vector>

#include "common/test_array.hpp"
#include "common/utest.hpp"
#include "tcs/bfprt.hpp"

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
    {1000, 500, 1, 1},     // all elements share the same key
    {1000, 0, 1000, 1},    // k = 0 (minimum)
    {1000, 999, 1000, 1},  // k = n-1 (maximum)
    {1000, 0, 1, 1},       // k = 0, single key
    {1000, 999, 1, 1},     // k = n-1, single key
};

void random_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    std::uniform_int_distribution<int64_t> key_dist(1, param.max_key);

    for (int64_t i = 0; i < param.repeat; i++) {
        auto arr = std::views::iota(0, param.size) | std::views::transform([&](int64_t) {
            return IndexedElement{key_dist(gen), 0};
        }) | std::ranges::to<TestArray>();

        auto expected = arr;
        std::ranges::sort(expected, {}, IndexedElement::proj);

        tcs::bfprt::bfprt(arr.begin(), arr.begin() + param.k, arr.end(), IndexedElement::proj);

        utest::assert_or_throw(
            IndexedElement::proj(arr[param.k]) == IndexedElement::proj(expected[param.k]));
        std::ranges::sort(arr, {}, IndexedElement::proj);
        utest::assert_or_throw(arr == expected);
    }
}

auto sweep = utest::register_test([] {
    std::vector<TestParam> cases;
    for (int64_t n = 1; n <= kSweepMaxSize; n++) {
        cases.push_back({.size = n, .k = n / 2, .max_key = kSweepMaxSize, .repeat = 2});
        cases.push_back({.size = n, .k = 0, .max_key = kSweepMaxSize, .repeat = 1});
        cases.push_back({.size = n, .k = n - 1, .max_key = kSweepMaxSize, .repeat = 1});
    }
    for (const auto& param : cases) {
        utest::test("bfprt", "sweep", random_test, param);
    }
});

auto random = utest::register_test([] {
    for (const auto& param : kCases) {
        utest::test("bfprt", "kCases", random_test, param);
    }
});
}  // namespace
