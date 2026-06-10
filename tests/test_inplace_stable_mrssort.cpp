#include <algorithm>
#include <random>
#include <ranges>

#include "common_test.hpp"
#include "tcs/inplace_stable_mrssort.hpp"
#include "utest.hpp"

namespace {
struct TestParam {
    int64_t size;
    int64_t max_key;
    int64_t repeat;
};

constexpr int kRandomSeed = 42;
constexpr int64_t kSweepMaxSize = 100;

constexpr TestParam kCases[] = {
    {20, 10, 10},
    {50, 20, 10},
    {100, 10, 10},
    {100, 30, 10},
    {100, 100, 10},
    {1000, 1000, 10},
    {1000, 10, 10},
    {1000, 1, 1},
};

void random_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    std::uniform_int_distribution<int64_t> key_dist(1, param.max_key);

    for ([[maybe_unused]] int64_t i : std::views::iota(0, param.repeat)) {
        auto arr = std::views::iota(0, param.size) | std::views::transform([&](int64_t i) {
            return IndexedElement{key_dist(gen), i};
        }) | std::ranges::to<TestArray>();

        auto expected = arr;
        std::ranges::stable_sort(expected, {}, IndexedElement::proj);

        tcs::inplace_stable_mrssort::inplace_stable_mrssort(
            arr.begin(), arr.end(), IndexedElement::proj);

        utest::assert_or_throw(arr.is_stable());
        utest::assert_or_throw(
            std::ranges::equal(arr, expected, {}, IndexedElement::proj, IndexedElement::proj));
    }
}

auto sweep = utest::register_test([] {
    for (int64_t n = 0; n <= kSweepMaxSize; n++) {
        utest::test("inplace_stable_mrssort", "sweep", random_test,
            TestParam{.size = n, .max_key = kSweepMaxSize, .repeat = 2});
    }
});

auto random = utest::register_test([] {
    for (const auto& param : kCases) {
        utest::test("inplace_stable_mrssort", "kCases", random_test, param);
    }
});
}  // namespace
