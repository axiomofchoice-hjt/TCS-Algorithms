#include <algorithm>
#include <random>
#include <ranges>

#include "common/test_array.hpp"
#include "tcs/inplace_stable_unpartition.hpp"
#include "utest.hpp"

namespace {
struct TestParam {
    int64_t size;
    int64_t num_ones;
    int64_t repeat;
};

constexpr int kRandomSeed = 42;
constexpr int64_t kSweepMaxSize = 100;

constexpr TestParam kCases[] = {
    {20, 10, 10},
    {50, 20, 10},
    {100, 10, 10},
    {100, 30, 10},
    {100, 70, 10},
    {1000, 10, 10},
    {1000, 100, 10},
    {1000, 300, 10},
    {1000, 700, 10},
    {10000, 5000, 1},
    {100, 0, 1},      // all zeros
    {100, 1, 1},      // single one
    {100, 99, 1},     // single zero
    {100, 100, 1},    // all ones
    {1000, 0, 1},     // all zeros (large)
    {1000, 1, 1},     // single one (large)
    {1000, 999, 1},   // single zero (large)
    {1000, 1000, 1},  // all ones (large)
};

void random_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    int64_t n = param.size;
    int64_t num_ones = param.num_ones;

    for ([[maybe_unused]] int64_t i : std::views::iota(0, param.repeat)) {
        TestArray arr(n);
        std::vector<bool> placement(n);

        for (int64_t i = 0; i < n; i++) {
            arr[i] = {i < num_ones ? 1 : 0, 0};
        }
        std::ranges::shuffle(arr, gen);
        arr.iota_index();
        for (auto [i, el] : arr | std::views::enumerate) {
            placement[i] = el.key != 0;
        }

        auto expected = arr;
        std::ranges::stable_sort(arr.begin(), arr.end(), {}, IndexedElement::proj);

        tcs::inplace_stable_unpartition::inplace_stable_unpartition(
            arr.begin(), arr.end(), [](IndexedElement e) { return IndexedElement::proj(e) == 0; },
            [&arr, &placement](auto p) { return !placement[p - arr.begin()]; });

        utest::assert_or_throw(arr.is_stable());
        utest::assert_or_throw(arr == expected);
    }
}

auto sweep = utest::register_test([] {
    for (int64_t n = 0; n <= kSweepMaxSize; n++) {
        utest::test("inplace_stable_unpartition", "sweep", random_test,
            TestParam{.size = n, .num_ones = n / 2, .repeat = 2});
    }
});

auto random = utest::register_test([] {
    for (const auto& param : kCases) {
        utest::test("inplace_stable_unpartition", "kCases", random_test, param);
    }
});
}  // namespace
