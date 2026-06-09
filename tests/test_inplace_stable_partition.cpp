#include <algorithm>
#include <random>
#include <vector>

#include "common_test.hpp"
#include "tcs/inplace_stable_partition.hpp"
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
    {20, 10, 20},
    {50, 20, 20},
    {100, 10, 20},
    {100, 30, 20},
    {100, 70, 20},
    {1000, 10, 20},
    {1000, 100, 20},
    {1000, 300, 20},
    {1000, 700, 20},
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

void random_test(const TestParam& param) {
    std::mt19937 gen(kRandomSeed);
    int64_t n = param.size;
    int64_t num_ones = param.num_ones;

    for (int64_t i = 0; i < param.repeat; i++) {
        std::vector<IndexedElement> arr(n);

        for (int64_t i = 0; i < n; i++) {
            arr[i] = {i < num_ones ? 1 : 0, 0};
        }

        std::ranges::shuffle(arr, gen);
        iota_index(arr);

        auto expected = arr;
        std::stable_partition(expected.begin(), expected.end(),
            [](IndexedElement e) { return IndexedElement::proj(e) == 0; });

        tcs::inplace_stable_partition::inplace_stable_partition(
            arr.begin(), arr.end(), [](IndexedElement e) { return IndexedElement::proj(e) == 0; });

        utest::assert_or_throw(is_stable(arr));
        utest::assert_or_throw(
            std::ranges::equal(arr, expected, {}, IndexedElement::proj, IndexedElement::proj));
    }
}

auto sweep = utest::test("inplace_stable_partition", "[inplace_stable_partition]", [] {
    for (int64_t n = 0; n <= kSweepMaxSize; n++) {
        random_test({.size = n, .num_ones = n / 2, .repeat = 2});
    }
});

auto random =
    utest::test("inplace_stable_partition", "[inplace_stable_partition]", [] {
        for (const auto& param : kCases) {
            random_test(param);
        }
    });
}  // namespace
