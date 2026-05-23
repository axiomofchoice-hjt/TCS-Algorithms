#include <algorithm>
#include <catch2/catch_test_macros.hpp>
#include <catch2/generators/catch_generators_range.hpp>
#include <random>
#include <ranges>
#include <vector>

#include "tcs/inplace_unstable_select.hpp"

namespace {
struct TestParam {
    int64_t total_size;
    int64_t k;
    int64_t max_key;
    int64_t repeat_count;
};

constexpr int kRandomSeed = 42;
constexpr int64_t kSweepMaxSize = 1000;

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
    {100000, 50000, 50000, 2},
    {1000, 500, 1, 1},     // all elements share the same key
    {1000, 0, 1000, 1},    // k = 0 (minimum)
    {1000, 999, 1000, 1},  // k = n-1 (maximum)
    {1000, 0, 1, 1},       // k = 0, single key
    {1000, 999, 1, 1},     // k = n-1, single key
};

void random_test(const TestParam& param) {
    static std::mt19937 gen(kRandomSeed);
    std::uniform_int_distribution<int64_t> key_dist(1, param.max_key);

    for (int64_t i : std::views::iota(0, param.repeat_count)) {
        auto arr = std::views::iota(0, param.total_size) |
                   std::views::transform([&](int64_t) { return key_dist(gen); }) |
                   std::ranges::to<std::vector<int64_t>>();

        auto expected = arr;
        std::ranges::sort(expected);

        try {
            tcs::inplace_unstable_select::inplace_unstable_select(
                arr.data(), arr.data() + param.k, arr.data() + param.total_size);
        } catch (std::exception& e) {
            INFO(std::format("{} [total_size={}, k={}, max_key={}, repeat_count={}]", e.what(), param.total_size,
                param.k, param.max_key, param.repeat_count));
            FAIL();
        }

        int64_t pivot = arr[param.k];
        REQUIRE(pivot == expected[param.k]);
        REQUIRE(std::ranges::all_of(arr | std::views::take(param.k), [pivot](int64_t x) { return x <= pivot; }));
        REQUIRE(std::ranges::all_of(arr | std::views::drop(param.k + 1), [pivot](int64_t x) { return x >= pivot; }));
        std::ranges::sort(arr);
        REQUIRE(arr == expected);
    }
}
}  // namespace

TEST_CASE("inplace_unstable_select size sweep", "[inplace_unstable_select]") {
    auto n = GENERATE(Catch::Generators::range(int64_t{1}, kSweepMaxSize + 1));
    random_test({.total_size = n, .k = n / 2, .max_key = kSweepMaxSize, .repeat_count = 2});
    random_test({.total_size = n, .k = 0, .max_key = kSweepMaxSize, .repeat_count = 2});
    random_test({.total_size = n, .k = n - 1, .max_key = kSweepMaxSize, .repeat_count = 2});
}

TEST_CASE("inplace_unstable_select random tests", "[inplace_unstable_select]") {
    for (const auto& param : kCases) {
        random_test(param);
    }
}
