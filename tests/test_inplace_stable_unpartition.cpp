#include <algorithm>
#include <catch2/catch_test_macros.hpp>
#include <catch2/generators/catch_generators_range.hpp>
#include <random>
#include <ranges>
#include <vector>

#include "tcs/inplace_stable_unpartition.hpp"

namespace {
struct Element {
    int64_t key;
    int64_t index;
};

struct TestParam {
    int64_t total_size;
    int64_t num_ones;
    int64_t repeat_count;
};

constexpr int kRandomSeed = 42;
constexpr int64_t kSweepMaxSize = 1000;

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
    {10000, 5000, 2},
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
    static std::mt19937 gen(kRandomSeed);
    int64_t n = param.total_size;
    int64_t num_ones = param.num_ones;

    for ([[maybe_unused]] int64_t i : std::views::iota(0, param.repeat_count)) {
        std::vector<Element> arr(n);
        std::vector<bool> placement(n);

        for (int64_t i = 0; i < n; i++) {
            arr[i] = {i < num_ones ? 1 : 0, 0};
        }
        std::shuffle(arr.begin(), arr.end(), gen);
        for (auto [i, el] : arr | std::views::enumerate) {
            el.index = static_cast<int64_t>(i);
            placement[i] = el.key != 0;
        }

        auto expected = arr;
        std::stable_sort(arr.begin(), arr.end(), [](Element a, Element b) { return a.key < b.key; });

        try {
            tcs::inplace_stable_unpartition::inplace_stable_unpartition(
                arr.data(), arr.data() + n, [](Element e) { return e.key == 0; },
                [&arr, &placement](Element* p) { return !placement[p - arr.data()]; });
        } catch (std::exception& e) {
            INFO(std::format("{} [total_size={}, num_ones={}, repeat_count={}]", e.what(), param.total_size,
                param.num_ones, param.repeat_count));
            FAIL();
        }

        REQUIRE(std::ranges::all_of(std::ranges::views::zip(arr, expected), [](auto&& zip) {
            auto [result, expected] = zip;
            return std::pair{result.key, result.index} == std::pair{expected.key, expected.index};
        }));
    }
}
}  // namespace

TEST_CASE("inplace_stable_unpartition size sweep", "[inplace_stable_unpartition]") {
    auto n = GENERATE(Catch::Generators::range(int64_t{0}, kSweepMaxSize + 1));
    random_test({.total_size = n, .num_ones = n / 2, .repeat_count = 2});
}

TEST_CASE("inplace_stable_unpartition random tests", "[inplace_stable_unpartition]") {
    for (const auto& param : kCases) {
        random_test(param);
    }
}
