#include <algorithm>
#include <catch2/catch_test_macros.hpp>
#include <catch2/generators/catch_generators_range.hpp>
#include <random>
#include <ranges>
#include <vector>

#include "common_test.hpp"
#include "tcs/inplace_stable_quicksort.hpp"

namespace {
struct TestParam {
    int64_t total_size;
    int64_t max_key;
    int64_t repeat_count;
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
    {10000, 5000, 1},
    {1000, 1, 1},
};

void random_test(const TestParam& param) {
    std::mt19937 gen(kRandomSeed);
    std::uniform_int_distribution<int64_t> key_dist(1, param.max_key);

    for ([[maybe_unused]] int64_t i : std::views::iota(0, param.repeat_count)) {
        auto arr = std::views::iota(0, param.total_size) | std::views::transform([&](int64_t i) {
            return IndexedElement{key_dist(gen), i};
        }) | std::ranges::to<std::vector<IndexedElement>>();

        auto expected = arr;
        std::ranges::stable_sort(expected, {}, IndexedElement::proj);

        try {
            tcs::inplace_stable_qsort::inplace_stable_quicksort(
                arr.begin(), arr.end(), IndexedElement::proj);
        } catch (std::exception& e) {
            INFO(std::format("{} [total_size={}, max_key={}, repeat_count={}]", e.what(),
                param.total_size, param.max_key, param.repeat_count));
            FAIL();
        }

        REQUIRE(is_stable(arr));
        REQUIRE(std::ranges::equal(
            arr, expected, {}, IndexedElement::proj, IndexedElement::proj));
    }
}
}  // namespace

TEST_CASE("inplace_stable_quicksort size sweep", "[inplace_stable_quicksort]") {
    auto n = GENERATE(Catch::Generators::range(int64_t{0}, kSweepMaxSize + 1));
    random_test({.total_size = n, .max_key = kSweepMaxSize, .repeat_count = 2});
}

TEST_CASE("inplace_stable_quicksort random tests", "[inplace_stable_quicksort]") {
    for (const auto& param : kCases) {
        random_test(param);
    }
}
