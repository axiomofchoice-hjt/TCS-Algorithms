
#include <algorithm>
#include <random>
#include <vector>

#include "common/test_array.hpp"
#include "common/utest.hpp"
#include "tcs/inplace_stable_unique.hpp"

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
    {10000, 5000, 1},
    {10000, 100, 1},
    {1000, 1, 1},
};

void random_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    std::uniform_int_distribution<int64_t> key_dist(1, param.max_key);

    for ([[maybe_unused]] int64_t i : std::views::iota(0, param.repeat)) {
        auto arr = std::views::iota(0, param.size) | std::views::transform([&](int64_t) {
            return IndexedElement{key_dist(gen), 0};
        }) | std::ranges::to<TestArray>();
        std::ranges::sort(arr, {}, IndexedElement::proj);
        arr.iota_index();

        auto expected = arr;
        std::optional<IndexedElement> pre;
        TestArray::iterator mid = expected.begin();
        for (TestArray::iterator it = expected.begin(); it < expected.end(); it++) {
            if (!pre || IndexedElement::proj(*pre) != IndexedElement::proj(*it)) {
                pre = *it;
                std::swap(*mid, *it);
                mid++;
            }
        }
        std::ranges::sort(mid, expected.end(), {}, IndexedElement::proj);

        tcs::inplace_stable_unique::inplace_stable_unique(
            arr.begin(), arr.end(), IndexedElement::proj);

        utest::assert_or_throw(arr.is_stable());
        utest::assert_or_throw(arr == expected);
    }
}

auto sweep = utest::register_test([] {
    std::vector<TestParam> cases;
    for (int64_t n = 0; n <= kSweepMaxSize; n++) {
        cases.push_back({.size = n, .max_key = kSweepMaxSize, .repeat = 2});
    }
    for (const auto& param : cases) {
        utest::test("inplace_stable_unique", "sweep", random_test, param);
    }
});

auto random = utest::register_test([] {
    for (const auto& param : kCases) {
        utest::test("inplace_stable_unique", "kCases", random_test, param);
    }
});
}  // namespace
