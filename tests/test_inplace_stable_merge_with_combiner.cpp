#include <algorithm>
#include <random>
#include <ranges>
#include <vector>

#include "common/test_array.hpp"
#include "common/utest.hpp"
#include "tcs/inplace_stable_merge_with_combiner.hpp"

namespace {
struct TestParam {
    int64_t size;
    int64_t left_size;
    int64_t max_key;
    int64_t combiner;
    int64_t repeat;
};

constexpr int64_t (*combiners[])(int64_t, int64_t) = {
    [](int64_t a, int64_t b) { return a + b ? int64_t{1} : int64_t{0}; },  // unique
    [](int64_t a, int64_t b) { return a + b; },                            // merge
    [](int64_t a, int64_t b) { return std::min(a, b); },                   // set intersection
    [](int64_t a, int64_t b) { return std::max(a, b); },                   // set union
    [](int64_t a, int64_t b) { return std::max(a - b, int64_t{0}); },      // set difference
    [](int64_t a, int64_t b) { return std::abs(a - b); },  // set symmetric difference
};

constexpr int kRandomSeed = 42;
constexpr int64_t kSweepMaxSize = 100;

constexpr TestParam kCases[] = {
    {20, 10, 10, 0, 2},
    {20, 10, 10, 1, 2},
    {20, 10, 10, 2, 2},
    {20, 10, 10, 3, 2},
    {20, 10, 10, 4, 2},
    {20, 10, 10, 5, 2},
    {50, 25, 20, 0, 2},
    {50, 25, 20, 1, 2},
    {50, 25, 20, 2, 2},
    {50, 25, 20, 3, 2},
    {50, 25, 20, 4, 2},
    {50, 25, 20, 5, 2},
    {100, 10, 10, 0, 2},
    {100, 10, 10, 1, 2},
    {100, 10, 10, 2, 2},
    {100, 10, 10, 3, 2},
    {100, 10, 10, 4, 2},
    {100, 10, 10, 5, 2},
    {100, 40, 10, 0, 2},
    {100, 40, 10, 1, 2},
    {100, 40, 10, 2, 2},
    {100, 40, 10, 3, 2},
    {100, 40, 10, 4, 2},
    {100, 40, 10, 5, 2},
    {100, 90, 10, 0, 2},
    {100, 90, 10, 1, 2},
    {100, 90, 10, 2, 2},
    {100, 90, 10, 3, 2},
    {100, 90, 10, 4, 2},
    {100, 90, 10, 5, 2},
    {100, 10, 30, 0, 2},
    {100, 10, 30, 1, 2},
    {100, 10, 30, 2, 2},
    {100, 10, 30, 3, 2},
    {100, 10, 30, 4, 2},
    {100, 10, 30, 5, 2},
    {100, 40, 30, 0, 2},
    {100, 40, 30, 1, 2},
    {100, 40, 30, 2, 2},
    {100, 40, 30, 3, 2},
    {100, 40, 30, 4, 2},
    {100, 40, 30, 5, 2},
    {100, 90, 30, 0, 2},
    {100, 90, 30, 1, 2},
    {100, 90, 30, 2, 2},
    {100, 90, 30, 3, 2},
    {100, 90, 30, 4, 2},
    {100, 90, 30, 5, 2},
    {100, 10, 100, 0, 2},
    {100, 10, 100, 1, 2},
    {100, 10, 100, 2, 2},
    {100, 10, 100, 3, 2},
    {100, 10, 100, 4, 2},
    {100, 10, 100, 5, 2},
    {100, 40, 100, 0, 2},
    {100, 40, 100, 1, 2},
    {100, 40, 100, 2, 2},
    {100, 40, 100, 3, 2},
    {100, 40, 100, 4, 2},
    {100, 40, 100, 5, 2},
    {100, 90, 100, 0, 2},
    {100, 90, 100, 1, 2},
    {100, 90, 100, 2, 2},
    {100, 90, 100, 3, 2},
    {100, 90, 100, 4, 2},
    {100, 90, 100, 5, 2},
    {1000, 500, 1000, 0, 2},
    {1000, 500, 1000, 1, 2},
    {1000, 500, 1000, 2, 2},
    {1000, 500, 1000, 3, 2},
    {1000, 500, 1000, 4, 2},
    {1000, 500, 1000, 5, 2},
    {1000, 500, 10, 0, 2},
    {1000, 500, 10, 1, 2},
    {1000, 500, 10, 2, 2},
    {1000, 500, 10, 3, 2},
    {1000, 500, 10, 4, 2},
    {1000, 500, 10, 5, 2},
    {10000, 5000, 5000, 0, 1},
    {10000, 5000, 5000, 1, 1},
    {10000, 5000, 5000, 2, 1},
    {10000, 5000, 5000, 3, 1},
    {10000, 5000, 5000, 4, 1},
    {10000, 5000, 5000, 5, 1},
    {1000, 500, 1, 0, 1},
    {1000, 500, 1, 1, 1},
    {1000, 500, 1, 2, 1},
    {1000, 500, 1, 3, 1},
    {1000, 500, 1, 4, 1},
    {1000, 500, 1, 5, 1},
    {1000, 0, 10, 0, 1},
    {1000, 0, 10, 1, 1},
    {1000, 0, 10, 2, 1},
    {1000, 0, 10, 3, 1},
    {1000, 0, 10, 4, 1},
    {1000, 0, 10, 5, 1},
    {1000, 1000, 10, 0, 1},
    {1000, 1000, 10, 1, 1},
    {1000, 1000, 10, 2, 1},
    {1000, 1000, 10, 3, 1},
    {1000, 1000, 10, 4, 1},
    {1000, 1000, 10, 5, 1},
    {1000, 0, 1, 0, 1},
    {1000, 0, 1, 1, 1},
    {1000, 0, 1, 2, 1},
    {1000, 0, 1, 3, 1},
    {1000, 0, 1, 4, 1},
    {1000, 0, 1, 5, 1},
    {1000, 1000, 1, 0, 1},
    {1000, 1000, 1, 1, 1},
    {1000, 1000, 1, 2, 1},
    {1000, 1000, 1, 3, 1},
    {1000, 1000, 1, 4, 1},
    {1000, 1000, 1, 5, 1},
};

template <typename RandomIt, typename Combiner, typename Proj>
RandomIt inplace_stable_merge_with_combiner_naive(
    RandomIt first, RandomIt mid, RandomIt last, Combiner combiner, Proj proj) {
    using T = std::iter_value_t<RandomIt>;

    std::vector<T> combined;
    std::vector<T> left_remaining;
    std::vector<T> right_remaining;

    auto left = first;
    auto right = mid;
    while (left != mid || right != last) {
        T key = (right == last || (left != mid && proj(*left) < proj(*right)) ? *left : *right);
        int64_t left_cnt =
            std::find_if(left, mid, [&](T x) { return proj(x) != proj(key); }) - left;
        int64_t right_cnt =
            std::find_if(right, last, [&](T x) { return proj(x) != proj(key); }) - right;
        int64_t take = combiner(left_cnt, right_cnt);
        for (int64_t i = 0; i < left_cnt; i++) {
            (take > 0 ? combined : left_remaining).push_back(*left);
            left++;
            take--;
        }
        for (int64_t i = 0; i < right_cnt; i++) {
            (take > 0 ? combined : right_remaining).push_back(*right);
            right++;
            take--;
        }
    }

    std::ranges::copy(combined, first);
    std::ranges::copy(left_remaining, first + combined.size());
    std::ranges::copy(right_remaining, first + combined.size() + left_remaining.size());
    return first + combined.size();
}

void random_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    std::uniform_int_distribution<int64_t> key_dist(1, param.max_key);

    for ([[maybe_unused]] auto [i, combiner] :
        std::views::cartesian_product(std::views::iota(0, param.repeat), combiners)) {
        auto arr = std::views::iota(0, param.size) | std::views::transform([&](int64_t) {
            return IndexedElement{key_dist(gen), 0};
        }) | std::ranges::to<TestArray>();
        std::ranges::sort(arr.begin(), arr.begin() + param.left_size, {}, IndexedElement::proj);
        std::ranges::sort(arr.begin() + param.left_size, arr.end(), {}, IndexedElement::proj);
        arr.iota_index();

        auto expected = arr;
        TestArray::iterator expected_result =
            inplace_stable_merge_with_combiner_naive(expected.begin(),
                expected.begin() + param.left_size, expected.end(), combiner, IndexedElement::proj);

        TestArray::iterator result =
            tcs::inplace_stable_merge_with_combiner::inplace_stable_merge_with_combiner(arr.begin(),
                arr.begin() + param.left_size, arr.end(), combiner, IndexedElement::proj);

        utest::assert_or_throw(result - arr.begin() == expected_result - expected.begin());
        utest::assert_or_throw(arr.is_stable());
        utest::assert_or_throw(arr == expected);
    }
}

auto sweep = utest::register_test([] {
    std::vector<TestParam> cases;
    for (int64_t n = 0; n <= kSweepMaxSize; n++) {
        for (int64_t combiner = 0; combiner < int64_t{std::size(combiners)}; combiner++) {
            cases.push_back({.size = n,
                .left_size = n / 2,
                .max_key = kSweepMaxSize,
                .combiner = combiner,
                .repeat = 2});
        }
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
