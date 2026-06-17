#include "common/test_array.hpp"
#include "common/test_sort.hpp"
#include "common/utest.hpp"
#include "tcs/inplace_stable_cyclesort.hpp"

namespace {
constexpr int kRandomSeed = 42;
constexpr int64_t kSweepMaxSize = 100;

constexpr TestSortParam kCases[] = {
    {20, 10, 10},
    {50, 20, 10},
    {100, 10, 10},
    {100, 30, 10},
    {100, 100, 10},
    {1000, 1000, 10},
    {1000, 10, 10},
    {1000, 1, 1},
};

auto random_test = gen_random_sort_test(
    [](TestArray& arr) {
        tcs::inplace_stable_cyclesort::inplace_stable_cyclesort(
            arr.begin(), arr.end(), IndexedElement::proj);
    },
    true, kRandomSeed);

auto sweep = utest::register_test([] {
    std::vector<TestSortParam> cases;
    for (int64_t n = 0; n <= kSweepMaxSize; n++) {
        cases.push_back(TestSortParam{.size = n, .max_key = kSweepMaxSize, .repeat = 2});
    }
    for (const auto& param : cases) {
        utest::test("inplace_stable_cyclesort", "sweep", random_test, param);
    }
});

auto random_cases = utest::register_test([] {
    for (const auto& param : kCases) {
        utest::test("inplace_stable_cyclesort", "kCases", random_test, param);
    }
});
}  // namespace
