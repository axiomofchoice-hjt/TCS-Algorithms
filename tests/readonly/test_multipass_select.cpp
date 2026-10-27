#include <algorithm>
#include <cstdint>
#include <forward_list>
#include <random>
#include <utility>
#include <vector>

#include "common/indexed_element.hpp"
#include "common/utest.hpp"
#include "tcs/readonly/multipass_select.hpp"

namespace {
constexpr int kRandomSeed = 42;
constexpr int64_t kSweepMaxSize = 100;
constexpr int64_t kMinWorkspace = 8;

struct TestParam {
    int64_t size;
    int64_t k;
    int64_t max_key;
    int64_t repeat;
};

// `multipass_select` now takes its workspace as a cell count instead of a
// caller-provided buffer range. Half the input keeps the first pass in
// sampling mode (population > workspace), which is what makes the algorithm
// multi-pass, while the floor keeps tiny inputs on the single-pass branch (and
// avoids `ceil_log2(size) == 0` for size == 1).
int64_t make_workspace(int64_t size) { return std::max(size / 2, kMinWorkspace); }

std::vector<IndexedElement> make_input(int64_t size, int64_t max_key, std::mt19937& gen) {
    // The paper's model assumes N *distinct* elements, so sample `size` distinct
    // keys from [1, max_key]; this requires max_key >= size.
    utest::assert_or_throw(
        max_key >= size, "make_input: max_key must be >= size for distinct keys");
    std::vector<int64_t> keys(max_key);
    for (int64_t v = 0; v < max_key; v++) {
        keys[v] = v + 1;
    }
    std::shuffle(keys.begin(), keys.end(), gen);
    std::vector<IndexedElement> arr(size);
    for (int64_t i = 0; i < size; i++) {
        arr[i] = {keys[i], i};
    }
    return arr;
}

// Runs the algorithm on `arr` viewed through const iterators (read-only input)
// and checks that it returns the k-th smallest key, that the input array is
// left untouched, and that the result is a copy of an actual input element.
void run_checked(const std::vector<IndexedElement>& arr, int64_t k) {
    auto expected = arr;
    std::ranges::sort(expected, {}, IndexedElement::proj);
    const int64_t expected_key = IndexedElement::proj(expected[k]);

    auto snapshot = arr;
    const auto& carr = arr;  // const vector -> const_iterator (forward, read-only)
    auto result = tcs::readonly::multipass_select::multipass_select(carr.begin(),
        static_cast<int64_t>(arr.size()), k, make_workspace(static_cast<int64_t>(arr.size())),
        IndexedElement::proj);

    utest::assert_or_throw(IndexedElement::proj(result) == expected_key);
    auto key_and_index = [](const IndexedElement& el) { return std::pair(el.key, el.index); };
    utest::assert_or_throw(std::ranges::equal(arr, snapshot, {}, key_and_index, key_and_index));
    utest::assert_or_throw(result.index >= 0 && result.index < static_cast<int64_t>(arr.size()));
}

void random_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    for (int64_t i = 0; i < param.repeat; i++) {
        run_checked(make_input(param.size, param.max_key, gen), param.k);
    }
}

// A true forward-only const iterator: std::forward_list::const_iterator is not
// random-access, which is the weakest iterator category the algorithm promises.
void forward_list_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    std::vector<int64_t> keys(param.max_key);
    for (int64_t v = 0; v < param.max_key; v++) {
        keys[v] = v + 1;
    }
    std::shuffle(keys.begin(), keys.end(), gen);
    std::forward_list<IndexedElement> list;
    std::vector<IndexedElement> expected;
    for (int64_t i = 0; i < param.size; i++) {
        IndexedElement el{keys[i], i};
        list.push_front(el);
        expected.push_back(el);
    }
    std::ranges::sort(expected, {}, IndexedElement::proj);

    auto result = tcs::readonly::multipass_select::multipass_select(
        list.cbegin(), param.size, param.k, make_workspace(param.size), IndexedElement::proj);
    utest::assert_or_throw(IndexedElement::proj(result) == IndexedElement::proj(expected[param.k]));
}

constexpr TestParam kCases[] = {
    {20, 10, 20, 10},
    {100, 10, 100, 10},
    {100, 40, 100, 10},
    {100, 90, 100, 10},
    {100, 10, 1000, 10},  // large key range, still distinct
    {100, 40, 500, 10},
    {100, 90, 100, 10},
    {1000, 500, 1000, 10},
    {1000, 500, 7000, 10},  // large key range
    {10000, 5000, 10000, 1},
    {100000, 50000, 200000, 1},
    {1000, 500, 1000, 1},
    {1000, 0, 1000, 1},    // k = 0 (minimum)
    {1000, 999, 1000, 1},  // k = n-1 (maximum)
    {1000, 0, 5000, 1},    // k = 0, large key range
    {1000, 999, 1000, 1},  // k = n-1
};

auto sweep = utest::register_test([] {
    std::vector<TestParam> cases;
    for (int64_t n = 1; n <= kSweepMaxSize; n++) {
        cases.push_back({.size = n, .k = n / 2, .max_key = kSweepMaxSize, .repeat = 2});
        cases.push_back({.size = n, .k = 0, .max_key = kSweepMaxSize, .repeat = 1});
        cases.push_back({.size = n, .k = n - 1, .max_key = kSweepMaxSize, .repeat = 1});
    }
    for (const auto& param : cases) {
        utest::test("multipass_select", "sweep", random_test, param);
    }
});

auto random = utest::register_test([] {
    for (const auto& param : kCases) {
        utest::test("multipass_select", "kCases", random_test, param);
    }
});

auto forward_list = utest::register_test([] {
    for (int64_t n : {1, 2, 3, 7, 16, 64, 100}) {
        utest::test("multipass_select", "forward_list", forward_list_test,
            TestParam{.size = n, .k = n / 2, .max_key = 100, .repeat = 1});
    }
});
}  // namespace
