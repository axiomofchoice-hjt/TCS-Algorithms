#include <algorithm>
#include <cstdint>
#include <forward_list>
#include <random>
#include <utility>
#include <vector>

#include "common/indexed_element.hpp"
#include "common/utest.hpp"
#include "tcs/readonly/onepass_median.hpp"

namespace {
constexpr int kRandomSeed = 42;
constexpr int64_t kSweepMaxSize = 100;
constexpr int64_t kForwardListMaxKey = 10;

struct TestParam {
    int64_t size;
    int64_t max_key;
    int64_t repeat;
};

// The algorithm requires a workspace of exactly size/2 + 2 cells.
constexpr int64_t kBufferSlack = 2;

int64_t buffer_size(int64_t n) { return (n / 2) + kBufferSlack; }

std::vector<IndexedElement> make_input(int64_t size, int64_t max_key, std::mt19937& gen) {
    std::uniform_int_distribution<int64_t> key_dist(1, max_key);
    std::vector<IndexedElement> arr(size);
    for (int64_t i = 0; i < size; i++) {
        arr[i] = {key_dist(gen), i};
    }
    return arr;
}

// Runs onepass_median on `arr` through const iterators (read-only input) with
// a size/2 + 2 workspace and checks that the returned lower/upper median pair
// has the expected keys, that the input array is left untouched, and that both
// results are copies of actual input elements.
void run_checked(const std::vector<IndexedElement>& arr) {
    auto expected = arr;
    std::ranges::sort(expected, {}, IndexedElement::proj);
    const int64_t n = static_cast<int64_t>(arr.size());
    const int64_t lo_key = IndexedElement::proj(expected[(n - 1) / 2]);
    const int64_t hi_key = IndexedElement::proj(expected[n / 2]);

    auto snapshot = arr;
    std::vector<IndexedElement> buffer(static_cast<size_t>(buffer_size(n)));
    const auto& carr = arr;  // const vector -> const_iterator (forward, read-only)
    auto result = tcs::readonly::onepass_median::onepass_median(
        carr.begin(), n, buffer.begin(), buffer.end(), IndexedElement::proj);

    utest::assert_or_throw(IndexedElement::proj(result[0]) == lo_key);
    utest::assert_or_throw(IndexedElement::proj(result[1]) == hi_key);
    auto key_and_index = [](const IndexedElement& el) { return std::pair(el.key, el.index); };
    utest::assert_or_throw(std::ranges::equal(arr, snapshot, {}, key_and_index, key_and_index));
    utest::assert_or_throw(result[0].index >= 0 && result[0].index < n);
    utest::assert_or_throw(result[1].index >= 0 && result[1].index < n);
}

void random_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    for (int64_t i = 0; i < param.repeat; i++) {
        run_checked(make_input(param.size, param.max_key, gen));
    }
}

// Keys drawn from a symmetric range including negatives.
void signed_key_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    std::uniform_int_distribution<int64_t> key_dist(-param.max_key, param.max_key);
    for (int64_t i = 0; i < param.repeat; i++) {
        std::vector<IndexedElement> arr(param.size);
        for (int64_t j = 0; j < param.size; j++) {
            arr[j] = {key_dist(gen), j};
        }
        run_checked(arr);
    }
}

// A true forward-only const iterator: std::forward_list::const_iterator is not
// random-access, which is the weakest iterator category the algorithm promises.
void forward_list_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    std::uniform_int_distribution<int64_t> key_dist(1, param.max_key);
    std::forward_list<IndexedElement> list;
    std::vector<IndexedElement> expected;
    for (int64_t i = 0; i < param.size; i++) {
        IndexedElement el{key_dist(gen), i};
        list.push_front(el);
        expected.push_back(el);
    }
    std::ranges::sort(expected, {}, IndexedElement::proj);
    const int64_t n = param.size;
    const int64_t lo_key = IndexedElement::proj(expected[(n - 1) / 2]);
    const int64_t hi_key = IndexedElement::proj(expected[n / 2]);

    std::vector<IndexedElement> buffer(static_cast<size_t>(buffer_size(n)));
    auto result = tcs::readonly::onepass_median::onepass_median(
        list.cbegin(), n, buffer.begin(), buffer.end(), IndexedElement::proj);
    utest::assert_or_throw(IndexedElement::proj(result[0]) == lo_key);
    utest::assert_or_throw(IndexedElement::proj(result[1]) == hi_key);
}

constexpr TestParam kCases[] = {
    {1, 10, 10},  // single element
    {2, 10, 10},  // two elements
    {3, 10, 10},
    {20, 10, 10},
    {100, 10, 10},
    {100, 100, 10},
    {1000, 1000, 10},
    {10000, 5000, 1},
    {100000, 50000, 1},
    {1000, 1, 1},  // all elements share the same key
};

constexpr TestParam kSignedCases[] = {
    {1, 10, 10},
    {2, 10, 10},
    {7, 10, 5},
    {100, 100, 5},
};

auto sweep = utest::register_test([] {
    std::vector<TestParam> cases;
    for (int64_t n = 1; n <= kSweepMaxSize; n++) {
        cases.push_back({.size = n, .max_key = kSweepMaxSize, .repeat = 2});
    }
    for (const auto& param : cases) {
        utest::test("onepass_median", "sweep", random_test, param);
    }
});

auto random = utest::register_test([] {
    for (const auto& param : kCases) {
        utest::test("onepass_median", "kCases", random_test, param);
    }
});

auto signed_keys = utest::register_test([] {
    for (const auto& param : kSignedCases) {
        utest::test("onepass_median", "signed_keys", signed_key_test, param);
    }
});

auto forward_list = utest::register_test([] {
    for (int64_t n : {1, 2, 3, 7, 16, 64, 100}) {
        utest::test("onepass_median", "forward_list", forward_list_test,
            TestParam{.size = n, .max_key = kForwardListMaxKey, .repeat = 1});
    }
});
}  // namespace
