#include <algorithm>
#include <cstdint>
#include <random>
#include <stdexcept>
#include <vector>

#include "common/indexed_element.hpp"
#include "common/utest.hpp"
#include "tcs/readonly/constant_space_select.hpp"

namespace {
struct TestParam {
    int64_t size;
    int64_t k;
    int64_t max_key;
    int64_t n_layers;
    int64_t repeat;
};

constexpr int kRandomSeed = 42;
constexpr int64_t kSweepMaxSize = 64;

// select orders by (proj(element), iterator-position), which is stable: for a
// vector whose index field equals its position, the expected k-th element is
// the k-th entry after stable_sorting by key.
std::vector<IndexedElement> make_input(int64_t size, int64_t max_key, std::mt19937& gen) {
    std::uniform_int_distribution<int64_t> key_dist(1, max_key);
    std::vector<IndexedElement> arr(size);
    for (int64_t i = 0; i < size; i++) {
        arr[i] = {key_dist(gen), i};
    }
    return arr;
}

std::vector<IndexedElement> make_signed_input(int64_t size, int64_t max_key, std::mt19937& gen) {
    std::uniform_int_distribution<int64_t> key_dist(-max_key, max_key);
    std::vector<IndexedElement> arr(size);
    for (int64_t i = 0; i < size; i++) {
        arr[i] = {key_dist(gen), i};
    }
    return arr;
}

// Runs select on `arr` through const iterators (read-only input) and checks
// that the returned element is the correctly ordered k-th element and that the
// input is left untouched.
void run_checked(const std::vector<IndexedElement>& arr, int64_t k, int64_t n_layers) {
    auto expected = arr;
    std::ranges::stable_sort(expected, {}, IndexedElement::proj);
    const int64_t n = static_cast<int64_t>(arr.size());
    utest::assert_or_throw(k >= 0 && k < n);

    auto snapshot = arr;
    const auto& carr = arr;  // const vector -> const_iterator (read-only)
    auto result = tcs::readonly::constant_space_select::constant_space_select(
        carr.cbegin(), carr.cend(), k, n_layers, IndexedElement::proj);

    utest::assert_or_throw(result >= carr.cbegin() && result < carr.cend());
    utest::assert_or_throw(IndexedElement::proj(*result) == IndexedElement::proj(expected[k]));
    utest::assert_or_throw(result->index == expected[k].index);
    auto key_and_index = [](const IndexedElement& el) { return std::pair(el.key, el.index); };
    utest::assert_or_throw(std::ranges::equal(arr, snapshot, {}, key_and_index, key_and_index));
}

void random_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    for (int64_t i = 0; i < param.repeat; i++) {
        run_checked(make_input(param.size, param.max_key, gen), param.k, param.n_layers);
    }
}

// Keys drawn from a symmetric range including negatives.
void signed_key_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    for (int64_t i = 0; i < param.repeat; i++) {
        run_checked(make_signed_input(param.size, param.max_key, gen), param.k, param.n_layers);
    }
}

// Every element shares the same key: verifies the index tie-break order.
void duplicate_key_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    for (int64_t i = 0; i < param.repeat; i++) {
        auto arr = make_input(param.size, 1, gen);  // max_key = 1 -> all keys equal
        run_checked(arr, param.k, param.n_layers);
    }
}

// select with the default projection (std::identity) over a plain integer
// range, which is the most common calling convention.
void identity_proj_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    std::uniform_int_distribution<int64_t> key_dist(1, param.max_key);
    for (int64_t i = 0; i < param.repeat; i++) {
        std::vector<int64_t> arr(param.size);
        for (int64_t& v : arr) {
            v = key_dist(gen);
        }
        auto expected = arr;
        std::ranges::stable_sort(expected);

        auto snapshot = arr;
        const auto& carr = arr;
        auto result = tcs::readonly::constant_space_select::constant_space_select(
            carr.cbegin(), carr.cend(), param.k, param.n_layers);
        utest::assert_or_throw(*result == expected[param.k]);
        utest::assert_or_throw(std::ranges::equal(arr, snapshot));
    }
}

// Invalid preconditions must be rejected with a std::runtime_error.
void invalid_input_throws([[maybe_unused]] int64_t unused) {
    std::vector<int64_t> arr{3, 1, 2};

    // n_layers must be positive.
    bool threw = false;
    try {
        (void)tcs::readonly::constant_space_select::constant_space_select(
            arr.begin(), arr.end(), 0, 0);
    } catch (const std::runtime_error&) {
        threw = true;
    }
    utest::assert_or_throw(threw);

    // k must be within [0, size).
    threw = false;
    try {
        (void)tcs::readonly::constant_space_select::constant_space_select(
            arr.begin(), arr.end(), 3, 1);
    } catch (const std::runtime_error&) {
        threw = true;
    }
    utest::assert_or_throw(threw);

    threw = false;
    try {
        (void)tcs::readonly::constant_space_select::constant_space_select(
            arr.begin(), arr.end(), -1, 1);
    } catch (const std::runtime_error&) {
        threw = true;
    }
    utest::assert_or_throw(threw);
}

// Sweep small sizes for every supported layer count, exercising the min / mid /
// max positions.
auto sweep = utest::register_test([] {
    for (int64_t n_layers : {1, 2, 3, 4}) {
        std::vector<TestParam> cases;
        for (int64_t n = 1; n <= kSweepMaxSize; n++) {
            cases.push_back({.size = n,
                .k = n / 2,
                .max_key = kSweepMaxSize,
                .n_layers = n_layers,
                .repeat = 2});
            cases.push_back(
                {.size = n, .k = 0, .max_key = kSweepMaxSize, .n_layers = n_layers, .repeat = 1});
            cases.push_back({.size = n,
                .k = n - 1,
                .max_key = kSweepMaxSize,
                .n_layers = n_layers,
                .repeat = 1});
        }
        for (const auto& param : cases) {
            utest::test("select", "sweep", random_test, param);
        }
    }
});

auto random = utest::register_test([] {
    constexpr TestParam kCases[] = {
        {20, 10, 10, 1, 10},
        {20, 10, 10, 2, 10},
        {20, 10, 10, 3, 10},
        {20, 10, 10, 4, 10},
        {100, 10, 10, 1, 10},
        {100, 40, 10, 2, 10},
        {100, 90, 10, 3, 10},
        {100, 10, 30, 4, 10},
        {100, 40, 30, 1, 10},
        {100, 90, 30, 2, 10},
        {100, 10, 100, 3, 10},
        {100, 40, 100, 4, 10},
        {100, 90, 100, 1, 10},
        {1000, 500, 1000, 2, 2},
        {1000, 500, 1000, 3, 2},
        {1000, 500, 1000, 4, 2},
        {1000, 0, 1000, 4, 1},    // k = 0 (minimum)
        {1000, 999, 1000, 4, 1},  // k = n-1 (maximum)
        {1000, 500, 1, 4, 1},     // all elements share the same key
        {1000, 0, 1, 4, 1},       // k = 0, single key
        {1000, 999, 1, 4, 1},     // k = n-1, single key
    };
    for (const auto& param : kCases) {
        utest::test("select", "kCases", random_test, param);
    }
});

auto signed_keys = utest::register_test([] {
    constexpr TestParam kCases[] = {
        {1, 0, 10, 1, 10},
        {2, 1, 10, 2, 10},
        {7, 3, 10, 3, 5},
        {100, 50, 100, 4, 5},
    };
    for (const auto& param : kCases) {
        utest::test("select", "signed_keys", signed_key_test, param);
    }
});

auto duplicates = utest::register_test([] {
    constexpr TestParam kCases[] = {
        {1, 0, 1, 1, 2},
        {2, 1, 1, 2, 2},
        {16, 8, 1, 3, 2},
        {100, 50, 1, 4, 2},
        {100, 0, 1, 4, 1},
        {100, 99, 1, 4, 1},
    };
    for (const auto& param : kCases) {
        utest::test("select", "duplicates", duplicate_key_test, param);
    }
});

auto identity = utest::register_test([] {
    constexpr TestParam kCases[] = {
        {1, 0, 10, 1, 5},
        {2, 1, 10, 2, 5},
        {64, 32, 10, 3, 3},
        {100, 50, 100, 4, 3},
        {100, 0, 100, 4, 2},
        {100, 99, 100, 4, 2},
        {100, 50, 1, 4, 2},  // all values equal
    };
    for (const auto& param : kCases) {
        utest::test("select", "identity_proj", identity_proj_test, param);
    }
});

auto invalid = utest::register_test(
    [] { utest::test("select", "invalid", invalid_input_throws, int64_t{0}); });
}  // namespace
