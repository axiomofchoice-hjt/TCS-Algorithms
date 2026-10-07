#include <algorithm>
#include <cstdint>
#include <random>
#include <stdexcept>
#include <utility>
#include <vector>

#include "common/indexed_element.hpp"
#include "common/utest.hpp"
#include "tcs/readonly/bit_vector_select.hpp"

namespace {
struct TestParam {
    int64_t size;
    int64_t k;
    int64_t max_key;
    int64_t repeat;
};

struct ShapeParam {
    int64_t size;
    int64_t k;
    int64_t shape;
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

// Deterministic shapes: ascending / descending / all equal / two interleaved
// values. The last two force the pivot search onto extreme elements, which is
// where a pivot split that keeps the pivot on one side would stop shrinking.
std::vector<IndexedElement> make_shape(int64_t size, int64_t shape) {
    std::vector<IndexedElement> arr(size);
    for (int64_t i = 0; i < size; i++) {
        int64_t key = shape == 0   ? i
                      : shape == 1 ? size - 1 - i
                      : shape == 2 ? 7
                                   : (i % 2 == 0 ? 0 : 1);
        arr[i] = {key, i};
    }
    return arr;
}

// Runs select on `arr` through const iterators (read-only input) and checks
// that the returned element is the correctly ordered k-th element and that the
// input is left untouched.
void run_checked(const std::vector<IndexedElement>& arr, int64_t k) {
    auto expected = arr;
    std::ranges::stable_sort(expected, {}, IndexedElement::proj);
    const int64_t n = static_cast<int64_t>(arr.size());
    utest::assert_or_throw(k >= 0 && k < n);

    auto snapshot = arr;
    const auto& carr = arr;  // const vector -> const_iterator (read-only)
    auto result = tcs::readonly::bit_vector_select::bit_vector_select(
        carr.cbegin(), carr.cend(), k, IndexedElement::proj);

    utest::assert_or_throw(result >= carr.cbegin() && result < carr.cend());
    utest::assert_or_throw(IndexedElement::proj(*result) == IndexedElement::proj(expected[k]));
    utest::assert_or_throw(result->index == expected[k].index);
    auto key_and_index = [](const IndexedElement& el) { return std::pair(el.key, el.index); };
    utest::assert_or_throw(std::ranges::equal(arr, snapshot, {}, key_and_index, key_and_index));
}

void random_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    for (int64_t i = 0; i < param.repeat; i++) {
        run_checked(make_input(param.size, param.max_key, gen), param.k);
    }
}

// Keys drawn from a symmetric range including negatives.
void signed_key_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    for (int64_t i = 0; i < param.repeat; i++) {
        run_checked(make_signed_input(param.size, param.max_key, gen), param.k);
    }
}

// Every element shares the same key: verifies the index tie-break order and
// that an all-equal candidate set still terminates.
void duplicate_key_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    for (int64_t i = 0; i < param.repeat; i++) {
        auto arr = make_input(param.size, 1, gen);  // max_key = 1 -> all keys equal
        run_checked(arr, param.k);
    }
}

void shape_test(ShapeParam param) {
    for (int64_t i = 0; i < param.repeat; i++) {
        run_checked(make_shape(param.size, param.shape), param.k);
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
        auto result = tcs::readonly::bit_vector_select::bit_vector_select(
            carr.cbegin(), carr.cend(), param.k);
        utest::assert_or_throw(*result == expected[param.k]);
        utest::assert_or_throw(std::ranges::equal(arr, snapshot));
    }
}

// A single element is always the 0-th order statistic.
void single_element_test([[maybe_unused]] int64_t unused) {
    std::vector<int64_t> arr{42};
    auto result = tcs::readonly::bit_vector_select::bit_vector_select(arr.begin(), arr.end(), 0);
    utest::assert_or_throw(result == arr.begin());
    utest::assert_or_throw(*result == 42);
}

// Invalid preconditions must be rejected with a std::runtime_error.
void invalid_input_throws([[maybe_unused]] int64_t unused) {
    std::vector<int64_t> arr{3, 1, 2};

    // k must be within [0, size).
    for (int64_t bad_k : {int64_t{-1}, int64_t{3}}) {
        bool threw = false;
        try {
            (void)tcs::readonly::bit_vector_select::bit_vector_select(
                arr.begin(), arr.end(), bad_k);
        } catch (const std::runtime_error&) {
            threw = true;
        }
        utest::assert_or_throw(threw);
    }

    // An empty range has no valid order statistic.
    std::vector<int64_t> empty;
    bool threw = false;
    try {
        (void)tcs::readonly::bit_vector_select::bit_vector_select(empty.begin(), empty.end(), 0);
    } catch (const std::runtime_error&) {
        threw = true;
    }
    utest::assert_or_throw(threw);
}

// Sweep small sizes for the min / mid / max positions.
auto sweep = utest::register_test([] {
    for (int64_t n = 1; n <= kSweepMaxSize; n++) {
        utest::test("bit_vector_select", "sweep", random_test,
            TestParam{.size = n, .k = n / 2, .max_key = kSweepMaxSize, .repeat = 2});
        utest::test("bit_vector_select", "sweep", random_test,
            TestParam{.size = n, .k = 0, .max_key = kSweepMaxSize, .repeat = 1});
        utest::test("bit_vector_select", "sweep", random_test,
            TestParam{.size = n, .k = n - 1, .max_key = kSweepMaxSize, .repeat = 1});
    }
});

// The same sweep over deterministic shapes, including the extreme-pivot ones.
auto shapes = utest::register_test([] {
    for (int64_t shape = 0; shape < 4; shape++) {
        for (int64_t n = 1; n <= kSweepMaxSize; n++) {
            utest::test("bit_vector_select", "shapes", shape_test,
                ShapeParam{.size = n, .k = n / 2, .shape = shape, .repeat = 1});
            utest::test("bit_vector_select", "shapes", shape_test,
                ShapeParam{.size = n, .k = 0, .shape = shape, .repeat = 1});
            utest::test("bit_vector_select", "shapes", shape_test,
                ShapeParam{.size = n, .k = n - 1, .shape = shape, .repeat = 1});
        }
    }
});

auto random = utest::register_test([] {
    constexpr TestParam kCases[] = {
        {20, 10, 10, 10},
        {20, 0, 10, 5},
        {20, 19, 10, 5},
        {100, 10, 10, 5},
        {100, 40, 10, 5},
        {100, 90, 10, 5},
        {100, 10, 30, 5},
        {100, 40, 30, 5},
        {100, 90, 30, 5},
        {100, 10, 100, 5},
        {100, 40, 100, 5},
        {100, 90, 100, 5},
        {1000, 500, 1000, 2},
        {8192, 4096, 1000, 1},
        {8192, 0, 1000, 1},     // k = 0 (minimum), larger n
        {8192, 8191, 1000, 1},  // k = n-1 (maximum), larger n
        {1000, 0, 1000, 1},     // k = 0 (minimum)
        {1000, 999, 1000, 1},   // k = n-1 (maximum)
        {1000, 500, 1, 1},      // all elements share the same key
        {1000, 0, 1, 1},        // k = 0, single key
        {1000, 999, 1, 1},      // k = n-1, single key
    };
    for (const auto& param : kCases) {
        utest::test("bit_vector_select", "kCases", random_test, param);
    }
});

auto signed_keys = utest::register_test([] {
    constexpr TestParam kCases[] = {
        {1, 0, 10, 10},
        {2, 0, 10, 10},
        {2, 1, 10, 10},
        {7, 3, 10, 5},
        {100, 50, 100, 5},
        {100, 0, 100, 5},
        {100, 99, 100, 5},
    };
    for (const auto& param : kCases) {
        utest::test("bit_vector_select", "signed_keys", signed_key_test, param);
    }
});

auto duplicates = utest::register_test([] {
    constexpr TestParam kCases[] = {
        {1, 0, 1, 2},
        {2, 0, 1, 2},
        {2, 1, 1, 2},
        {16, 8, 1, 2},
        {100, 50, 1, 2},
        {100, 0, 1, 2},
        {100, 99, 1, 2},
    };
    for (const auto& param : kCases) {
        utest::test("bit_vector_select", "duplicates", duplicate_key_test, param);
    }
});

auto identity = utest::register_test([] {
    constexpr TestParam kCases[] = {
        {1, 0, 10, 5},
        {2, 1, 10, 5},
        {64, 32, 10, 3},
        {100, 50, 100, 3},
        {100, 0, 100, 2},
        {100, 99, 100, 2},
        {100, 50, 1, 2},  // all values equal
    };
    for (const auto& param : kCases) {
        utest::test("bit_vector_select", "identity_proj", identity_proj_test, param);
    }
});

auto edge = utest::register_test(
    [] { utest::test("bit_vector_select", "single_element", single_element_test, int64_t{0}); });

auto invalid = utest::register_test(
    [] { utest::test("bit_vector_select", "invalid", invalid_input_throws, int64_t{0}); });
}  // namespace
