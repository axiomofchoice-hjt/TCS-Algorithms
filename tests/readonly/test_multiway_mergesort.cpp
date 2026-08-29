#include <algorithm>
#include <cstdint>
#include <random>
#include <ranges>
#include <utility>
#include <vector>

#include "common/indexed_element.hpp"
#include "common/utest.hpp"
#include "tcs/readonly/multiway_mergesort.hpp"

namespace {
constexpr int kRandomSeed = 42;
constexpr int64_t kSweepMaxSize = 100;
constexpr int64_t kSweepMaxKey = 20;

struct TestParam {
    int64_t size;
    int64_t buffer;  // number of buffer cells (number of blocks)
    int64_t max_key;
    int64_t repeat;
};

// The buffer is a container holding iterators into the (read-only) input, so it
// is typed as a vector of const iterators. Its size is the number of blocks.
using Buffer = std::vector<std::vector<IndexedElement>::const_iterator>;

// Runs multiway_mergesort on `arr` through const iterators with a buffer of
// `buffer` cells and checks that the output is a *stable* sort of the input
// (exact (key, index) order matches std::stable_sort), and that the input array
// is left untouched.
void run_checked(const std::vector<IndexedElement>& arr, int64_t buffer) {
    auto expected = arr;
    std::ranges::stable_sort(expected, {}, IndexedElement::proj);

    auto snapshot = arr;
    const auto& carr = arr;  // const vector -> const_iterator (read-only)
    Buffer buffer_(static_cast<size_t>(buffer), carr.end());
    std::vector<IndexedElement> out(static_cast<size_t>(arr.size()));

    tcs::readonly::multiway_mergesort::multiway_mergesort(carr.begin(), carr.end(), buffer_.begin(),
        buffer_.end(), out.begin(), IndexedElement::proj);

    // Correctness + stability: the output must be exactly the stable-sorted
    // sequence of (key, index) pairs.
    auto key_and_index = [](const IndexedElement& el) { return std::pair(el.key, el.index); };
    utest::assert_or_throw(std::ranges::equal(out, expected, {}, key_and_index, key_and_index));

    // Read-only guarantee: the input is never modified.
    utest::assert_or_throw(std::ranges::equal(carr, snapshot, {}, key_and_index, key_and_index));
}

std::vector<IndexedElement> make_input(
    int64_t size, int64_t max_key, bool signed_keys, std::mt19937& gen) {
    std::vector<IndexedElement> arr(static_cast<size_t>(size));
    std::uniform_int_distribution<int64_t> key_dist(signed_keys ? -max_key : 1, max_key);
    for (int64_t i = 0; i < size; i++) {
        arr[static_cast<size_t>(i)] = {key_dist(gen), i};
    }
    return arr;
}

// Empty input must not crash and must produce no output (regardless of buffer).
void empty_input_test([[maybe_unused]] TestParam param) {
    for (int64_t buffer : {0, 1, 3, 5}) {
        std::vector<IndexedElement> arr;
        run_checked(arr, buffer);
    }
}

// Sweep every buffer size in [1, size + 1] for a batch of random arrays, covering
// single-block, multi-block, non-dividing, and oversized buffers.
void buffer_sweep_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    for (int64_t repeat = 0; repeat < param.repeat; repeat++) {
        auto arr = make_input(param.size, param.max_key, false, gen);
        for (int64_t buffer = 1; buffer <= param.size + 1; buffer++) {
            run_checked(arr, buffer);
        }
    }
}

void random_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    for (int64_t repeat = 0; repeat < param.repeat; repeat++) {
        auto arr = make_input(param.size, param.max_key, false, gen);
        run_checked(arr, param.buffer);
    }
}

void signed_key_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    for (int64_t repeat = 0; repeat < param.repeat; repeat++) {
        auto arr = make_input(param.size, param.max_key, true, gen);
        run_checked(arr, param.buffer);
    }
}

constexpr TestParam kCases[] = {
    {20, 3, 10, 20},
    {20, 5, 10, 20},
    {20, 20, 10, 20},
    {20, 21, 10, 20},  // oversized buffer
    {50, 7, 20, 20},
    {100, 10, 10, 20},
    {100, 37, 30, 20},  // non-dividing block count
    {100, 100, 30, 20},
    {100, 200, 30, 20},  // oversized buffer
    {1000, 3, 1000, 20},
    {1000, 100, 1000, 20},
    {1000, 1000, 10, 20},
    {1000, 5000, 10, 20},  // oversized buffer
    {10000, 37, 5000, 2},
    {10000, 1000, 5000, 2},
    {100000, 1000, 50000, 1},
    {1000, 1, 1, 1},     // all elements share a single key
    {1000, 17, 1, 1},    // all same key, non-dividing block count
    {1000, 1000, 1, 1},  // all same key, whole-array block count
};

constexpr TestParam kSignedCases[] = {
    {1, 1, 10, 5},
    {7, 3, 10, 5},
    {100, 37, 100, 5},
    {1000, 100, 1000, 3},
};

auto empty = utest::register_test([] {
    utest::test("multiway_mergesort", "empty_input", empty_input_test,
        TestParam{.size = 0, .buffer = 1, .max_key = 1, .repeat = 1});
});

auto buffer_sweep = utest::register_test([] {
    std::vector<TestParam> cases;
    for (int64_t n = 1; n <= kSweepMaxSize; n++) {
        cases.push_back({.size = n, .buffer = 1, .max_key = kSweepMaxKey, .repeat = 1});
    }
    for (const auto& param : cases) {
        utest::test("multiway_mergesort", "buffer_sweep", buffer_sweep_test, param);
    }
});

auto random = utest::register_test([] {
    for (const auto& param : kCases) {
        utest::test("multiway_mergesort", "kCases", random_test, param);
    }
});

auto signed_keys = utest::register_test([] {
    for (const auto& param : kSignedCases) {
        utest::test("multiway_mergesort", "signed_keys", signed_key_test, param);
    }
});
}  // namespace
