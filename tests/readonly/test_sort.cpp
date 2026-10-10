// Tests for tcs::readonly::sort::sort.
//
// The algorithm reads its input through const (read-only) random-access
// iterators and writes the sorted permutation into a caller-provided output
// range, so every check below asserts three things at once:
//   * the output equals the stable sort of the input by key, element identity
//     included (ties are broken by iterator position);
//   * the input range is left untouched;
//   * nothing is written at or past output[n].
//
// Keep the case count small: this file must stay within the debug-mode runtime
// budget in AGENTS.md.

#include <algorithm>
#include <cstdint>
#include <format>
#include <random>
#include <stdexcept>
#include <utility>
#include <vector>

#include "common/indexed_element.hpp"
#include "common/utest.hpp"
#include "tcs/readonly/sort.hpp"

namespace {
constexpr int kRandomSeed = 42;

struct TestParam {
    int64_t size;
    int64_t max_key;
    int64_t workspace;
    int64_t repeat;
};

struct ShapeParam {
    int64_t size;
    int64_t shape;
    int64_t workspace;
    int64_t repeat;
};

std::pair<int64_t, int64_t> key_and_index(const IndexedElement& el) { return {el.key, el.index}; }

std::vector<IndexedElement> make_input(int64_t size, int64_t max_key, std::mt19937& gen) {
    std::uniform_int_distribution<int64_t> key_dist(1, max_key);
    std::vector<IndexedElement> arr(static_cast<size_t>(size));
    for (int64_t i = 0; i < size; i++) {
        arr[static_cast<size_t>(i)] = {key_dist(gen), i};
    }
    return arr;
}

// Deterministic input shapes: 0 ascending, 1 descending, 2 all keys equal,
// 3 two interleaved values, 4 organ pipe (up then down), 5 one odd element out.
std::vector<IndexedElement> make_shape(int64_t size, int64_t shape) {
    std::vector<IndexedElement> arr(static_cast<size_t>(size));
    for (int64_t i = 0; i < size; i++) {
        int64_t key = shape == 0   ? i
                      : shape == 1 ? size - 1 - i
                      : shape == 2 ? 7
                      : shape == 3 ? i % 2
                      : shape == 4 ? std::min(i, size - 1 - i)
                                   : (i == size / 2 ? 1 : 0);
        arr[static_cast<size_t>(i)] = {key, i};
    }
    return arr;
}

void run_checked(const std::vector<IndexedElement>& arr, int64_t workspace) {
    const int64_t n = static_cast<int64_t>(arr.size());
    const size_t un = static_cast<size_t>(n);

    auto expected = arr;
    std::ranges::stable_sort(expected, {}, IndexedElement::proj);

    auto snapshot = arr;
    const auto& carr = arr;  // const -> const_iterator: the input stays read-only
    // One extra sentinel slot catches any write at output[n].
    std::vector<IndexedElement> out(un + 1, IndexedElement{-1, -1});
    tcs::readonly::sort::sort(
        carr.begin(), carr.end(), out.begin(), workspace, IndexedElement::proj);

    utest::assert_or_throw_lazy(std::ranges::equal(out.begin(), out.begin() + n, expected.begin(),
                                    expected.end(), {}, key_and_index, key_and_index),
        [&] { return std::format("sort mismatch: n={}, workspace={}", n, workspace); });
    utest::assert_or_throw_lazy(std::ranges::equal(arr, snapshot, {}, key_and_index, key_and_index),
        [&] { return std::format("input modified: n={}, workspace={}", n, workspace); });
    utest::assert_or_throw_lazy(out[un].key == -1 && out[un].index == -1,
        [&] { return std::format("wrote past output[n]: n={}, workspace={}", n, workspace); });
}

void random_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    for (int64_t i = 0; i < param.repeat; i++) {
        run_checked(make_input(param.size, param.max_key, gen), param.workspace);
    }
}

void shape_test(ShapeParam param) {
    for (int64_t i = 0; i < param.repeat; i++) {
        run_checked(make_shape(param.size, param.shape), param.workspace);
    }
}

// The whole element (key and index) must survive as a copy, which catches a
// sort that emits the right keys but the wrong elements.
void default_proj_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    std::uniform_int_distribution<int64_t> key_dist(-param.max_key, param.max_key);
    for (int64_t i = 0; i < param.repeat; i++) {
        std::vector<int64_t> arr(static_cast<size_t>(param.size));
        for (int64_t& v : arr) {
            v = key_dist(gen);
        }
        auto expected = arr;
        std::ranges::stable_sort(expected);

        auto snapshot = arr;
        const auto& carr = arr;
        std::vector<int64_t> out(static_cast<size_t>(param.size), 0);
        tcs::readonly::sort::sort(carr.begin(), carr.end(), out.begin(), param.workspace);

        utest::assert_or_throw_lazy(out == expected,
            [&] { return std::format("default proj mismatch: n={}", param.size); });
        utest::assert_or_throw_lazy(
            arr == snapshot, [&] { return std::format("input modified: n={}", param.size); });
    }
}

// A non-identity projection (descending) must be honoured by both the
// comparisons and the tie-break.
void descending_proj_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    auto proj = [](const IndexedElement& el) { return -el.key; };
    for (int64_t i = 0; i < param.repeat; i++) {
        auto arr = make_input(param.size, param.max_key, gen);
        auto expected = arr;
        std::ranges::stable_sort(expected, {}, proj);

        auto snapshot = arr;
        const auto& carr = arr;
        std::vector<IndexedElement> out(static_cast<size_t>(param.size), IndexedElement{-1, -1});
        tcs::readonly::sort::sort(carr.begin(), carr.end(), out.begin(), param.workspace, proj);

        utest::assert_or_throw_lazy(
            std::ranges::equal(out, expected, {}, key_and_index, key_and_index),
            [&] { return std::format("descending proj mismatch: n={}", param.size); });
        utest::assert_or_throw_lazy(
            std::ranges::equal(arr, snapshot, {}, key_and_index, key_and_index),
            [&] { return std::format("input modified: n={}", param.size); });
    }
}

void empty_input_test([[maybe_unused]] int64_t unused) {
    std::vector<IndexedElement> empty;
    std::vector<IndexedElement> out{{-1, -1}};
    tcs::readonly::sort::sort(empty.cbegin(), empty.cend(), out.begin(), 1, IndexedElement::proj);
    utest::assert_or_throw(out[0].key == -1 && out[0].index == -1);
}

void single_element_test([[maybe_unused]] int64_t unused) {
    std::vector<IndexedElement> arr{{42, 0}};
    std::vector<IndexedElement> out(2, IndexedElement{-1, -1});
    tcs::readonly::sort::sort(arr.cbegin(), arr.cend(), out.begin(), 1, IndexedElement::proj);
    utest::assert_or_throw(out[0].key == 42 && out[0].index == 0);
    utest::assert_or_throw(out[1].key == -1 && out[1].index == -1);
    utest::assert_or_throw(arr[0].key == 42 && arr[0].index == 0);
}

// Invalid preconditions must be rejected with a std::runtime_error.
void invalid_input_throws([[maybe_unused]] int64_t unused) {
    std::vector<IndexedElement> arr{{3, 0}, {1, 1}, {2, 2}};
    std::vector<IndexedElement> out(3, IndexedElement{-1, -1});

    // The workspace budget must be positive.
    for (int64_t bad_workspace : {int64_t{0}, int64_t{-1}}) {
        bool threw = false;
        try {
            tcs::readonly::sort::sort(
                arr.cbegin(), arr.cend(), out.begin(), bad_workspace, IndexedElement::proj);
        } catch (const std::runtime_error&) {
            threw = true;
        }
        utest::assert_or_throw(threw);
    }

    // first must not be past last.
    bool threw = false;
    try {
        tcs::readonly::sort::sort(arr.cend(), arr.cbegin(), out.begin(), 1, IndexedElement::proj);
    } catch (const std::runtime_error&) {
        threw = true;
    }
    utest::assert_or_throw(threw);
}

// Boundary sizes where ceil_log2(n), the tree height and the number of blocks
// change, crossed with the key-distribution extremes (max_key = 1 makes every
// key equal, which exercises the position tie-break) and a few workspaces.
auto sweep = utest::register_test([] {
    for (int64_t n : {int64_t{0}, int64_t{1}, int64_t{2}, int64_t{3}, int64_t{4}, int64_t{5},
             int64_t{6}, int64_t{8}, int64_t{9}, int64_t{16}, int64_t{17}, int64_t{32}, int64_t{33},
             int64_t{64}, int64_t{65}}) {
        for (int64_t max_key : {int64_t{1}, int64_t{64}}) {
            for (int64_t workspace : {int64_t{1}, int64_t{3}, int64_t{64}}) {
                utest::test("readonly_sort", "sweep", random_test,
                    TestParam{.size = n, .max_key = max_key, .workspace = workspace, .repeat = 2});
            }
        }
    }
});

// Every small size (exhaustive below 17) over deterministic shapes.
auto shapes = utest::register_test([] {
    for (int64_t shape = 0; shape < 6; shape++) {
        for (int64_t n : {int64_t{0}, int64_t{1}, int64_t{2}, int64_t{3}, int64_t{4}, int64_t{5},
                 int64_t{6}, int64_t{7}, int64_t{8}, int64_t{9}, int64_t{10}, int64_t{11},
                 int64_t{12}, int64_t{13}, int64_t{14}, int64_t{15}, int64_t{16}, int64_t{24},
                 int64_t{32}, int64_t{48}, int64_t{64}}) {
            utest::test("readonly_sort", "shapes", shape_test,
                ShapeParam{.size = n, .shape = shape, .workspace = 1, .repeat = 1});
        }
    }
});

// The workspace is the only tuning knob; minimal, awkward and oversized values
// must all yield the same output.
auto workspace_sweep = utest::register_test([] {
    for (int64_t n :
        {int64_t{1}, int64_t{2}, int64_t{3}, int64_t{5}, int64_t{16}, int64_t{37}, int64_t{64}}) {
        for (int64_t workspace : {int64_t{1}, int64_t{2}, int64_t{3}, int64_t{4}, int64_t{5},
                 int64_t{8}, int64_t{16}, int64_t{37}, int64_t{64}, int64_t{1000}}) {
            utest::test("readonly_sort", "workspace", random_test,
                TestParam{.size = n, .max_key = 8, .workspace = workspace, .repeat = 2});
        }
    }
});

// Larger sizes that force several sub-vectors, a partial last sub-vector,
// sub_block_size = 1, and a workspace far larger than the input.
auto regression = utest::register_test([] {
    constexpr TestParam kCases[] = {
        {0, 64, 1, 1},  // empty input: nothing is written
        {1, 64, 1, 1},  // single element
        {2, 64, 1, 1},  // smallest non-trivial tree
        {3, 64, 1, 4},
        {100, 10, 1, 4},      // minimal workspace
        {100, 1, 1, 4},       // all keys equal
        {1000, 1, 32, 2},     // all keys equal, larger input
        {300, 300, 1, 1},     // minimal workspace, several tree levels
        {2000, 1000, 32, 1},  // several sub-vectors, partial last one
        {3000, 10, 1024, 1},  // sub_block_size = 1, 12 sub-vectors
    };
    for (const auto& param : kCases) {
        utest::test("readonly_sort", "kCases", random_test, param);
    }
});

auto default_proj = utest::register_test([] {
    constexpr TestParam kCases[] = {
        {0, 64, 1, 1},
        {1, 64, 1, 1},
        {2, 64, 1, 1},
        {37, 1000, 1, 4},
        {100, 100, 8, 4},
        {1000, 10, 32, 2},
    };
    for (const auto& param : kCases) {
        utest::test("readonly_sort", "default_proj", default_proj_test, param);
    }
});

auto descending_proj = utest::register_test([] {
    constexpr TestParam kCases[] = {
        {2, 64, 1, 4},
        {100, 100, 1, 4},
        {1000, 1000, 32, 1},
        {1000, 1, 32, 1},  // all keys equal: the projection decides the order
    };
    for (const auto& param : kCases) {
        utest::test("readonly_sort", "descending_proj", descending_proj_test, param);
    }
});

auto edges = utest::register_test([] {
    utest::test("readonly_sort", "empty_input", empty_input_test, int64_t{0});
    utest::test("readonly_sort", "single_element", single_element_test, int64_t{0});
    utest::test("readonly_sort", "invalid", invalid_input_throws, int64_t{0});
});
}  // namespace
