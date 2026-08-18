#include <algorithm>
#include <cstdint>
#include <list>
#include <random>
#include <vector>

#include "common/utest.hpp"
#include "tcs/linked_list/shuffle.hpp"

namespace {
using IntList = std::list<int>;

std::vector<int> to_vector(const IntList& list) { return {list.begin(), list.end()}; }

constexpr int kRandomSeed = 42;

const std::vector<int> kSorted6 = {1, 2, 3, 4, 5, 6};
const std::vector<int> kSorted5 = {1, 2, 3, 4, 5};
const std::vector<int> kSorted2 = {1, 2};
const std::vector<int> kSingle1 = {1};
const std::vector<int> kDuplicates = {1, 1, 2, 2, 3, 3};
const std::vector<int> kUnsorted = {5, 3, 1, 2, 4};

const std::vector<int> kCases[] = {
    kSorted6,
    kSorted5,
    kSorted2,
    kSingle1,
    kDuplicates,
    kUnsorted,
};

// The shuffle takes its RNG by value, so wrap the generator in a [&] lambda:
// copying the lambda copies only the reference, and every recursive call
// shares one random stream. No `mutable` needed — the body mutates the
// *referenced* generator, not the capture itself. The lambda draws a uniform
// integer in [lo, hi], per the Rand contract of the shuffle.
void shuffle_inplace(IntList& list, std::mt19937& gen) {
    tcs::linked_list::shuffle::linked_list_shuffle(list, [&](int64_t lo, int64_t hi) {
        return std::uniform_int_distribution<int64_t>(lo, hi)(gen);
    });
}

auto test_shuffle = utest::register_test([] {
    for (int64_t i = 0; i < static_cast<int64_t>(std::size(kCases)); i++) {
        utest::test(
            "linked_list_shuffle", "multiset",
            [](int64_t idx) {
                const auto& input = kCases[idx];
                IntList list(input.begin(), input.end());

                std::mt19937 gen(kRandomSeed);
                shuffle_inplace(list, gen);

                auto output = to_vector(list);
                auto expected = input;
                std::ranges::sort(expected);
                std::ranges::sort(output);
                utest::assert_or_throw(
                    output == expected, "shuffled output must be a permutation of input");
            },
            i);
    }
});

auto test_empty = utest::register_test([] {
    utest::test(
        "linked_list_shuffle", "empty",
        [](int64_t) {
            IntList list;
            std::mt19937 gen(kRandomSeed);
            shuffle_inplace(list, gen);
            utest::assert_or_throw(list.empty(), "empty list should stay empty");
        },
        int64_t{0});
});

// Same seed must reproduce the same shuffle: the by-value Rand copies all
// refer to the one captured generator, so the outcome is deterministic.
auto test_deterministic = utest::register_test([] {
    utest::test(
        "linked_list_shuffle", "deterministic",
        [](int64_t) {
            IntList a(kSorted6.begin(), kSorted6.end());
            IntList b(kSorted6.begin(), kSorted6.end());
            std::mt19937 gen_a(kRandomSeed);
            std::mt19937 gen_b(kRandomSeed);
            shuffle_inplace(a, gen_a);
            shuffle_inplace(b, gen_b);
            utest::assert_or_throw(
                to_vector(a) == to_vector(b), "same seed must give the same shuffle");
        },
        int64_t{0});
});

// The generator is consumed through the reference capture, so the shuffle
// really randomizes: a different seed must give a different order.
auto test_seed_sensitivity = utest::register_test([] {
    utest::test(
        "linked_list_shuffle", "seed_sensitivity",
        [](int64_t) {
            IntList a(kSorted6.begin(), kSorted6.end());
            IntList b(kSorted6.begin(), kSorted6.end());
            std::mt19937 gen_a(kRandomSeed);
            std::mt19937 gen_b(kRandomSeed + 1);
            shuffle_inplace(a, gen_a);
            shuffle_inplace(b, gen_b);
            utest::assert_or_throw(
                to_vector(a) != to_vector(b), "different seeds should give different shuffles");
        },
        int64_t{0});
});
}  // namespace
