#include <algorithm>
#include <cstdint>
#include <random>
#include <vector>

#include "common/utest.hpp"
#include "tcs/linked_list/shuffle.hpp"

namespace {

using LinkedList = tcs::linked_list::LinkedList<int>;

std::vector<int> to_vector(const LinkedList& list) {
    std::vector<int> result;
    for (auto it = list.begin(); it != list.end(); ++it) {
        result.push_back(*it);
    }
    return result;
}

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

auto test_shuffle = utest::register_test([] {
    for (int64_t i = 0; i < static_cast<int64_t>(std::size(kCases)); i++) {
        utest::test(
            "linked_list_shuffle", "multiset",
            [](int64_t idx) {
                const auto& input = kCases[idx];
                LinkedList list;
                for (int v : input) {
                    list.push_back(v);
                }

                std::mt19937 gen(kRandomSeed);
                auto result = tcs::linked_list::shuffle::linked_list_shuffle(std::move(list), gen);

                auto output = to_vector(result);
                auto expected = input;
                std::ranges::sort(expected);
                auto sorted = output;
                std::ranges::sort(sorted);
                utest::assert_or_throw(
                    sorted == expected, "shuffled output must be a permutation of input");
            },
            i);
    }
});

auto test_empty = utest::register_test([] {
    utest::test(
        "linked_list_shuffle", "empty",
        [](int64_t) {
            LinkedList list;
            std::mt19937 gen(kRandomSeed);
            auto result = tcs::linked_list::shuffle::linked_list_shuffle(std::move(list), gen);
            utest::assert_or_throw(result.empty(), "empty list should stay empty");
        },
        int64_t{0});
});

}  // namespace
