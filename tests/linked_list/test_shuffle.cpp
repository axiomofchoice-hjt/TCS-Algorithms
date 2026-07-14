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
    for (auto it = list.begin(); it != list.end(); ++it) result.push_back(*it);
    return result;
}

const std::vector<int> kCases[] = {
    {1, 2, 3, 4, 5, 6},
    {1, 2, 3, 4, 5},
    {1, 2},
    {1},
    {1, 1, 2, 2, 3, 3},
    {5, 3, 1, 2, 4},
};

auto test_shuffle = utest::register_test([] {
    for (int64_t i = 0; i < static_cast<int64_t>(std::size(kCases)); i++) {
        utest::test(
            "linked_list_shuffle", "multiset",
            [](int64_t idx) {
                const auto& input = kCases[idx];
                LinkedList list;
                for (int v : input) list.push_back(v);

                std::mt19937 gen(42);
                auto result =
                    tcs::linked_list::shuffle::linked_list_shuffle(
                        std::move(list), gen);

                auto output = to_vector(result);
                auto expected = input;
                std::ranges::sort(expected);
                auto sorted = output;
                std::ranges::sort(sorted);
                utest::assert_or_throw(sorted == expected,
                    "shuffled output must be a permutation of input");
            },
            i);
    }
});

auto test_empty = utest::register_test([] {
    utest::test(
        "linked_list_shuffle", "empty",
        [](int64_t) {
            LinkedList list;
            std::mt19937 gen(42);
            auto result =
                tcs::linked_list::shuffle::linked_list_shuffle(
                    std::move(list), gen);
            utest::assert_or_throw(result.empty(), "empty list should stay empty");
        },
        int64_t{0});
});

}  // namespace
