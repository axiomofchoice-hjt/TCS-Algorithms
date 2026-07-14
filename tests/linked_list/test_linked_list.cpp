#include <cstdint>
#include <vector>

#include "common/utest.hpp"
#include "tcs/linked_list/linked_list.hpp"

namespace {

using LinkedList = tcs::linked_list::LinkedList<int>;

std::vector<int> to_vector(const LinkedList& list) {
    std::vector<int> result;
    for (auto it = list.begin(); it != list.end(); ++it) {
        result.push_back(*it);
    }
    return result;
}

auto test_push_back = utest::register_test([] {
    utest::test(
        "linked_list", "push_back",
        [](int64_t) {
            LinkedList list;
            utest::assert_or_throw(list.empty(), "new list should be empty");
            utest::assert_or_throw(list.size() == 0, "new list size should be 0");

            list.push_back(1);
            utest::assert_or_throw(!list.empty(), "list should not be empty");
            utest::assert_or_throw(list.size() == 1, "size should be 1");
            utest::assert_or_throw(*list.begin() == 1, "first element should be 1");

            list.push_back(2);
            list.push_back(3);
            utest::assert_or_throw(list.size() == 3, "size should be 3");
            utest::assert_or_throw(to_vector(list) == std::vector<int>({1, 2, 3}),
                "elements should be in insertion order");
        },
        int64_t{0});
});

auto test_erase = utest::register_test([] {
    utest::test(
        "linked_list", "erase",
        [](int64_t) {
            LinkedList list;
            list.push_back(1);
            list.push_back(2);
            list.push_back(3);

            auto it = list.begin();
            ++it;
            it = list.erase(it);
            utest::assert_or_throw(
                to_vector(list) == std::vector<int>({1, 3}), "erasing middle element");
            utest::assert_or_throw(*it == 3, "erase should return next iterator");

            it = list.begin();
            it = list.erase(it);
            utest::assert_or_throw(
                to_vector(list) == std::vector<int>({3}), "erasing first element");
            utest::assert_or_throw(*it == 3, "erase should return next iterator");
        },
        int64_t{0});
});

auto test_split = utest::register_test([] {
    utest::test(
        "linked_list", "split",
        [](int64_t) {
            LinkedList list;
            for (int v : {1, 2, 3, 4, 5}) {
                list.push_back(v);
            }

            auto it = list.begin();
            std::advance(it, 2);
            auto [left, right] = LinkedList::split(std::move(list), it);

            utest::assert_or_throw(
                to_vector(left) == std::vector<int>({1, 2}), "left half after split");
            utest::assert_or_throw(
                to_vector(right) == std::vector<int>({3, 4, 5}), "right half after split");
        },
        int64_t{0});
});

auto test_concat = utest::register_test([] {
    utest::test(
        "linked_list", "concat",
        [](int64_t) {
            LinkedList left;
            left.push_back(1);
            left.push_back(2);

            LinkedList right;
            right.push_back(3);
            right.push_back(4);

            auto merged = LinkedList::concat(std::move(left), std::move(right));
            utest::assert_or_throw(to_vector(merged) == std::vector<int>({1, 2, 3, 4}),
                "concat should append right after left");
        },
        int64_t{0});
});

auto test_move = utest::register_test([] {
    utest::test(
        "linked_list", "move",
        [](int64_t) {
            LinkedList list;
            list.push_back(1);
            list.push_back(2);

            LinkedList moved(std::move(list));
            utest::assert_or_throw(to_vector(moved) == std::vector<int>({1, 2}),
                "moved list should contain original elements");
            utest::assert_or_throw(list.empty(), "moved-from list should be empty");
            utest::assert_or_throw(list.size() == 0, "moved-from list size should be 0");

            LinkedList assigned;
            assigned = std::move(moved);
            utest::assert_or_throw(to_vector(assigned) == std::vector<int>({1, 2}),
                "move-assigned list should contain original elements");
            utest::assert_or_throw(moved.empty(), "moved-from list should be empty");
        },
        int64_t{0});
});

auto test_empty = utest::register_test([] {
    utest::test(
        "linked_list", "empty",
        [](int64_t) {
            LinkedList list;
            utest::assert_or_throw(list.empty(), "new list should be empty");

            auto it = list.begin();
            auto end = list.end();
            utest::assert_or_throw(it == end, "begin should equal end for empty list");

            list.push_back(42);
            utest::assert_or_throw(!list.empty(), "non-empty list should not be empty");
        },
        int64_t{0});
});

}  // namespace
