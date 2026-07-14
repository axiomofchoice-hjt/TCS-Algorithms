#include <cstdint>
#include <vector>

#include "common/utest.hpp"
#include "tcs/linked_list/linked_list.hpp"

namespace {

using LinkedList = tcs::linked_list::LinkedList<int>;

const std::vector<int> kSeq12 = {1, 2};
const std::vector<int> kSeq123 = {1, 2, 3};
const std::vector<int> kSeq1234 = {1, 2, 3, 4};
const std::vector<int> kSeq12345 = {1, 2, 3, 4, 5};
const std::vector<int> kSeq34 = {3, 4};
const std::vector<int> kSeq345 = {3, 4, 5};
const std::vector<int> kAfterEraseMid = {1, 3};
const std::vector<int> kSingle3 = {3};
constexpr int kTestValue = 42;

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
            utest::assert_or_throw(to_vector(list) == kSeq123,
                "elements should be in insertion order");
        },
        int64_t{0});
});

auto test_erase = utest::register_test([] {
    utest::test(
        "linked_list", "erase",
        [](int64_t) {
            LinkedList list;
            for (int v : kSeq123) list.push_back(v);

            auto it = list.begin();
            ++it;
            it = list.erase(it);
            utest::assert_or_throw(to_vector(list) == kAfterEraseMid, "erasing middle element");
            utest::assert_or_throw(*it == 3, "erase should return next iterator");

            it = list.begin();
            it = list.erase(it);
            utest::assert_or_throw(to_vector(list) == kSingle3, "erasing first element");
            utest::assert_or_throw(*it == 3, "erase should return next iterator");
        },
        int64_t{0});
});

auto test_split = utest::register_test([] {
    utest::test(
        "linked_list", "split",
        [](int64_t) {
            LinkedList list;
            for (int v : kSeq12345) {
                list.push_back(v);
            }

            auto it = list.begin();
            std::advance(it, 2);
            auto [left, right] = LinkedList::split(std::move(list), it);

            utest::assert_or_throw(to_vector(left) == kSeq12, "left half after split");
            utest::assert_or_throw(to_vector(right) == kSeq345, "right half after split");
        },
        int64_t{0});
});

auto test_concat = utest::register_test([] {
    utest::test(
        "linked_list", "concat",
        [](int64_t) {
            LinkedList left;
            for (int v : kSeq12) left.push_back(v);

            LinkedList right;
            for (int v : kSeq34) right.push_back(v);

            auto merged = LinkedList::concat(std::move(left), std::move(right));
            utest::assert_or_throw(to_vector(merged) == kSeq1234,
                "concat should append right after left");
        },
        int64_t{0});
});

auto test_move = utest::register_test([] {
    utest::test(
        "linked_list", "move",
        [](int64_t) {
            LinkedList list;
            for (int v : kSeq12) list.push_back(v);

            LinkedList moved(std::move(list));
            utest::assert_or_throw(to_vector(moved) == kSeq12,
                "moved list should contain original elements");
            utest::assert_or_throw(list.empty(), "moved-from list should be empty");
            utest::assert_or_throw(list.size() == 0, "moved-from list size should be 0");

            LinkedList assigned;
            assigned = std::move(moved);
            utest::assert_or_throw(to_vector(assigned) == kSeq12,
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

            list.push_back(kTestValue);
            utest::assert_or_throw(!list.empty(), "non-empty list should not be empty");
        },
        int64_t{0});
});

}  // namespace
