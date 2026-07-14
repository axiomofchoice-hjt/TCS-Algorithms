#pragma once

#include <cstdint>
#include <random>

#include "linked_list.hpp"

namespace tcs {
namespace linked_list {
namespace shuffle {
template <typename T, typename Random>
LinkedList<T> linked_list_shuffle(LinkedList<T> list, Random& rand) {
    int64_t n = list.size();
    if (n < 2) {
        return list;
    }

    auto it = std::next(list.begin(), n / 2);
    auto [left, right] = LinkedList<T>::split(std::move(list), it);

    left = linked_list_shuffle(std::move(left), rand);
    right = linked_list_shuffle(std::move(right), rand);

    int64_t left_sz = n / 2;
    int64_t right_sz = n - left_sz;

    LinkedList<T> res;
    while (left_sz + right_sz > 0) {
        std::uniform_int_distribution<int64_t> dist(0, left_sz + right_sz - 1);
        int64_t i = dist(rand);
        if (i < left_sz) {
            res.push_back(*left.begin());
            left.pop_front();
            left_sz--;
        } else {
            res.push_back(*right.begin());
            right.pop_front();
            right_sz--;
        }
    }
    return res;
}
}  // namespace shuffle
}  // namespace linked_list
}  // namespace tcs
