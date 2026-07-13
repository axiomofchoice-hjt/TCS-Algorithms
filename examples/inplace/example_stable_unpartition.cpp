#include <print>
#include <vector>

#include "../common.hpp"
#include "tcs/inplace/stable_unpartition.hpp"

int main() {
    std::println("=== tcs::inplace::stable_unpartition::inplace_stable_unpartition ===");

    // partitioned: zeros first, ones last
    auto arr = std::vector<int64_t>{0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1};
    // placement: 0 = originally from left half, 1 = originally from right half
    std::vector<int64_t> placement = {1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0};

    print_arr(arr, "before");

    tcs::inplace::stable_unpartition::inplace_stable_unpartition(
        arr.begin(), arr.end(), [](int64_t x) { return x == 0; },
        [&arr, &placement](auto p) { return !placement[p - arr.begin()]; });

    print_arr(arr, "after ");
}
