#include <array>
#include <print>
#include <vector>

#include "common.hpp"
#include "tcs/inplace_stable_quicksort.hpp"

int main() {
    std::println("=== tcs::inplace_stable_qsort::inplace_stable_quicksort ===");

    constexpr auto kShuffledOneToTen = std::array{2, 5, 9, 6, 3, 10, 1, 7, 4, 8};
    auto arr = std::vector<int64_t>(kShuffledOneToTen.begin(), kShuffledOneToTen.end());

    print_arr(arr, "before");

    tcs::inplace_stable_qsort::inplace_stable_quicksort(arr.begin(), arr.end());

    print_arr(arr, "after ");
}
