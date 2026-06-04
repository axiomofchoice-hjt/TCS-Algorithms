#include <array>
#include <print>
#include <vector>

#include "common.hpp"
#include "tcs/inplace_unstable_qsort.hpp"

int main() {
    std::println("=== tcs::inplace_unstable_qsort::unstable_quick_sort ===");

    constexpr auto kShuffledOneToTen = std::array{2, 5, 9, 6, 3, 10, 1, 7, 4, 8};
    auto arr = std::vector<int64_t>(kShuffledOneToTen.begin(), kShuffledOneToTen.end());

    print_arr(arr, "before");

    tcs::inplace_unstable_qsort::unstable_quick_sort(arr.begin(), arr.end());

    print_arr(arr, "after ");
}
