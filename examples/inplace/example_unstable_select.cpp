#include <array>
#include <print>
#include <vector>

#include "../common.hpp"
#include "tcs/inplace/unstable_select.hpp"

int main() {
    std::println("=== tcs::inplace::unstable_select::inplace_unstable_select ===");

    constexpr auto kShuffledOneToTen = std::array{2, 5, 9, 6, 3, 10, 1, 7, 4, 8};
    auto arr = std::vector<int64_t>(kShuffledOneToTen.begin(), kShuffledOneToTen.end());
    constexpr int64_t kTargetRank = 5;

    print_arr(arr, "before");

    tcs::inplace::unstable_select::inplace_unstable_select(
        arr.begin(), arr.begin() + kTargetRank, arr.end());

    print_arr(arr, "after ");
    std::println("{}-th smallest element: {}", kTargetRank, arr[kTargetRank]);
}
