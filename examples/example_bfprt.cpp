#include <print>
#include <vector>

#include "common.hpp"
#include "tcs/bfprt.hpp"

int main() {
    std::println("=== tcs::bfprt::bfprt ===");

    constexpr auto kShuffledOneToTen = std::array{2, 5, 9, 6, 3, 10, 1, 7, 4, 8};
    auto arr = std::vector<int64_t>(kShuffledOneToTen.begin(), kShuffledOneToTen.end());
    constexpr int64_t kTargetRank = 5;

    print_arr(arr, "before");

    tcs::bfprt::bfprt(arr.begin(), arr.begin() + kTargetRank, arr.end());

    print_arr(arr, "after ");
    std::println("{}-th smallest element: {}", kTargetRank, arr[kTargetRank]);
}
