#include <print>
#include <vector>

#include "common.hpp"
#include "tcs/inplace_unstable_merge.hpp"

int main() {
    std::println("=== tcs::inplace_unstable_merge::inplace_unstable_merge ===");

    constexpr int64_t kLeftSize = 5;
    constexpr auto kSortedOdds = std::array{1, 3, 5, 7, 9};
    constexpr auto kSortedEvens = std::array{2, 4, 6, 8, 10};
    auto arr = std::vector<int64_t>{};
    arr.insert(arr.end(), kSortedOdds.begin(), kSortedOdds.end());
    arr.insert(arr.end(), kSortedEvens.begin(), kSortedEvens.end());

    print_arr(arr, "before");

    tcs::inplace_unstable_merge::inplace_unstable_merge(
        arr.data(), arr.data() + kLeftSize, arr.data() + arr.size());

    print_arr(arr, "after ");
}
