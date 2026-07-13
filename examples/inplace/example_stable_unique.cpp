#include <print>
#include <vector>

#include "../common.hpp"
#include "tcs/inplace/stable_unique.hpp"

int main() {
    std::println("=== tcs::inplace::stable_unique::inplace_stable_unique ===");

    constexpr auto kArrayWithDuplicates = std::array{1, 2, 2, 3, 3, 3, 4, 4, 5, 6, 6, 7};
    auto arr = std::vector<int64_t>(kArrayWithDuplicates.begin(), kArrayWithDuplicates.end());

    print_arr(arr, "before");

    tcs::inplace::stable_unique::inplace_stable_unique(arr.begin(), arr.end());

    print_arr(arr, "after ");
}
