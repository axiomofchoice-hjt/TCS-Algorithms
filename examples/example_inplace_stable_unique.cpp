#include <array>
#include <print>
#include <vector>

#include "common.hpp"
#include "tcs/inplace_stable_unique.hpp"

int main() {
    std::println("=== tcs::inplace_stable_unique::inplace_stable_unique ===");

    std::vector<int64_t> arr = {1, 2, 2, 3, 3, 3, 4, 4, 5, 6, 6, 7};

    print_arr(arr, "before");

    auto end = tcs::inplace_stable_unique::inplace_stable_unique(arr.begin(), arr.end());

    print_arr(arr, "after ");
}
