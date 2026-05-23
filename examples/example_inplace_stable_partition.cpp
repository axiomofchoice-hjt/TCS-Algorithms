#include <print>
#include <vector>

#include "common.hpp"
#include "tcs/inplace_stable_partition.hpp"

int main() {
    std::println("=== tcs::inplace_stable_partition::inplace_stable_partition ===");

    constexpr auto kZerosAndOnes = std::array{1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1};
    auto arr = std::vector<int64_t>(kZerosAndOnes.begin(), kZerosAndOnes.end());

    print_arr(arr, "before");

    tcs::inplace_stable_partition::inplace_stable_partition(
        arr.data(), arr.data() + arr.size(), [](int64_t x) { return x == 0; });

    print_arr(arr, "after ");
}
