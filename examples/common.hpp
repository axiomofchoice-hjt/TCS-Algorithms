#pragma once

#include <print>
#include <ranges>
#include <string_view>

inline void print_arr(const auto& arr, std::string_view label) {
    std::print("{}: [", label);
    for (auto [i, v] : arr | std::views::enumerate) {
        std::print("{}", v);
        if (i + 1 < arr.size()) {
            std::print(", ");
        }
    }
    std::println("]");
}
