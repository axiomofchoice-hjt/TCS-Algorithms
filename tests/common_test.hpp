#pragma once

#include <algorithm>
#include <cstdint>
#include <ranges>
#include <vector>

/// Element with a key for ordering and an index for stability verification.
struct IndexedElement {
    int64_t key;
    int64_t index;

    static int64_t proj(const IndexedElement& el) { return el.key; }
};

template <typename Range>
void iota_index(Range range) {
    for (auto [i, el] : range | std::views::enumerate) {
        el.index = static_cast<int64_t>(i);
    }
}

template <typename Range>
bool is_stable(Range range) {
    auto sorted = range | std::ranges::to<std::vector<IndexedElement>>();
    std::ranges::sort(sorted, {}, IndexedElement::proj);
    for (auto [a, b] : range | std::views::pairwise) {
        if (a.key == b.key && a.index > b.index) {
            return false;
        }
    }
    return true;
}
