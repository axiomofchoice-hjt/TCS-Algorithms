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
    for (int64_t i : std::views::iota(0, static_cast<int64_t>(range.size()))) {
        range[i].index = i;
    }
}

template <typename Range>
bool is_stable(Range range) {
    auto sorted = range | std::ranges::to<std::vector<IndexedElement>>();
    std::ranges::stable_sort(sorted, {}, IndexedElement::proj);
    for (int64_t i : std::views::iota(0, static_cast<int64_t>(sorted.size()) - 1)) {
        if (sorted[i].key == sorted[i + 1].key && sorted[i].index > sorted[i + 1].index) {
            return false;
        }
    }
    return true;
}
