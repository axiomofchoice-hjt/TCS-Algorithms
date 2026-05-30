#pragma once

#include <compare>
#include <cstdint>

/// Element with a key for ordering and an index for stability verification.
struct IndexedElement {
    int64_t key;
    int64_t index;

    std::strong_ordering operator<=>(const IndexedElement& other) const { return key <=> other.key; }
    bool operator==(const IndexedElement& other) const { return key == other.key; }
};
