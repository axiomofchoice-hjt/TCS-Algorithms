#pragma once

#include <cstdint>

struct IndexedElement {
    int64_t key;
    int64_t index;

    static int64_t proj(const IndexedElement& el) { return el.key; }
};
