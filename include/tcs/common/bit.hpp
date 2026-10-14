#pragma once

#include <bit>
#include <climits>
#include <cstdint>

#include "assert.hpp"

namespace tcs::common {
constexpr int64_t n_machine_word_bits = sizeof(uint64_t) * CHAR_BIT;

inline int64_t bit_width(int64_t x) { return std::bit_width(static_cast<uint64_t>(x)); }

inline int64_t ceil_log2(int64_t x) {
    assert_or_throw(x > 0, "ceil_log2: argument must be positive");
    return bit_width(x - 1);
}
}  // namespace tcs::common
