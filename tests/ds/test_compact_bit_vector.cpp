#include <algorithm>
#include <cstdint>
#include <format>
#include <random>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/utest.hpp"
#include "tcs/ds/compact_bit_vector.hpp"

namespace {
using tcs::ds::compact_bit_vector::BitVector;
using tcs::ds::compact_bit_vector::ceil_log2;
using tcs::ds::compact_bit_vector::CompactBitVector;
using tcs::ds::compact_bit_vector::n_machine_word_bits;
using tcs::ds::compact_bit_vector::PackedVector;

// Named constants instead of bare literals (readability-magic-numbers).
constexpr int64_t kSeed = 20261003;
constexpr int64_t kSeedStride = 7919;
constexpr int64_t kSeedStrideWords = 131;
constexpr int64_t kShortPattern = 40;
constexpr int64_t kExtraWidthA = 13;
constexpr int64_t kExtraWidthB = 37;
constexpr int64_t kTinyPoolMax = 12;
constexpr int64_t kSmallPoolMax = 13;
constexpr int64_t kWidthSwitchN = 4096;
constexpr int64_t kLargeN = 65536;
constexpr int64_t kHugeN = 150000;
constexpr int64_t kEighth = 8;
constexpr int64_t kSixteenth = 16;
constexpr int64_t kRunWidth = 3;
constexpr int64_t kSixStep = 6;
constexpr int64_t kProjectionStep = 5;
constexpr int64_t kMixStep = 200;
constexpr int64_t kSparseStep = 977;
constexpr int64_t kPermilleScale = 1000;
constexpr int64_t kSetStride = 3;
constexpr int64_t kSetPops = 5;
constexpr int64_t kBitVectorOps = 2000;
constexpr int64_t kRangeProbes = 2000;
constexpr int64_t kPackedArgScale = 100;
constexpr int64_t kPackedLen = 300;
constexpr int64_t kPackedProbes = 200;
constexpr int64_t kPackedPops = 50;
constexpr int64_t kInvalidWidth = 8;
constexpr int64_t kInvalidWidthPlusOne = 9;
constexpr int64_t kInvalidValue = 256;
constexpr int64_t kInvalidBits = 64;
constexpr int64_t kTooSmallWordBits = 3;

template <typename F>
bool throws(F&& f) {
    try {
        f();
    } catch (const std::exception&) {
        return true;
    }
    return false;
}

std::string to_bits(const std::vector<uint8_t>& bits) {
    std::string out;
    out.reserve(bits.size());
    for (uint8_t bit : bits) {
        out += bit != 0 ? '1' : '0';
    }
    return out;
}

std::string describe(std::string_view what, const std::vector<uint8_t>& bits, int64_t n_word_bits) {
    if (static_cast<int64_t>(bits.size()) <= kShortPattern) {
        return std::format("{} bits={} w={}", what, to_bits(bits), n_word_bits);
    }
    return std::format("{} size={} w={}", what, bits.size(), n_word_bits);
}

// Candidate word widths for n bits: the smallest legal one (every stored range
// is exactly one machine word), a few around it, and the full machine word.
std::vector<int64_t> widths_for(int64_t n) {
    int64_t min_w = std::max(ceil_log2(std::max(n, int64_t{1})), int64_t{1});
    std::vector<int64_t> widths{min_w};
    for (int64_t w : {min_w + 1, min_w + 2, kExtraWidthA, kExtraWidthB, n_machine_word_bits}) {
        if (w >= min_w && w <= n_machine_word_bits &&
            std::find(widths.begin(), widths.end(), w) == widths.end()) {
            widths.push_back(w);
        }
    }
    return widths;
}

template <typename Pred>
std::vector<uint8_t> make_pattern(int64_t n, Pred pred) {
    std::vector<uint8_t> bits(n);
    for (int64_t i = 0; i < n; i++) {
        bits[i] = pred(i) ? 1 : 0;
    }
    return bits;
}

// Brute-force reference for get/rank/select.
struct Reference {
    std::vector<uint8_t> bits;
    std::vector<int64_t> ones;
    std::vector<int64_t> prefix;

    explicit Reference(std::vector<uint8_t> input)
        : bits(std::move(input)), prefix(bits.size() + 1) {
        for (int64_t i = 0; i < static_cast<int64_t>(bits.size()); i++) {
            if (bits[i] != 0) {
                ones.push_back(i);
            }
            prefix[i + 1] = prefix[i] + (bits[i] != 0 ? 1 : 0);
        }
    }

    int64_t size() const { return static_cast<int64_t>(bits.size()); }
    int64_t count() const { return static_cast<int64_t>(ones.size()); }
    int64_t rank(int64_t index) const { return prefix[index]; }
    int64_t select(int64_t k) const { return ones[k]; }
};

void check_all(const std::vector<uint8_t>& bits, int64_t n_word_bits, std::string_view what,
    bool check_bounds = false) {
    Reference ref(bits);
    const std::string where = describe(what, bits, n_word_bits);
    auto cbv = CompactBitVector::create(
        bits.begin(), bits.end(), n_word_bits, [](uint8_t bit) { return bit != 0; });

    for (int64_t i = 0; i < ref.size(); i++) {
        bool expected = ref.bits[i] != 0;
        utest::assert_or_throw(cbv.get(i) == expected,
            std::format("{}: get({}) = {}, expected {}", where, i, cbv.get(i), expected));
    }
    for (int64_t i = 0; i <= ref.size(); i++) {
        int64_t actual = cbv.rank(i);
        utest::assert_or_throw(actual == ref.rank(i),
            std::format("{}: rank({}) = {}, expected {}", where, i, actual, ref.rank(i)));
    }
    for (int64_t k = 0; k < ref.count(); k++) {
        int64_t actual = cbv.select(k);
        utest::assert_or_throw(actual == ref.select(k),
            std::format("{}: select({}) = {}, expected {}", where, k, actual, ref.select(k)));
    }

    if (!check_bounds) {
        return;
    }
    utest::assert_or_throw(
        throws([&] { cbv.get(ref.size()); }), std::format("{}: get(size) must throw", where));
    utest::assert_or_throw(
        throws([&] { cbv.get(-1); }), std::format("{}: get(-1) must throw", where));
    utest::assert_or_throw(throws([&] { cbv.rank(ref.size() + 1); }),
        std::format("{}: rank(size + 1) must throw", where));
    utest::assert_or_throw(
        throws([&] { cbv.rank(-1); }), std::format("{}: rank(-1) must throw", where));
    utest::assert_or_throw(throws([&] { cbv.select(ref.count()); }),
        std::format("{}: select(count) must throw", where));
    utest::assert_or_throw(
        throws([&] { cbv.select(-1); }), std::format("{}: select(-1) must throw", where));
}

// ------------------------------------------------------------------ exhaustive

struct ExhaustiveParam {
    int64_t n_max;
    int64_t all_widths;
};

void exhaustive_test(ExhaustiveParam param) {
    for (int64_t n = 0; n <= param.n_max; n++) {
        std::vector<int64_t> candidates = widths_for(n);
        std::vector<int64_t> widths;
        if (param.all_widths != 0) {
            widths = candidates;
        } else {
            widths = {candidates.front(), candidates.back()};
        }
        for (uint64_t mask = 0; mask < (uint64_t{1} << n); mask++) {
            std::vector<uint8_t> bits(n);
            for (int64_t i = 0; i < n; i++) {
                bits[i] = (mask >> i) & 1;
            }
            for (int64_t w : widths) {
                check_all(bits, w, std::format("exhaustive n={}", n));
            }
        }
    }
}

auto exhaustive_small = utest::register_test([] {
    utest::test("compact_bit_vector", "exhaustive_all_widths", exhaustive_test,
        ExhaustiveParam{.n_max = kTinyPoolMax, .all_widths = 1});
});

auto exhaustive_large = utest::register_test([] {
    utest::test("compact_bit_vector", "exhaustive_two_widths", exhaustive_test,
        ExhaustiveParam{.n_max = kSmallPoolMax, .all_widths = 0});
});

// --------------------------------------------------------------- one-hot / one-cold

struct PositionsParam {
    int64_t n;
};

void single_one_test(PositionsParam param) {
    const int64_t n = param.n;
    std::vector<int64_t> widths = widths_for(n);
    for (int64_t p = 0; p < n; p++) {
        std::vector<uint8_t> bits(n, 0);
        bits[p] = 1;
        for (int64_t w : {widths.front(), widths.back()}) {
            check_all(bits, w, std::format("single_one n={} p={}", n, p));
        }
    }
}

void single_zero_test(PositionsParam param) {
    const int64_t n = param.n;
    std::vector<int64_t> widths = widths_for(n);
    for (int64_t p = 0; p < n; p++) {
        std::vector<uint8_t> bits(n, 1);
        bits[p] = 0;
        for (int64_t w : {widths.front(), widths.back()}) {
            check_all(bits, w, std::format("single_zero n={} p={}", n, p));
        }
    }
}

auto single_one = utest::register_test([] {
    for (int64_t n : {1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 17, 32, 64, 127, 257}) {
        utest::test("compact_bit_vector", "single_one", single_one_test, PositionsParam{.n = n});
    }
});

auto single_zero = utest::register_test([] {
    for (int64_t n : {1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 17, 32, 64, 127, 257}) {
        utest::test("compact_bit_vector", "single_zero", single_zero_test, PositionsParam{.n = n});
    }
});

// ------------------------------------------------------------------- structured

struct StructuredParam {
    int64_t n;
};

void structured_test(StructuredParam param) {
    const int64_t n = param.n;
    std::vector<std::pair<std::string, std::vector<uint8_t>>> patterns;
    patterns.emplace_back("zeros", make_pattern(n, [](int64_t) { return false; }));
    patterns.emplace_back("ones", make_pattern(n, [](int64_t) { return true; }));
    patterns.emplace_back("alt10", make_pattern(n, [](int64_t i) { return i % 2 == 0; }));
    patterns.emplace_back("alt01", make_pattern(n, [](int64_t i) { return i % 2 == 1; }));
    for (int64_t k : {int64_t{1}, int64_t{2}, int64_t{3}, int64_t{7}, kSixteenth, int64_t{64}}) {
        patterns.emplace_back(
            std::format("runs{}", k), make_pattern(n, [k](int64_t i) { return i % (2 * k) < k; }));
    }
    for (int64_t step : {int64_t{2}, kRunWidth, int64_t{17}, kMixStep, kSparseStep}) {
        patterns.emplace_back(std::format("step{}", step),
            make_pattern(n, [step](int64_t i) { return i % step == 0; }));
    }
    patterns.emplace_back("front", make_pattern(n, [n](int64_t i) { return i < (n / kEighth); }));
    patterns.emplace_back(
        "back", make_pattern(n, [n](int64_t i) { return i >= n - (n / kEighth); }));
    patterns.emplace_back(
        "wings", make_pattern(n, [n](int64_t i) { return i < (n / 4) || i >= n - (n / 4); }));
    patterns.emplace_back(
        "center", make_pattern(n, [n](int64_t i) { return i >= (n / 4) && i < n - (n / 4); }));
    patterns.emplace_back("mixed",
        make_pattern(n, [n](int64_t i) { return i < (n / 2) ? i % kMixStep == 0 : true; }));

    for (auto& [name, bits] : patterns) {
        for (int64_t w : widths_for(n)) {
            check_all(bits, w, std::format("structured {} n={}", name, n), true);
        }
    }
}

auto structured = utest::register_test([] {
    for (int64_t n : {1, 2, 3, 4, 5, 7, 8, 9, 16, 17, 63, 64, 65, 100, 256, 1000, 4097}) {
        utest::test("compact_bit_vector", "structured", structured_test, StructuredParam{.n = n});
    }
});

// ----------------------------------------------------------------------- random

struct RandomParam {
    int64_t n;
    int64_t permille;
    int64_t repeat;
};

void random_test(RandomParam param) {
    std::mt19937_64 gen(kSeed + (param.n * kSeedStride) + param.permille);
    std::vector<uint8_t> bits(param.n);
    std::vector<int64_t> candidates = widths_for(param.n);
    std::vector<int64_t> widths = param.n > kWidthSwitchN
                                      ? std::vector<int64_t>{candidates.front(), candidates.back()}
                                      : candidates;
    for (int64_t rep = 0; rep < param.repeat; rep++) {
        for (int64_t i = 0; i < param.n; i++) {
            bits[i] = static_cast<int64_t>(gen() % kPermilleScale) < param.permille ? 1 : 0;
        }
        for (int64_t w : widths) {
            check_all(bits, w,
                std::format("random n={} permille={} rep={}", param.n, param.permille, rep), true);
        }
    }
}

auto random_densities = utest::register_test([] {
    constexpr int64_t kNs[] = {1, 2, 3, 4, 5, 8, 16, 17, 32, 33, 64, 65, 128, 129, 256, 257, 512,
        513, 1024, 1025, kWidthSwitchN, kWidthSwitchN + 1, 12345};
    constexpr int64_t kPermille[] = {0, 1, 10, 100, 500, 900, 990, 1000};
    for (int64_t n : kNs) {
        for (int64_t permille : kPermille) {
            utest::test("compact_bit_vector", "random_densities", random_test,
                RandomParam{.n = n, .permille = permille, .repeat = 1});
        }
    }
});

// ------------------------------------------------------------------------ large
// Sizes far beyond a machine word: exercises many segments, wide (sparse) spans
// and mixed inputs.
void large_test(StructuredParam param) {
    const int64_t n = param.n;
    std::vector<std::pair<std::string, std::vector<uint8_t>>> patterns;
    patterns.emplace_back("ones", make_pattern(n, [](int64_t) { return true; }));
    patterns.emplace_back(
        "sparse", make_pattern(n, [](int64_t i) { return i % kSparseStep == 0; }));
    patterns.emplace_back("mixed", make_pattern(n, [n](int64_t i) {
        return i < (n / 2) ? i % kSparseStep == 0 : i % kRunWidth == 0;
    }));
    if (n <= kLargeN) {
        patterns.emplace_back(
            "runs3", make_pattern(n, [](int64_t i) { return i % kSixStep < kRunWidth; }));
        patterns.emplace_back(
            "back", make_pattern(n, [n](int64_t i) { return i >= n - (n / kSixteenth); }));
    }

    std::vector<int64_t> candidates = widths_for(n);
    for (auto& [name, bits] : patterns) {
        for (int64_t w : {candidates.front(), candidates.back()}) {
            check_all(bits, w, std::format("large {} n={}", name, n));
        }
    }
}

auto large = utest::register_test([] {
    for (int64_t n : {kLargeN, kHugeN}) {
        utest::test("compact_bit_vector", "large", large_test, StructuredParam{.n = n});
    }
});

// ------------------------------------------------------------------------ empty

void empty_test() {
    std::vector<uint8_t> bits;
    for (int64_t w : {int64_t{1}, kInvalidWidth, kExtraWidthA, n_machine_word_bits}) {
        auto cbv = CompactBitVector::create(
            bits.begin(), bits.end(), w, [](uint8_t bit) { return bit != 0; });
        utest::assert_or_throw(cbv.rank(0) == 0, "empty rank(0) must be 0");
        utest::assert_or_throw(throws([&] { cbv.get(0); }), "empty get(0) must throw");
        utest::assert_or_throw(throws([&] { cbv.rank(1); }), "empty rank(1) must throw");
        utest::assert_or_throw(throws([&] { cbv.select(0); }), "empty select(0) must throw");
    }
}

auto empty = utest::register_test(
    [] { utest::test("compact_bit_vector", "empty", [](int64_t) { empty_test(); }, int64_t{0}); });

// ------------------------------------------------------------------- projection

struct Item {
    int64_t value;
};

void projection_test(PositionsParam param) {
    const int64_t n = param.n;
    std::vector<uint8_t> bits = make_pattern(n, [](int64_t i) { return i % kProjectionStep == 0; });
    std::vector<Item> items(n);
    for (int64_t i = 0; i < n; i++) {
        items[i] = Item{.value = bits[i]};
    }

    Reference ref(bits);
    for (int64_t w : widths_for(n)) {
        auto cbv = CompactBitVector::create(
            items.begin(), items.end(), w, [](const Item& item) { return item.value != 0; });
        for (int64_t i = 0; i <= n; i++) {
            utest::assert_or_throw(cbv.rank(i) == ref.rank(i),
                std::format("projection rank({}) = {}, expected {}", i, cbv.rank(i), ref.rank(i)));
        }
        for (int64_t k = 0; k < ref.count(); k++) {
            utest::assert_or_throw(cbv.select(k) == ref.select(k),
                std::format(
                    "projection select({}) = {}, expected {}", k, cbv.select(k), ref.select(k)));
        }
    }
}

auto projection = utest::register_test([] {
    for (int64_t n : {1, 8, 33, 1000}) {
        utest::test("compact_bit_vector", "projection", projection_test, PositionsParam{.n = n});
    }
});

// -------------------------------------------------------- index-based placement

void placement_test(PositionsParam param) {
    const int64_t n = param.n;
    std::vector<uint8_t> bits = make_pattern(n, [](int64_t i) { return i % kProjectionStep == 0; });
    Reference ref(bits);
    for (int64_t w : widths_for(n)) {
        auto cbv = CompactBitVector::create(n, [&bits](int64_t i) { return bits[i] != 0; }, w);
        for (int64_t i = 0; i < n; i++) {
            utest::assert_or_throw(cbv.get(i) == (bits[i] != 0),
                std::format("placement get({}) = {}, expected {}", i, cbv.get(i), bits[i] != 0));
        }
        for (int64_t i = 0; i <= n; i++) {
            utest::assert_or_throw(cbv.rank(i) == ref.rank(i),
                std::format("placement rank({}) = {}, expected {}", i, cbv.rank(i), ref.rank(i)));
        }
        for (int64_t k = 0; k < ref.count(); k++) {
            utest::assert_or_throw(cbv.select(k) == ref.select(k),
                std::format(
                    "placement select({}) = {}, expected {}", k, cbv.select(k), ref.select(k)));
        }
    }

    // An empty result must never consult the placement.
    auto empty = CompactBitVector::create(
        0,
        [](int64_t) -> bool {
            utest::assert_or_throw(false, "placement called for size 0");
            return false;
        },
        kExtraWidthA);
    utest::assert_or_throw(empty.rank(0) == 0, "placement empty rank(0) must be 0");
    utest::assert_or_throw(
        throws([&] { CompactBitVector::create(-1, [](int64_t) { return false; }, kExtraWidthA); }),
        "negative size must throw");

    // The BitVector overload takes its size from the bit vector itself.
    auto raw = BitVector::create(kExtraWidthA);
    for (uint8_t bit : bits) {
        raw.push_back(bit != 0);
    }
    auto rebuilt = CompactBitVector::create(raw, kExtraWidthA);
    for (int64_t i = 0; i <= n; i++) {
        utest::assert_or_throw(rebuilt.rank(i) == ref.rank(i),
            std::format("bit vector rank({}) = {}, expected {}", i, rebuilt.rank(i), ref.rank(i)));
    }
    for (int64_t k = 0; k < ref.count(); k++) {
        utest::assert_or_throw(rebuilt.select(k) == ref.select(k),
            std::format(
                "bit vector select({}) = {}, expected {}", k, rebuilt.select(k), ref.select(k)));
    }
}

auto placement = utest::register_test([] {
    for (int64_t n : {1, 8, 33, 1000}) {
        utest::test("compact_bit_vector", "placement", placement_test, PositionsParam{.n = n});
    }
});

// ------------------------------------------------------ BitVector / PackedVector

void bit_vector_test(int64_t n_word_bits) {
    const int64_t w = n_word_bits;
    std::mt19937_64 gen(kSeed + (w * kSeedStrideWords));
    auto bv = BitVector::create(w);
    std::vector<uint8_t> ref;

    for (int64_t step = 0; step < kBitVectorOps; step++) {
        int64_t op = static_cast<int64_t>(gen() % 3);
        if (op == 0 || ref.empty()) {
            uint8_t bit = static_cast<uint8_t>(gen() & 1);
            bv.push_back(bit != 0);
            ref.push_back(bit);
        } else if (op == 1) {
            int64_t bits = static_cast<int64_t>(gen() % (w + 1));
            uint64_t value = 0;
            if (bits > 0) {
                value = bits == n_machine_word_bits ? gen() : gen() & ((uint64_t{1} << bits) - 1);
            }
            bv.push_back_range(value, bits);
            for (int64_t j = 0; j < bits; j++) {
                ref.push_back(static_cast<uint8_t>((value >> j) & 1));
            }
        } else {
            bv.pop_back();
            ref.pop_back();
        }
        utest::assert_or_throw(bv.size_ == static_cast<int64_t>(ref.size()),
            std::format("w={}: size {} != {}", w, bv.size_, ref.size()));
    }

    for (int64_t i = 0; i < static_cast<int64_t>(ref.size()); i++) {
        utest::assert_or_throw(bv.get(i) == (ref[i] != 0),
            std::format("w={}: get({}) = {}, expected {}", w, i, bv.get(i), ref[i] != 0));
    }

    for (int64_t probe = 0; probe < kRangeProbes; probe++) {
        int64_t l = static_cast<int64_t>(gen() % (ref.size() + 1));
        int64_t max_len = std::min<int64_t>(w, static_cast<int64_t>(ref.size()) - l);
        int64_t len = max_len == 0 ? 0 : static_cast<int64_t>(gen() % (max_len + 1));
        uint64_t expected = 0;
        for (int64_t j = 0; j < len; j++) {
            expected |= uint64_t{ref[l + j]} << j;
        }
        uint64_t actual = bv.get_range(l, l + len);
        utest::assert_or_throw(
            actual == expected, std::format("w={}: get_range({}, {}) = {}, expected {}", w, l,
                                    l + len, actual, expected));
    }

    // set()/pop_back_range() must stay consistent with the plain-bits model.
    for (int64_t i = 0; i < static_cast<int64_t>(ref.size()); i += kSetStride) {
        bv.set(i, true);
        ref[i] = 1;
        utest::assert_or_throw(bv.get(i), std::format("w={}: set({}) failed", w, i));
    }
    for (int64_t j = 0; j < kSetPops && bv.size_ > 0; j++) {
        int64_t bits = std::min<int64_t>(w, bv.size_);
        int64_t r = bv.size_;
        bv.pop_back_range(bits);
        utest::assert_or_throw(bv.size_ == r - bits, std::format("w={}: pop_back_range", w));
    }
}

auto bit_vector = utest::register_test([] {
    for (int64_t w : {int64_t{1}, int64_t{2}, int64_t{3}, int64_t{5}, int64_t{7}, kInvalidWidth,
             kExtraWidthA, int64_t{32}, kExtraWidthB, n_machine_word_bits}) {
        utest::test("compact_bit_vector", "bit_vector", [](int64_t x) { bit_vector_test(x); }, w);
    }
});

void packed_vector_test(int64_t arg) {
    const int64_t n_word_bits = arg / kPackedArgScale;
    const int64_t element_bits = arg % kPackedArgScale;
    std::mt19937_64 gen(kSeed + (n_word_bits * kSeedStrideWords) + element_bits);
    uint64_t mask =
        element_bits == n_machine_word_bits ? ~uint64_t{0} : (uint64_t{1} << element_bits) - 1;
    auto pv = PackedVector::create(element_bits, n_word_bits);
    std::vector<uint64_t> ref;
    for (int64_t i = 0; i < kPackedLen; i++) {
        uint64_t value = gen() & mask;
        pv.push_back(value);
        ref.push_back(value);
    }
    utest::assert_or_throw(
        pv.size() == static_cast<int64_t>(ref.size()), "PackedVector::size mismatch");
    for (int64_t i = 0; i < static_cast<int64_t>(ref.size()); i++) {
        utest::assert_or_throw(pv.get(i) == ref[i], std::format("packed get({})", i));
    }
    for (int64_t probe = 0; probe < kPackedProbes; probe++) {
        int64_t i = static_cast<int64_t>(gen() % ref.size());
        uint64_t value = gen() & mask;
        pv.set(i, value);
        ref[i] = value;
        utest::assert_or_throw(pv.get(i) == value, std::format("packed set({})", i));
    }
    for (int64_t i = 0; i < kPackedPops; i++) {
        pv.pop_back();
        ref.pop_back();
    }
    utest::assert_or_throw(pv.size() == static_cast<int64_t>(ref.size()), "packed pop_back");
    for (int64_t i = 0; i < static_cast<int64_t>(ref.size()); i++) {
        utest::assert_or_throw(pv.get(i) == ref[i], std::format("packed get({}) after pop", i));
    }
}

auto packed_vector = utest::register_test([] {
    for (int64_t w : {int64_t{1}, int64_t{2}, int64_t{3}, kInvalidWidth, kExtraWidthA, int64_t{32},
             n_machine_word_bits}) {
        for (int64_t element_bits : {int64_t{1}, w / 2, w}) {
            if (element_bits < 1) {
                continue;
            }
            utest::test(
                "compact_bit_vector", "packed_vector", [](int64_t x) { packed_vector_test(x); },
                (w * kPackedArgScale) + element_bits);
        }
    }
});

// ------------------------------------------------------------ invalid arguments

void invalid_test() {
    std::vector<uint8_t> bits(kInvalidBits, 1);
    utest::assert_or_throw(throws([] { BitVector::create(0); }), "create(0) must throw");
    utest::assert_or_throw(
        throws([] { BitVector::create(n_machine_word_bits + 1); }), "create(word + 1) must throw");
    utest::assert_or_throw(
        throws([] { PackedVector::create(0, kInvalidWidth); }), "width 0 must throw");
    utest::assert_or_throw(
        throws([] { PackedVector::create(kInvalidWidthPlusOne, kInvalidWidth); }),
        "width > word must throw");
    utest::assert_or_throw(throws([] { (void)ceil_log2(0); }), "ceil_log2(0) must throw");
    // n_word_bits must fit ceil_log2(size).
    utest::assert_or_throw(
        throws([&] { CompactBitVector::create(bits.begin(), bits.end(), kTooSmallWordBits); }),
        "too small n_word_bits must throw");
    // get/set out of range.
    auto bv = BitVector::create(kInvalidWidth);
    bv.push_back(true);
    utest::assert_or_throw(throws([&] { bv.get(1); }), "get past end must throw");
    utest::assert_or_throw(throws([&] { bv.set(-1, true); }), "set(-1) must throw");
    utest::assert_or_throw(throws([&] { bv.push_back_range(0, kInvalidWidthPlusOne); }),
        "push_back_range too wide must throw");
    utest::assert_or_throw(throws([&] { bv.set_range(0, kInvalidWidth, kInvalidValue); }),
        "value too wide must throw");
}

auto invalid = utest::register_test([] {
    utest::test("compact_bit_vector", "invalid", [](int64_t) { invalid_test(); }, int64_t{0});
});
}  // namespace
