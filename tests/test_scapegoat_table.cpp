#include <random>
#include <set>
#include <vector>

#include "common/utest.hpp"
#include "tcs/ds/scapegoat_table.hpp"

namespace {
constexpr int kRandomSeed = 42;
constexpr int64_t kSweepMaxN = 100;
constexpr int64_t kKeyMin = 1;
constexpr int64_t kInsertFraction = 2;

constexpr int64_t kSweepMaxKey = 200;
constexpr int64_t kDuplicateN = 200;
constexpr int64_t kDuplicateMaxKey = 50;
constexpr int64_t kDuplicateRepeat = 10;
constexpr int64_t kOrderedN = 500;
constexpr int64_t kReverseN = 5000;
constexpr int64_t kInvariantMaxKey = 200;
constexpr int64_t kInvariantRepeat = 5;
constexpr int64_t kProjectionNQueries = 200;
constexpr int64_t kProjectionMaxKey = 100;
constexpr int64_t kProjectionRepeat = 5;

struct TestParam {
    int64_t n_queries;
    int64_t max_key;
    int64_t repeat;
};

constexpr TestParam kCases[] = {
    {10, 10, 100},
    {50, 20, 50},
    {100, 30, 20},
    {200, 50, 10},
    {500, 100, 5},
    {1000, 200, 3},
    {2000, 500, 2},
    {5000, 1000, 1},
};

void random_test(TestParam param) {
    std::mt19937 gen(kRandomSeed);
    std::uniform_int_distribution<int64_t> key_dist(kKeyMin, param.max_key);

    for (int64_t rep = 0; rep < param.repeat; rep++) {
        tcs::ds::scapegoat_table::ScapegoatTable<int64_t> table;
        std::set<int64_t> inserted;

        int64_t n_insert = param.max_key / kInsertFraction;
        while (static_cast<int64_t>(inserted.size()) < n_insert) {
            inserted.insert(key_dist(gen));
        }
        for (int64_t key : inserted) {
            table.insert(key);
        }

        for (int64_t i = 0; i < param.n_queries; i++) {
            int64_t query = key_dist(gen);

            bool expected_contains = inserted.contains(query);
            utest::assert_or_throw(table.contains(query) == expected_contains,
                std::format("contains({}) expected {}", query, expected_contains));

            auto lb = table.lower_bound(query);
            auto expected_lb = inserted.lower_bound(query);
            if (expected_lb == inserted.end()) {
                utest::assert_or_throw(
                    !lb.has_value(), std::format("lower_bound({}) should be nullopt", query));
            } else {
                utest::assert_or_throw(lb.has_value() && *lb == *expected_lb,
                    std::format("lower_bound({}) = {}, expected {}", query, *lb, *expected_lb));
            }
        }
    }
}

auto random_cases = utest::register_test([] {
    for (const auto& param : kCases) {
        utest::test("scapegoat_table", "kCases", random_test, param);
    }
});

void sweep_test(TestParam param) {
    for (int64_t n = 1; n <= param.n_queries; n++) {
        tcs::ds::scapegoat_table::ScapegoatTable<int64_t> table;
        std::mt19937 gen(kRandomSeed + n);
        std::uniform_int_distribution<int64_t> key_dist(kKeyMin, param.max_key);
        std::set<int64_t> expected;

        for (int64_t i = 0; i < n; i++) {
            int64_t key = key_dist(gen);
            table.insert(key);
            expected.insert(key);
        }

        for (auto it = expected.begin(); it != expected.end(); ++it) {
            utest::assert_or_throw(table.contains(*it));
        }
    }
}

auto sweep = utest::register_test([] {
    utest::test("scapegoat_table", "sweep", sweep_test,
        TestParam{.n_queries = kSweepMaxN, .max_key = kSweepMaxKey, .repeat = 1});
});

void duplicate_test(TestParam param) {
    for (int64_t rep = 0; rep < param.repeat; rep++) {
        tcs::ds::scapegoat_table::ScapegoatTable<int64_t> table;
        std::mt19937 gen(kRandomSeed + rep);
        std::uniform_int_distribution<int64_t> key_dist(kKeyMin, param.max_key);
        std::set<int64_t> expected;

        for (int64_t i = 0; i < param.n_queries; i++) {
            int64_t key = key_dist(gen);
            table.insert(key);
            expected.insert(key);
        }

        for (int64_t key : expected) {
            table.insert(key);
            utest::assert_or_throw(table.contains(key));
        }

        for (int64_t key : expected) {
            auto lb = table.lower_bound(key);
            utest::assert_or_throw(lb.has_value() && *lb == key);
        }
    }
}

auto duplicates = utest::register_test([] {
    utest::test("scapegoat_table", "duplicates", duplicate_test,
        TestParam{
            .n_queries = kDuplicateN, .max_key = kDuplicateMaxKey, .repeat = kDuplicateRepeat});
});

void ordered_insert_test(TestParam param) {
    for (int64_t rep = 0; rep < param.repeat; rep++) {
        tcs::ds::scapegoat_table::ScapegoatTable<int64_t> table;
        for (int64_t i = 0; i < param.n_queries; i++) {
            table.insert(i);
        }
        for (int64_t i = 0; i < param.n_queries; i++) {
            utest::assert_or_throw(table.contains(i));
            auto lb = table.lower_bound(i);
            utest::assert_or_throw(lb.has_value() && *lb == i);
        }
        auto lb = table.lower_bound(param.n_queries);
        utest::assert_or_throw(!lb.has_value());
    }
}

auto ordered = utest::register_test([] {
    utest::test("scapegoat_table", "ordered", ordered_insert_test,
        TestParam{.n_queries = kOrderedN, .max_key = 0, .repeat = 1});
});

void reverse_insert_test(TestParam param) {
    for (int64_t rep = 0; rep < param.repeat; rep++) {
        tcs::ds::scapegoat_table::ScapegoatTable<int64_t> table;
        for (int64_t i = param.n_queries - 1; i >= 0; i--) {
            table.insert(i);
        }
        for (int64_t i = 0; i < param.n_queries; i++) {
            utest::assert_or_throw(table.contains(i));
        }
    }
}

auto reverse = utest::register_test([] {
    utest::test("scapegoat_table", "reverse", reverse_insert_test,
        TestParam{.n_queries = kReverseN, .max_key = 0, .repeat = 1});
});

void empty_test() {
    tcs::ds::scapegoat_table::ScapegoatTable<int64_t> table;
    utest::assert_or_throw(!table.contains(0));
    utest::assert_or_throw(!table.lower_bound(0).has_value());
}

auto empty = utest::register_test(
    [] { utest::test("scapegoat_table", "empty", [](TestParam) { empty_test(); }, TestParam{}); });

void counts_invariant_test(TestParam param) {
    for (int64_t rep = 0; rep < param.repeat; rep++) {
        tcs::ds::scapegoat_table::ScapegoatTable<int64_t> table;
        std::mt19937 gen(kRandomSeed + rep);
        std::uniform_int_distribution<int64_t> key_dist(kKeyMin, param.max_key);
        std::set<int64_t> inserted;

        int64_t n_insert = param.max_key / kInsertFraction;
        while (static_cast<int64_t>(inserted.size()) < n_insert) {
            inserted.insert(key_dist(gen));
        }
        for (int64_t key : inserted) {
            table.insert(key);
            int64_t actual = static_cast<int64_t>(table.genuine_keys(0, table.n_blocks_).size());
            utest::assert_or_throw(table.counts_[1] == actual,
                std::format("counts_[1] = {} but genuine_keys = {}", table.counts_[1], actual));
            utest::assert_or_throw(
                std::ranges::is_sorted(table.data_, {}, table.proj_), "data_ is not sorted");
        }
    }
}

auto counts_invariant = utest::register_test([] {
    utest::test("scapegoat_table", "counts_invariant", counts_invariant_test,
        TestParam{.n_queries = 0, .max_key = kInvariantMaxKey, .repeat = kInvariantRepeat});
});

struct KeyedValue {
    int64_t key;
};

void projection_test(TestParam param) {
    auto proj = [](const KeyedValue& x) { return x.key; };
    tcs::ds::scapegoat_table::ScapegoatTable<KeyedValue, decltype(proj)> table;
    std::set<int64_t> inserted;
    std::mt19937 gen(kRandomSeed);
    std::uniform_int_distribution<int64_t> key_dist(kKeyMin, param.max_key);

    int64_t n_insert = param.max_key / kInsertFraction;
    while (static_cast<int64_t>(inserted.size()) < n_insert) {
        inserted.insert(key_dist(gen));
    }
    for (int64_t key : inserted) {
        table.insert(KeyedValue{key});
    }

    for (int64_t i = 0; i < param.n_queries; i++) {
        int64_t query = key_dist(gen);
        bool expected = inserted.contains(query);
        utest::assert_or_throw(table.contains(KeyedValue{query}) == expected,
            std::format("projection contains({}) expected {}", query, expected));

        auto lb = table.lower_bound(KeyedValue{query});
        auto expected_lb = inserted.lower_bound(query);
        if (expected_lb == inserted.end()) {
            utest::assert_or_throw(!lb.has_value());
        } else {
            utest::assert_or_throw(lb.has_value() && lb->key == *expected_lb);
        }
    }
}

auto projection = utest::register_test([] {
    utest::test("scapegoat_table", "projection", projection_test,
        TestParam{.n_queries = kProjectionNQueries,
            .max_key = kProjectionMaxKey,
            .repeat = kProjectionRepeat});
});
}  // namespace
