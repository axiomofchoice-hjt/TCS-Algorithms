#pragma once

#include <charconv>
#include <cstdint>
#include <cstring>
#include <format>
#include <functional>
#include <print>
#include <ranges>
#include <source_location>
#include <stdexcept>
#include <string>
#include <string_view>

namespace utest {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

struct TestCase {
    std::string suite;
    std::string name;
    std::vector<int64_t> params;
    std::function<void()> func;
};

struct TestRegistry {
   public:
    static TestRegistry& instance() {
        static TestRegistry reg;
        return reg;
    }
    void add_test(TestCase tc) { tests_.push_back(std::move(tc)); }
    const std::vector<TestCase>& tests() const { return tests_; }

   private:
    std::vector<TestCase> tests_;
};

template <typename Func, typename T>
inline void test(std::string suite, std::string name, Func func, T params) {
    std::vector<int64_t> params_(sizeof(T) / sizeof(int64_t), 0);
    std::memcpy(params_.data(), &params, sizeof(T));
    TestRegistry::instance().add_test(
        {std::move(suite), std::move(name), params_, [=] { func(params); }});
}

template <typename Func>
inline int register_test(Func func) {
    func();
    return 0;
};

using Interval = std::pair<int64_t, int64_t>;

inline std::vector<Interval> parse_param_spec(std::string_view spec) {
    std::vector<Interval> intervals;
    for (auto part : spec | std::views::split(',')) {
        auto sv = std::string_view(part.begin(), part.end());
        if (auto dash = sv.find('-'); dash != std::string_view::npos) {
            auto lo_sv = sv.substr(0, dash);
            auto hi_sv = sv.substr(dash + 1);
            if (lo_sv.empty() && hi_sv.empty()) {
                intervals.emplace_back(INT64_MIN, INT64_MAX);
            } else {
                int64_t lo = INT64_MIN;
                int64_t hi = INT64_MAX;
                if (!lo_sv.empty()) {
                    std::from_chars(lo_sv.data(), lo_sv.data() + lo_sv.size(), lo);
                }
                if (!hi_sv.empty()) {
                    std::from_chars(hi_sv.data(), hi_sv.data() + hi_sv.size(), hi);
                }
                intervals.emplace_back(lo, hi);
            }
        } else {
            int64_t v;
            std::from_chars(sv.data(), sv.data() + sv.size(), v);
            intervals.emplace_back(v, v);
        }
    }
    return intervals;
}

inline bool interval_matches(int64_t value, const std::vector<Interval>& intervals) {
    for (const auto& [lo, hi] : intervals) {
        if (value >= lo && value <= hi) {
            return true;
        }
    }
    return false;
}

struct CliOptions {
    std::string filter;
    std::vector<std::vector<Interval>> param_specs;

    static CliOptions parse(int argc, char* argv[]) {
        CliOptions opts;
        for (int i = 1; i < argc; i++) {
            std::string_view arg(argv[i]);
            if (arg == "--filter" && i + 1 < argc) {
                opts.filter = argv[++i];
            } else if (arg == "--params") {
                while (i + 1 < argc && !std::string_view(argv[i + 1]).starts_with("--")) {
                    opts.param_specs.emplace_back(parse_param_spec(argv[++i]));
                }
            }
        }
        return opts;
    }

    bool match(const TestCase& tc) const {
        auto full_name = std::format("{}.{}", tc.suite, tc.name);
        if (!filter.empty() && !full_name.contains(filter)) {
            return false;
        }
        if (!param_specs.empty() &&
            static_cast<int64_t>(param_specs.size()) != static_cast<int64_t>(tc.params.size())) {
            std::println("Warning: {} param count mismatch (expected {}, got {})", full_name,
                tc.params.size(), param_specs.size());
            return false;
        }
        for (int64_t j = 0; j < static_cast<int64_t>(param_specs.size()); j++) {
            if (!interval_matches(tc.params[j], param_specs[j])) {
                return false;
            }
        }
        return true;
    }
};

inline int run(int argc, char* argv[]) {
    auto opts = CliOptions::parse(argc, argv);
    int64_t total = 0;
    int64_t failed = 0;
    for (const auto& tc : TestRegistry::instance().tests()) {
        if (!opts.match(tc)) {
            continue;
        }
        total++;
        try {
            tc.func();
        } catch (const std::exception& e) {
            std::string params_str;
            for (int64_t i = 0; i < static_cast<int64_t>(tc.params.size()); i++) {
                params_str += (i > 0 ? ", " : "") + std::to_string(tc.params[i]);
            }
            std::println("Test {}.{} [{}] failed: {}", tc.suite, tc.name, params_str, e.what());
            failed++;
        }
    }
    std::println("{} passed, {} failed", total - failed, failed);
    return failed > 0 ? 1 : 0;
}
}  // namespace utest
