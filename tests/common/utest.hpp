#pragma once

#include <algorithm>
#include <charconv>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <format>
#include <functional>
#include <limits>
#include <map>
#include <optional>
#include <print>
#include <ranges>
#include <source_location>
#include <stdexcept>
#include <string>
#include <string_view>
#include <system_error>
#include <type_traits>
#include <utility>
#include <vector>

namespace utest {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

// Like assert_or_throw, but `message` is a callable invoked only on failure, so
// hot loops do not format a message on the passing path.
template <typename Message>
inline void assert_or_throw_lazy(bool condition, Message&& message,
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message()));
    }
}

struct TestCase {
    std::string suite;
    std::string name;
    std::string file;  // test file that registered this case
    int64_t line = 0;
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

// Copies `params` verbatim into 8-byte words so --params can range-check each
// field (pass flat, word-sized-viewable types such as int64_t or structs of
// them). Ceil division: a type smaller than int64_t still gets one word, where
// the old `sizeof(T) / sizeof(int64_t)` produced an empty vector and then
// memcpy'd `sizeof(T)` bytes into it -- undefined behaviour. No caller passed
// such a type, so that bug was latent; the ceil division keeps it fixed.
//
// Contract: T must be trivially copyable and free of padding, because the
// object representation is compared word by word in memory order (the words
// are not endianness-corrected). Words beyond sizeof(T) stay zero, so a
// negative sub-word value (e.g. an int32_t) does not match a negative spec.
template <typename T>
inline std::vector<int64_t> pack_params(const T& params) {
    static_assert(std::is_trivially_copyable_v<T>, "test params must be trivially copyable");
    constexpr std::size_t kWords = (sizeof(T) + sizeof(int64_t) - 1) / sizeof(int64_t);
    std::vector<int64_t> words(kWords, 0);
    std::memcpy(words.data(), &params, sizeof(T));
    return words;
}

template <typename Func, typename T>
inline void test(std::string suite, std::string name, Func func, T params,
    const std::source_location& loc = std::source_location::current()) {
    TestRegistry::instance().add_test({std::move(suite), std::move(name), loc.file_name(),
        static_cast<int64_t>(loc.line()), pack_params(params), [=] { func(params); }});
}

// Overload for tests that need no parameter, so there is no need to invent a
// dummy `int64_t{0}` argument.
template <typename Func>
inline void test(std::string suite, std::string name, Func func,
    const std::source_location& loc = std::source_location::current()) {
    TestRegistry::instance().add_test({std::move(suite), std::move(name), loc.file_name(),
        static_cast<int64_t>(loc.line()), {}, [func = std::move(func)] { func(); }});
}

template <typename Func>
inline int register_test(Func func) {
    func();
    return 0;
};

using Interval = std::pair<int64_t, int64_t>;

// Strict: the whole field must be consumed, so "12x" or "1-2-3" is rejected
// instead of being silently truncated by from_chars.
inline bool parse_int64(std::string_view sv, int64_t& out) {
    if (sv.empty()) {
        return false;
    }
    const char* first = sv.data();
    const char* last = sv.data() + sv.size();
    auto [ptr, ec] = std::from_chars(first, last, out);
    return ec == std::errc() && ptr == last;
}

// Parses one --params spec: a comma-separated list of the intervals
// N | LO-HI | LO- | -HI | -. Returns nullopt for an empty or malformed spec so
// the caller can reject it with a usage error; a mistyped spec used to fall
// through to [0, 0] (or [MIN, MAX]) and silently select the wrong subset.
inline std::optional<std::vector<Interval>> parse_param_spec(std::string_view spec) {
    if (spec.empty()) {
        return std::nullopt;
    }
    std::vector<Interval> intervals;
    for (auto part : spec | std::views::split(',')) {
        auto sv = std::string_view(part.begin(), part.end());
        if (auto dash = sv.find('-'); dash != std::string_view::npos) {
            auto lo_sv = sv.substr(0, dash);
            auto hi_sv = sv.substr(dash + 1);
            int64_t lo = std::numeric_limits<int64_t>::min();
            int64_t hi = std::numeric_limits<int64_t>::max();
            if (!lo_sv.empty() && !parse_int64(lo_sv, lo)) {
                return std::nullopt;
            }
            if (!hi_sv.empty() && !parse_int64(hi_sv, hi)) {
                return std::nullopt;
            }
            intervals.emplace_back(lo, hi);
        } else {
            int64_t v = 0;
            if (!parse_int64(sv, v)) {
                return std::nullopt;
            }
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
    // How a test case relates to the command-line selection.
    enum class Selection {
        kSelected,       // the filter and every parameter spec match
        kParamMismatch,  // the filter matches, but the packed parameter count differs
        kRejected,       // the filter or a parameter value does not match
    };

    std::string filter;
    std::vector<std::vector<Interval>> param_specs;
    bool list = false;
    bool time = false;
    bool help = false;
    std::string error;  // first invalid command-line argument, if any

    static CliOptions parse(int argc, char* argv[]) {
        CliOptions opts;
        auto reject = [&opts](std::string message) {
            if (opts.error.empty()) {
                opts.error = std::move(message);
            }
        };
        for (int i = 1; i < argc; i++) {
            std::string_view arg(argv[i]);
            // Accept both "--filter X" and "--filter=X".
            std::string_view option = arg;
            std::string_view inline_value;
            bool has_inline_value = false;
            if (arg.starts_with("--")) {
                if (auto eq = arg.find('='); eq != std::string_view::npos) {
                    option = arg.substr(0, eq);
                    inline_value = arg.substr(eq + 1);
                    has_inline_value = true;
                }
            }
            // The inline value, else the next argument, else nothing (the caller
            // reports the missing value). A following option is never swallowed
            // as a value, so `--filter --list` reports the missing value instead
            // of silently filtering on the literal string "--list".
            auto next_value = [&]() -> std::optional<std::string_view> {
                if (has_inline_value) {
                    return inline_value;
                }
                if (i + 1 < argc && !std::string_view(argv[i + 1]).starts_with("--")) {
                    return std::string_view(argv[++i]);
                }
                return std::nullopt;
            };
            auto reject_value = [&](std::string_view name) {
                reject(std::format("option '{}' takes no value", name));
            };
            // Records the first malformed spec and leaves the selection empty,
            // so a typo cannot silently select the wrong subset.
            auto add_param_spec = [&](std::string_view spec) {
                auto parsed = parse_param_spec(spec);
                if (!parsed) {
                    reject(std::format("invalid --params spec '{}'", spec));
                    return;
                }
                opts.param_specs.push_back(std::move(*parsed));
            };
            if (option == "--filter") {
                auto value = next_value();
                if (!value || value->empty()) {
                    // An empty filter matches everything, which is the same
                    // false green as silently running the whole suite.
                    reject("option '--filter' requires a non-empty value");
                    continue;
                }
                opts.filter = *value;
            } else if (option == "--params") {
                const std::size_t before = opts.param_specs.size();
                if (has_inline_value) {
                    add_param_spec(inline_value);
                }
                while (i + 1 < argc && !std::string_view(argv[i + 1]).starts_with("--")) {
                    add_param_spec(argv[++i]);
                }
                if (opts.param_specs.size() == before) {
                    reject("option '--params' requires at least one valid spec");
                }
            } else if (option == "--list") {
                if (has_inline_value) {
                    reject_value("--list");
                }
                opts.list = true;
            } else if (option == "--time") {
                if (has_inline_value) {
                    reject_value("--time");
                }
                opts.time = true;
            } else if (option == "--help" || option == "-h") {
                if (has_inline_value) {
                    reject_value(option);
                }
                opts.help = true;
            } else if (!arg.empty() && arg.front() == '-') {
                reject(std::format("unknown option '{}'", arg));
            } else {
                // Silently running the whole suite on a mistyped positional
                // filter is exactly the false green this harness avoids.
                reject(std::format("unexpected argument '{}'", arg));
            }
        }
        return opts;
    }

    bool matches_filter(const TestCase& tc) const {
        return filter.empty() || std::format("{}.{}", tc.suite, tc.name).contains(filter);
    }

    bool param_count_matches(const TestCase& tc) const {
        return param_specs.empty() || param_specs.size() == tc.params.size();
    }

    // Precondition: param_count_matches(tc).
    bool param_values_match(const TestCase& tc) const {
        for (std::size_t j = 0; j < param_specs.size(); j++) {
            if (!interval_matches(tc.params[j], param_specs[j])) {
                return false;
            }
        }
        return true;
    }

    Selection select(const TestCase& tc) const {
        if (!matches_filter(tc)) {
            return Selection::kRejected;
        }
        if (!param_count_matches(tc)) {
            return Selection::kParamMismatch;
        }
        return param_values_match(tc) ? Selection::kSelected : Selection::kRejected;
    }
};

inline std::string format_params(const std::vector<int64_t>& params) {
    std::string out;
    for (std::size_t i = 0; i < params.size(); i++) {
        out += (i == 0 ? "" : ", ") + std::to_string(params[i]);
    }
    return out;
}

// One aggregated line instead of one warning per non-matching test.
inline void print_param_skipped(int64_t skipped, std::size_t expected_words) {
    if (skipped > 0) {
        std::println(
            "utest: skipped {} test(s) whose parameter count != {}", skipped, expected_words);
    }
}

// AGENTS.md caps every algorithm's test file at this budget in a debug build
// that does not define TCS_NO_TEMP_IMPL. Keep this value in sync with the
// 测试运行时间上限 section of AGENTS.md. --time enforces the budget on the
// per-file totals it prints and exits with kOverBudget when one exceeds it.
inline constexpr double kFileBudgetSeconds = 1.0;

// The budget only describes the configuration AGENTS.md names. A release build
// (NDEBUG) or one using the true in-place primitives is a different measurement,
// so --time still prints the table there but does not fail the run: otherwise a
// fast release build would silently certify a budget that only the debug build
// is required to meet.
#if defined(NDEBUG) || defined(TCS_NO_TEMP_IMPL)
inline constexpr bool kBudgetConfig = false;
#else
inline constexpr bool kBudgetConfig = true;
#endif

// Exit statuses of run(). Plain ints (not an enum) so they format directly.
inline constexpr int kOk = 0;
inline constexpr int kTestFailed = 1;
inline constexpr int kBadUsage = 2;
inline constexpr int kNothingSelected = 3;
inline constexpr int kOverBudget = 4;

inline void print_usage(std::FILE* out, std::string_view program) {
    std::println(out, "usage: {} [options]", program);
    std::println(
        out, "  --filter <substring>  only run tests whose suite.name contains <substring>");
    std::println(out, "  --params <spec> ...   only run tests whose i-th packed parameter matches");
    std::println(out,
        "                        the i-th <spec>: N | LO-HI | LO- | -HI | - (comma separated)");
    std::println(out, "  --list                list the matching tests instead of running them");
    std::println(out,
        "  --time                print per-file timing and enforce the {:.1f}s/file budget",
        kFileBudgetSeconds);
    std::println(out, "  --help, -h            print this help and exit");
    std::println(out,
        "exit status: {} ok, {} test failure, {} bad command line, {} nothing selected,", kOk,
        kTestFailed, kBadUsage, kNothingSelected);
    std::println(out, "             {} a file was over the {:.1f}s budget (debug builds without",
        kOverBudget, kFileBudgetSeconds);
    std::println(out, "             TCS_NO_TEMP_IMPL only)");
}

struct FileStats {
    int64_t cases = 0;
    int64_t failed = 0;
    double total_ms = 0;
    double max_ms = 0;

    double total_seconds() const { return total_ms / 1000; }
    bool over_budget() const { return total_seconds() > kFileBudgetSeconds; }
};

inline int run(int argc, char* argv[]) {
    auto opts = CliOptions::parse(argc, argv);
    if (!opts.error.empty()) {
        std::println(stderr, "utest: {}", opts.error);
        print_usage(stderr, argv[0]);
        return kBadUsage;
    }
    if (opts.help) {
        print_usage(stdout, argv[0]);
        return kOk;
    }

    const auto& tests = TestRegistry::instance().tests();

    if (opts.list) {
        int64_t listed = 0;
        int64_t param_skipped = 0;
        for (const auto& tc : tests) {
            const auto selection = opts.select(tc);
            if (selection == CliOptions::Selection::kParamMismatch) {
                param_skipped++;
                continue;
            }
            if (selection != CliOptions::Selection::kSelected) {
                continue;
            }
            std::println(
                "{}.{} [{}]  {}:{}", tc.suite, tc.name, format_params(tc.params), tc.file, tc.line);
            listed++;
        }
        print_param_skipped(param_skipped, opts.param_specs.size());
        std::println("{} test(s) listed", listed);
        return listed > 0 ? kOk : kNothingSelected;
    }

    int64_t total = 0;
    int64_t failed = 0;
    int64_t param_skipped = 0;
    std::map<std::string, FileStats> stats;

    for (const auto& tc : tests) {
        const auto selection = opts.select(tc);
        if (selection == CliOptions::Selection::kParamMismatch) {
            param_skipped++;
            continue;
        }
        if (selection != CliOptions::Selection::kSelected) {
            continue;
        }
        total++;
        FileStats* stat = opts.time ? &stats[tc.file] : nullptr;
        const bool timing = stat != nullptr;
        const auto start =
            timing ? std::chrono::steady_clock::now() : std::chrono::steady_clock::time_point{};
        bool ok = true;
        std::string failure;
        try {
            tc.func();
        } catch (const std::exception& e) {
            failure = e.what();
            ok = false;
        } catch (...) {
            failure = "unknown exception";
            ok = false;
        }
        // Measured before the failure line is printed, so a slow terminal does
        // not inflate the reported time.
        double ms = 0.0;
        if (timing) {
            const auto elapsed = std::chrono::steady_clock::now() - start;
            ms = std::chrono::duration<double, std::milli>(elapsed).count();
        }
        if (!ok) {
            std::println(
                "Test {}.{} [{}] failed: {}", tc.suite, tc.name, format_params(tc.params), failure);
            failed++;
        }
        if (stat != nullptr) {
            stat->cases++;
            stat->failed += ok ? 0 : 1;
            stat->total_ms += ms;
            stat->max_ms = std::max(stat->max_ms, ms);
        }
    }

    print_param_skipped(param_skipped, opts.param_specs.size());

    if (total == 0) {
        std::fflush(stdout);  // keep the diagnostic after the stdout notes in merged logs
        std::println(stderr, "utest: no test matched the selection");
        return kNothingSelected;
    }

    int64_t over_budget = 0;
    if (opts.time) {
        std::vector<std::pair<std::string, FileStats>> rows(stats.begin(), stats.end());
        // Stable so that files with equal totals keep their (name) order.
        std::ranges::stable_sort(rows,
            [](const auto& a, const auto& b) { return a.second.total_ms > b.second.total_ms; });
        // Widen past the minimum so a long (e.g. absolute) path cannot push the
        // numeric columns out of alignment.
        std::size_t width = 44;
        for (const auto& row : rows) {
            width = std::max(width, row.first.size());
        }
        std::println(
            "{:<{}} {:>6} {:>5} {:>11} {:>11}", "file", width, "cases", "fail", "total", "max");
        for (const auto& [file, s] : rows) {
            const bool over = kBudgetConfig && s.over_budget();
            over_budget += over ? 1 : 0;
            std::println("{:<{}} {:>6} {:>5} {:>10.3f}s {:>10.3f}s{}", file, width, s.cases,
                s.failed, s.total_seconds(), s.max_ms / 1000, over ? "  <-- over budget" : "");
        }
        // Say so rather than let a partial or differently-built measurement pass
        // for the budget AGENTS.md actually specifies.
        if (!kBudgetConfig) {
            std::fflush(stdout);
            std::println(stderr,
                "utest: --time is running outside the AGENTS.md budget config (debug without "
                "TCS_NO_TEMP_IMPL); the {:.1f}s/file budget is reported but not enforced",
                kFileBudgetSeconds);
        }
        if (!opts.filter.empty() || !opts.param_specs.empty()) {
            std::fflush(stdout);
            std::println(stderr,
                "utest: --time was given a filter or --params, so each file's total covers only "
                "the selected cases");
        }
    }

    std::println("{} passed, {} failed", total - failed, failed);

    // Report over-budget even when a test also failed, so the budget signal is
    // never lost; a test failure still takes precedence in the exit status.
    if (over_budget > 0) {
        std::fflush(stdout);
        std::println(
            stderr, "utest: {} file(s) over the {:.1f}s budget", over_budget, kFileBudgetSeconds);
    }
    if (failed > 0) {
        return kTestFailed;
    }
    if (over_budget > 0) {
        return kOverBudget;
    }
    return kOk;
}
}  // namespace utest
