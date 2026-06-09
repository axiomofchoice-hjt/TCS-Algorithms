#pragma once

#include <cstring>
#include <format>
#include <functional>
#include <print>
#include <source_location>
#include <stdexcept>
#include <string>

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

struct Registrar {
    Registrar(TestCase tc) { TestRegistry::instance().add_test(std::move(tc)); }
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

inline int run([[maybe_unused]] int argc, [[maybe_unused]] char* argv[]) {
    for (const auto& tc : TestRegistry::instance().tests()) {
        try {
            tc.func();
        } catch (const std::exception& e) {
            std::println("Test {}.{} failed: {}", tc.suite, tc.name, e.what());
            return 1;
        }
    }
    return 0;
}
}  // namespace utest
