#pragma once

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

inline Registrar test(std::string suite, std::string name, std::function<void()> func) {
    return Registrar(TestCase{std::move(suite), std::move(name), std::move(func)});
}

inline int run([[maybe_unused]] int argc, [[maybe_unused]] char* argv[]) {
    for (const auto& tc : TestRegistry::instance().tests()) {
        std::println("Running {}::{}", tc.suite, tc.name);
        tc.func();
    }
    return 0;
}
}  // namespace utest
