#include <format>
#include <source_location>
#include <string_view>

namespace tcs {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}
}  // namespace tcs
