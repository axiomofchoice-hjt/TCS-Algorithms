# TCS-Algorithms — Agent Instructions

## Project

Header-only C++23 library of in-place algorithms with optimal theoretical bounds. All algorithms target O(n) time, O(1) extra space under Word RAM (except BFPRT: O(log n) recursion stack). Algorithmic clarity over performance — constant-factor optimizations are out of scope.

## Commands

```sh
./run.sh                         # Build everything and run all tests
xmake build test                 # Build test binary only
xmake run test [-- args...]       # Run all tests, with optional CLI filtering
xmake f --mode=debug && xmake    # Debug build
bash scripts/code-quality.sh     # clang-format + clang-tidy (requires clang toolchain)
```

## Architecture

- `include/tcs/` — 1 header per algorithm. Fully self-contained: each has its own namespace and copies of shared utilities (`bubble_sort`, `assert_or_throw`, `WordStorage`, `BitStack`, etc.). Do NOT try to extract shared code into a common header — duplication is by design.
- `tests/` — Unit tests, one `.cpp` per algorithm. `utest.hpp` is the lightweight test runner; `test_main.cpp` is the entrypoint.

## Key conventions

- **No `git commit` unless explicitly asked.** Edits go to the working tree; the user says when to commit. Even if the user asks to make a change, do NOT commit unless they also say "commit" or "提交".
- **NEVER use `git checkout --` or `git restore` to discard working tree changes.** The user explicitly forbids this.
- **No comments unless asked.** Don't add doc comments, inline explanations, or `// TODO` notes unrequested.
- Use `std::iter_value_t<RandomIt>` not `std::iterator_traits<...>::value_type` (C++23 style).
- Assertions: `assert_or_throw` lives in each header's namespace. Prefer descriptive messages over the default `"empty message"`.
- `.clang-format`: Google-based, 4-space indent, 100 column limit.

## Gotchas

- **Recursion → iteration:** `inplace_stable_select` was converted from recursive to `while` loop for real O(1) space guarantee. Don't reintroduce recursion.
- **`restoring_select` Stack:** buffer-backed bit stack using element pair swaps. Each bit occupies one pair (buf0[i], buf1[i]) — buf0 < buf1 by construction. Push swaps the pair if bit=1, pop swaps back and reads.
- **`restoring_select_buffer_size`:** correctly accounts for framing (4*scalar_bits per level) plus 2*len per level for bit arrays.
- **Tests use `IndexedElement`** (key + index) to verify stability via `common_test.hpp`.

---

## Code Style (Detailed)

### File & Namespace Structure

- One algorithm per header under `include/tcs/<algorithm>.hpp`.
- Each header is fully self-contained: it repeats all shared helpers (`assert_or_throw`, `bubble_sort`, `ceil_log2`, `WordStorage`, `BufferStorage`, `BitStack`, `StorageAttributes`, etc.).
- Namespace pattern: `namespace tcs { namespace <algorithm_name> { ... } }`.
- No common internal headers; standalone copy-paste-ability is a design goal.

### C++23 Idioms

- Iterator typedef: `std::iter_value_t<RandomIt>` instead of `std::iterator_traits<RandomIt>::value_type`.
- Projection parameter: `typename Proj = std::identity` on every public / helper template that needs ordering.
- Ranges algorithms: prefer `std::ranges::rotate`, `std::ranges::is_sorted`, `std::ranges::find_if`, `std::ranges::max_element`, etc.
- Pass `{}` as the comparator when using ranges calls with projections: `std::ranges::is_sorted(first, last, {}, proj)`.
- CTAD: `std::pair{...}` instead of `std::pair<...>{...}`.
- Designated initializers: `WordStorage{.n_bits = w, .element_bits = e, .word = 0}`.
- Formatting: use `std::format` for assertion messages and test diagnostics.
- Attributes: `[[unlikely]]` on assertion-failure branches.

### Naming

- Functions, local variables, parameters: `snake_case`.
- Types / structs: `PascalCase` (e.g. `WordStorage`, `BufferStorage`, `BitStack`).
- Template parameters: `RandomIt`, `Pred`, `Proj`, `Storage`, `T`.
- Test constants: `kCamelCase` (e.g. `kRandomSeed`, `kSweepMaxSize`).
- Internal helpers use short, math-oriented names: `first`, `last`, `mid`, `len`, `n_blocks`, `buf0`, `buf1`.

### Types & Arithmetic

- Indexes and lengths are `int64_t`, not `int` or `size_t`.
- Literals in bitwise contexts: `uint64_t{1}` instead of `1ULL`.
- `ceil_log2` helper is duplicated per header; it wraps `std::bit_width`.

### Assertions

- `assert_or_throw` is duplicated per header with `std::source_location` support.
- Default message is `"empty message"` — actively discouraged; every call site should pass a descriptive invariant message.
- `static_assert(std::is_invocable_v<Proj, T>)` or `std::is_invocable_r_v<bool, Pred, T>` on templates that accept callables.

### Formatting

- Enforced by `.clang-format` (Google base, 4-space indent, 100-column limit, `AllowShortFunctionsOnASingleLine: All`).
- Run `bash scripts/code-quality.sh` before finishing touches.

---

## Test Style

- **Framework:** `utest.hpp` — minimal auto-registration runner, no macros, no external dependencies.
- **Test registration:** `utest::test("suite", "name", [] { ... })` at file scope.
- **Parameterized registration:** `utest::register_test([] { for (...) { utest::test("suite", "name", func, TestParam{...}); } })`. `func` receives `TestParam` by value; the framework serializes params via `memcpy`.
- **Assertions:** `utest::assert_or_throw(condition, message)` — throws on failure.
- **CLI filtering:** `--filter <substr>` matches "suite.name"; `--params <spec>...` matches TestCase params by interval (e.g. `0-2,5 1- -`).
- **Stability testing:** `IndexedElement` (`key` + `index`) in `tests/common_test.hpp`; `is_stable()` checks index monotonicity for equal keys.
- **Parameterized cases:** a `struct TestParam` + `constexpr TestParam kCases[]` array. Edge cases (all zeros, single element, all same key, min / max k) are explicit entries.
- **Sweep tests:** manual `for (int64_t n = 0; n <= kSweepMaxSize; n++)` loops for exhaustive small-size coverage.
- **Random seed:** fixed `std::mt19937 gen(kRandomSeed)` with `kRandomSeed = 42` for reproducibility.
- **Anonymous namespaces:** all test helpers live in an unnamed namespace.
