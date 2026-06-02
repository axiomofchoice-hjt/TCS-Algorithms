# TCS-Algorithms — Agent Instructions

## Project

Header-only C++23 library of in-place algorithms with optimal theoretical bounds. All algorithms target O(n) time, O(1) extra space under Word RAM (except BFPRT: O(log n) recursion stack). Algorithmic clarity over performance — constant-factor optimizations are out of scope.

## Commands

```sh
./run.sh                         # Build everything and run all tests
xmake build test                 # Build test binary only
xmake run test "[tag]"           # Run a single test suite (Catch2 filter)
xmake f --mode=debug && xmake    # Debug build
bash scripts/code-quality.sh     # clang-format + clang-tidy (requires clang toolchain)
```

## Architecture

- `include/tcs/` — 1 header per algorithm. Fully self-contained: each has its own namespace and copies of shared utilities (`bubble_sort`, `assert_or_throw`, `WordStorage`, `BitStack`, etc.). Do NOT try to extract shared code into a common header — duplication is by design.
- `tests/` — Catch2 unit tests, one `.cpp` per algorithm. `test_main.cpp` is the entrypoint.

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
