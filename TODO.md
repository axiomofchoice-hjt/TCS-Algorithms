# TODO

## High Priority

### 1. Add meaningful messages to all `assert_or_throw` calls
Currently most assertions use the default `"empty message"`, making failures hard to debug.
Every call site in `include/tcs/` should provide a descriptive message indicating which invariant was violated.
These currently produce opaque errors like `Assertion failed at inplace_stable_unpartition.hpp:137: empty message`.

### 2. (By design) Duplicated utilities kept for self-contained headers
`bubble_sort`, `ceil_log2`, `WordStorage`, `BufferStorage` are intentionally duplicated per header so each file can be copied and used standalone without internal dependencies.

## Medium Priority

### 3. Add missing assertions to internal helpers
Some internal functions lack precondition checks. Candidates:
- `bubble_sort(first, last)` — should assert `first <= last` (all call sites)
- `block_selection_sort(first, last, ...)` — should assert `first <= last` and alignment constraints
- `stable_collect_first_n(first, last, n, ...)` — should assert `n >= 0`
- `unpartition_with_rotation(first, last, ...)` — should assert `first <= last`

### 4. Add boundary stress tests
- Tests for non-trivial element types (e.g., `std::string`)
- Tests with very high ratio of duplicate values
- 100k+ element tests beyond the few existing ones

### 5. Sweep test generates too many trivial cases
`GENERATE(Catch::Generators::range(0, kSweepMaxSize + 1))` includes very small `n` where algorithms degenerate to bubble sort fallback. Consider logarithmic sweep or skipping `n < some_threshold`.

### 6. Improve variable naming in complex functions
- `merge_blocks_impl`: `counters[0]`/`counters[1]` and `pointers[0]`/`pointers[1]` differentiate zero/one groups by index — use a named struct or at least `constexpr int kZero = 0, kOne = 1`.
- `inplace_stable_01_unpartition`: magic constants `3` and `2` for step loops should be named constants.

### 7. Unify `Storage` factory pattern
`WordStorage`/`BufferStorage` use `static create()` factory methods, but some call sites use aggregate initialization `{.n_bits=..., .element_bits=...}`. Pick one style and apply consistently.

## Low Priority

### 8. Add Doxygen-style documentation to algorithm entry points
All public entry points lack documentation comments describing the algorithm, parameters, complexity guarantees, and invariants.

### 9. `assert_or_throw` used for control flow vs. invariant checking
Some assertions guard normal branching logic (not just debug-only invariants). Consider splitting into `ASSERT` (debug-only) and `VERIFY` (always-active) macros to make intent clear.
