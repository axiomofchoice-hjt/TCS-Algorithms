# TODO

## High Priority

### 1. Add meaningful messages to all `assert_or_throw` calls

Currently most assertions use the default `"empty message"`, making failures hard to debug.
Every call site in `include/tcs/` should provide a descriptive message indicating which
invariant was violated.

## Medium Priority

### 2. Stubs are by design — keep for readability

`inplace_stable_select` and `inplace_stable_quicksort` delegate to stub functions for
partition, unpartition, and selection. Replacing them with real O(1) implementations
would inline too much code and hurt readability. Stubs are intentional.

### 3. (By design) Duplicated utilities kept for self-contained headers

`bubble_sort`, `ceil_log2`, `WordStorage`, `BufferStorage`, `BitStack`, `StorageAttributes`
are intentionally duplicated per header so each file can be copied and used standalone
without internal dependencies. Each resides in its own `tcs::<algorithm>` namespace to
avoid ODR conflicts when multiple headers are included together.

### 4. Add missing assertions to internal helpers

Some internal functions lack precondition checks. Candidates:

- `bubble_sort(first, last)` — assert `first <= last`
- `block_selection_sort` — assert `first <= last` and alignment
- `stable_collect_first_n` — assert `n >= 0`
- `unpartition_with_rotation` — assert `first <= last`

### 5. Sweep test generates many trivial cases

Manual `for (int64_t n = 0; n <= kSweepMaxSize; n++)` includes very small `n` where
algorithms degenerate to fallback. Consider logarithmic sweep or skipping `n < some_threshold`.

### 6. Improve variable naming in complex functions

- `merge_blocks_impl`: `counters[0]`/`counters[1]` → `kZero`/`kOne`
- `inplace_stable_01_unpartition`: step loop magic `3` and `2` → named constants

### 7. Unify `Storage` factory pattern

Mix of `static create()` and aggregate init `{.n_bits=..., .element_bits=...}`.
Pick one style.

### 8. `std::partition` → `std::ranges::partition`

Skipped because ranges version returns `subrange`, not plain iterator. Call sites
need `.begin()` adjustment.

## Low Priority

### 9. Doxygen-style docs for algorithm entry points

### 10. `assert_or_throw` semantics

Split into `ASSERT` (debug-only) vs `VERIFY` (always-active) for intent clarity.
