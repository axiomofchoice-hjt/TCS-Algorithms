# TODO

## High Priority

### 1. Add meaningful messages to all `assert_or_throw` calls

Currently most assertions use the default `"empty message"`, making failures hard to debug.
Every call site in `include/tcs/` should provide a descriptive message indicating which
invariant was violated.

### 2. Implement `inplace_stable_select`

Currently placeholder using `std::ranges::stable_sort`. Needs the real O(n) in-place
stable selection algorithm as described.

### 3. Debug `inplace_stable_unpartition` test failures

~999 assertions fail in sweep test (line 137 / inplace_01_split boundary assertion).
Algorithm logic needs investigation.

## Medium Priority

### 4. (By design) Duplicated utilities kept for self-contained headers

`bubble_sort`, `ceil_log2`, `WordStorage`, `BufferStorage`, `BitStack`, `StorageAttributes`
are intentionally duplicated per header so each file can be copied and used standalone
without internal dependencies. Each resides in its own `tcs::<algorithm>` namespace to
avoid ODR conflicts when multiple headers are included together.

### 5. Add missing assertions to internal helpers

Some internal functions lack precondition checks. Candidates:
- `bubble_sort(first, last)` — assert `first <= last`
- `block_selection_sort` — assert `first <= last` and alignment
- `stable_collect_first_n` — assert `n >= 0`
- `unpartition_with_rotation` — assert `first <= last`

### 6. Sweep test generates too many trivial cases

`GENERATE(Catch::Generators::range(1, kSweepMaxSize + 1))` includes very small `n` where
algorithms degenerate to fallback. Consider logarithmic sweep or skipping `n < some_threshold`.

### 7. Improve variable naming in complex functions

- `merge_blocks_impl`: `counters[0]`/`counters[1]` → `kZero`/`kOne`
- `inplace_stable_01_unpartition`: step loop magic `3` and `2` → named constants

### 8. Unify `Storage` factory pattern

Mix of `static create()` and aggregate init `{.n_bits=..., .element_bits=...}`.
Pick one style.

### 9. `std::partition` → `std::ranges::partition`

Skipped because ranges version returns `subrange`, not plain iterator. Call sites
need `.begin()` adjustment.

## Low Priority

### 10. Doxygen-style docs for algorithm entry points

### 11. `assert_or_throw` semantics

Split into `ASSERT` (debug-only) vs `VERIFY` (always-active) for intent clarity.

## Completed

- [x] `T*` → `RandomIt` iterator refactoring (all headers)
- [x] `Proj = std::identity` default template parameter (all headers)
- [x] `std::is_sorted` → `std::ranges::is_sorted`
- [x] `std::find_if/count_if/all_of/max_element` → `std::ranges::` versions
- [x] `std::less{}` → `{}` in `std::ranges` calls
- [x] `kStandardCases` + `kEdgeCases` → unified `kCases[]` with `repeat_count`
- [x] `IndexedElement` extracted to `tests/common_test.hpp`
- [x] `readability-function-cognitive-complexity` disabled (REQUIRE inflates metric)
- [x] Sweep tests use `GENERATE(Catch::Generators::range(...))`
- [x] All algorithm calls wrapped in try-catch with `INFO` on failure
- [x] `int` → `int64_t` in all test files
- [x] `assert.hpp` deleted; `assert_or_throw` inlined per header
- [x] `#include <functional>` added to all headers using `std::identity`

## Future Algorithms

- O(n) Moves In-place Stable Sort
- In-place Burrows–Wheeler Transform
- Rank-Pairing / Hollow / Soft / Strict Fibonacci / Brodal Heap
- Fusion Tree, Cuckoo Hashing, Tango Tree
- Deamortized Splay Tree
- Succinct Bit Vector
- Cache-Oblivious B-Tree
- In-place Linked List Shuffle
- Stable Duplicate-Key Extraction

## Search Channels

- Google Scholar cited-by chains
- https://cstheory.stackexchange.com/questions/tagged/ds.algorithms
- STOC/FOCS/SODA proceedings (1980–2015)
- Jeff Erickson's Algorithms notes references
- arXiv cs.DS
- Wikipedia List of algorithms footnotes
- Semantic Scholar "Highly Influenced" on classic papers
- Huang & Langston 1989 cited-by chain for all O(1)-space lineage
