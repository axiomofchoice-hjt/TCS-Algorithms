# TCS-Algorithms

In-place algorithms in modern C++ — with more to come.

Built with **C++23** and **xmake**.

## 1. Motivation

In-place algorithms are like dancing in shackles — pushing theoretical boundaries under the strictest space constraints.
Can we merge two sorted arrays in $O(n)$ time and $O(1)$ extra space — and do it stably?
Partition around a predicate? Select the k-th smallest element?
The answer to each of these is yes, but the algorithms are buried in academic papers from the 1980s–1990s and rarely implemented.

This project brings them to life under the **Word RAM model** — the standard model for algorithm analysis where a word is just large enough to hold a pointer (like `size_t`), but cannot encode arbitrary information.
Under this model, "in-place" has a rigorous meaning: $O(1)$ extra space, not just "no heap allocation."
The `include/tcs/pointer/` directory instead hosts algorithms for the **pointer-machine model**, where following a link is the only cost unit and linked structures are the native representation.
Each header is self-contained — copy one file, include it, and you're done.

The goal is **algorithmic clarity**, not chasing constant factors.
For the full story behind each algorithm, start with the [overview](https://axiomofchoice-hjt.github.io/pages/1b8e07/) (Chinese).

## 2. Algorithms

1. **In-place Unstable Merge** — `#include <tcs/inplace/unstable_merge.hpp>`
   - $O(n)$ time, $O(1)$ extra space
   - Merge two sorted adjacent subarrays (unstable)
   - [Blog post](https://axiomofchoice-hjt.github.io/pages/c829b5/)

2. **In-place Stable Merge** — `#include <tcs/inplace/stable_merge.hpp>`
   - $O(n)$ time, $O(1)$ extra space
   - Merge two sorted adjacent subarrays, preserving stability
   - [Blog post](https://axiomofchoice-hjt.github.io/pages/326ae9/)

3. **In-place Stable Partition** — `#include <tcs/inplace/stable_partition.hpp>`
   - $O(n)$ time, $O(1)$ extra space
   - Partition an array around a predicate while preserving relative order
   - [Blog post](https://axiomofchoice-hjt.github.io/pages/0d69d8/)

4. **In-place Stable Select** — `#include <tcs/inplace/stable_select.hpp>`
   - $O(n)$ time, $O(1)$ extra space
   - k-th smallest element selection with stability guarantee
   - [Blog post](https://axiomofchoice-hjt.github.io/pages/8da648/)

More algorithms are available in `include/tcs/` and `examples/` for usage demos.

The complexity above is that of the algorithms. A few headers delegate to a
secondary helper (partition / unpartition / select): by default they build that
helper with `std`-based fallbacks so they remain copyable as single files, but
those fallbacks run in O(n) extra space. When you use the full `include/tcs/`
tree, define **`TCS_NO_TEMP_IMPL`** to switch those helpers to the true O(1)
in-place primitives in `stable_partition.hpp`, `stable_unpartition.hpp`,
`stable_select.hpp`, and `unstable_select.hpp`.

## 3. Quick Start

```bash
# Install xmake
curl -fsSL https://xmake.io/shget.text | bash

# Build & run all tests
./run.sh

# Manual ASan + UBSan: build the test/example binaries with AddressSanitizer
# and UndefinedBehaviorSanitizer, then run the test suite.
./scripts/asan.sh
```

The Lean 4 formalization lives in `proof/` and is built on its own with `lake`
— it is not part of the xmake build:

```bash
cd proof
lake build   # type check every proof
./check.sh   # proof-completeness audit: no sorry, no sorryAx
```

## 4. Directory Structure

```text
TCS-Algorithms/
├── include/tcs/            # Header-only library
│   ├── bfprt.hpp           # Median-of-medians selection
│   ├── cyclesort.hpp       # Classic in-place cycle sort
│   ├── inplace/            # In-place algorithms (O(1) space)
│   ├── pointer/            # Pointer-machine algorithms
│   ├── readonly/           # Read-only-input algorithms
│   └── ds/                 # Data structures
├── tests/                  # Unit tests
│   ├── common/             # Shared test helpers
│   ├── inplace/            # Tests for in-place algorithms
│   ├── pointer/            # Tests for pointer-machine algorithms
│   ├── readonly/           # Tests for readonly algorithms
│   └── ds/                 # Tests for data structures
├── examples/               # Usage examples
│   ├── common.hpp          # Shared example helpers
│   ├── example_bfprt.cpp   # BFPRT selection demo
│   └── inplace/            # Examples for in-place algorithms
├── proof/                  # Lean 4 formalization (independent lake project)
│   ├── Tcs/Spec.lean       # Specification vocabulary (Sorted / Permutes / IsSort)
│   ├── Tcs/Order.lean      # Decidable total order on keys (Lean core has none)
│   ├── Tcs/Count.lean      # List.countP lemmas shared by the algorithm proofs
│   ├── Tcs/Perm.lean       # Swap → Perm bridge for in-place algorithms
│   ├── Tcs/Select.lean     # Rank and selection specs (k-th smallest key)
│   ├── Tcs/Cyclesort.lean  # Verified cycle sort (see below)
│   ├── Tcs/Bfprt.lean      # Verified BFPRT selection (see below)
│   ├── lakefile.toml       # Lake package definition
│   ├── lean-toolchain      # Pinned Lean toolchain
│   └── check.sh            # Proof-completeness audit (no sorry / sorryAx)
├── scripts/                # Dev scripts
│   ├── format.sh           # clang-format all sources
│   ├── code-quality.sh     # clang-format + clang-tidy checks
│   └── asan.sh             # Manual ASan+UBSan build & run
└── xmake.lua               # Build configuration
```

The `proof/` directory is deliberately **not** wired into the xmake build: it is
a self-contained Lean 4 project with its own `lakefile.toml` and pinned
`lean-toolchain`, and it is built with `lake` alone (no CMake, no Makefile).

So far `tcs::cyclesort::cyclesort` and `tcs::bfprt::bfprt` are formally verified
end to end, with no `sorry` anywhere and no `Classical.choice` in either proof.

`Tcs/Cyclesort.lean`: the result is a permutation of the input and is sorted by
`proj`. The proof also covers the memory-safety property the C++ relies on
implicitly — that `std::find_if` in the inner loop can never run past the
destination range — as `exists_partner`.

`Tcs/Bfprt.lean`: modelled on the element list of the range `[first, last)`, with
`k = mid - first`, and matching `tests/test_bfprt.cpp`: the result is a permutation
of the range and its element at index `k` has rank `k` (`Tcs.IsKthSmallest`), that
is, its key is the `(k+1)`-th smallest of the range counting multiplicity
(`bfprtAux_selects`, with the array-level `bfprtRange_selects` and
`bfprtRange_key_eq_sorted` corollaries). The median-of-medians *choice* is
deliberately unused: a three-way partition selects correctly for whatever pivot it
is given, and the recursion terminates because every recursive range is strictly
shorter — which only needs the pivot to occur in the range. Median of medians is
what makes that shortening fast, a running-time fact that is not formalized. The
model was cross-checked against the C++ implementation on 400 shared random cases
(identical `k`-th smallest keys) and against an exhaustive sweep of every input of
length at most 6.

## 5. Dependencies

- **Compiler**: GCC 14+ / Clang 18+ (C++23 support required)
- **Build tool**: [xmake](https://xmake.io/)
- **Lean toolchain** (optional, `proof/` only): Lean 4 via
  [elan](https://github.com/leanprover/elan); `lake` builds it with no further
  dependencies and no Mathlib.

## 6. Usage

Header-only — copy `include/tcs/` into your project, or integrate via xmake:

```cpp
#include <tcs/bfprt.hpp>
#include <vector>

std::vector<int> arr = {3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5};
int k = 5;
tcs::bfprt::bfprt(arr.begin(), arr.begin() + k, arr.end());
// arr[k] holds the k-th smallest element
```

## 7. License

MIT
