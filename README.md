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

## 3. Quick Start

```bash
# Install xmake
curl -fsSL https://xmake.io/shget.text | bash

# Build & run all tests
./run.sh
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
├── scripts/                # Dev scripts
│   ├── format.sh           # clang-format all sources
│   └── code-quality.sh     # clang-format + clang-tidy checks
└── xmake.lua               # Build configuration
```

## 5. Dependencies

- **Compiler**: GCC 14+ / Clang 18+ (C++23 support required)
- **Build tool**: [xmake](https://xmake.io/)

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
