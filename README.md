# TCS-Algorithms

Implementations of theoretical computer science algorithms in modern C++.

Built with **C++23**, **xmake**, and **Catch2**.

## 1. Motivation

Inplace algorithms are like dancing in shackles — pushing the limits of theory under the strictest
space constraints. Can you merge two sorted arrays in $O(n)$ time with $O(1)$ extra space? Stably?
Partition around a predicate? Select the k-th smallest element? The answers are yes, but the
algorithms are buried in academic papers from the 1980s–1990s and rarely implemented.

This project brings them to life under the **Word RAM model** — the standard model for algorithm
analysis where a word is just large enough to hold a pointer (think `size_t`), but can't encode
arbitrary information. Under this model, "inplace" has a rigorous meaning: $O(1)$ extra space,
not just "no heap allocation." Each header is self-contained — copy one file, include it, and
you're done.

The goal is **algorithmic clarity**, not chasing constant factors. For the deeper story behind
each algorithm, start with the [overview](docs/overview.md) (Chinese).

## 2. Algorithms

1. **Inplace Unstable Merge** — `#include <tcs/inplace_unstable_merge.hpp>`
   - $O(n)$ time, $O(1)$ extra space
   - Merge two sorted adjacent subarrays (unstable)
   - [Blog post](docs/unstable-merge.md) (also at [axiomofchoice-hjt.github.io](https://axiomofchoice-hjt.github.io/pages/c829b5/))

2. **Inplace Stable Merge** — `#include <tcs/inplace_stable_merge.hpp>`
   - $O(n)$ time, $O(1)$ extra space
   - Merge two sorted adjacent subarrays, preserving stability
   - [Blog post](docs/stable-merge.md) (also at [axiomofchoice-hjt.github.io](https://axiomofchoice-hjt.github.io/pages/326ae9/))

3. **Inplace Stable Partition** — `#include <tcs/inplace_stable_partition.hpp>`
   - $O(n)$ time, $O(1)$ extra space
   - Partition an array around a predicate while preserving relative order
   - [Blog post](docs/stable-partition.md) (also at [axiomofchoice-hjt.github.io](https://axiomofchoice-hjt.github.io/pages/0d69d8/))

4. **BFPRT** (Median of Medians) & **Inplace Unstable Select**
   - `#include <tcs/bfprt.hpp>`, `#include <tcs/inplace_unstable_select.hpp>`
   - $O(n)$ time; BFPRT uses $O(\log n)$ extra space (recursion), select uses $O(1)$
   - k-th smallest element selection
   - [Blog post](docs/bfprt-and-unstable-select.md) (also at [axiomofchoice-hjt.github.io](https://axiomofchoice-hjt.github.io/pages/63a6df/))

5. **Inplace Stable Unpartition** — `#include <tcs/inplace_stable_unpartition.hpp>`
   - $O(n)$ time, $O(1)$ extra space
   - Reverse a stable partition to original order via a placement oracle
   - [Blog post](docs/stable-unpartition.md) (also at [axiomofchoice-hjt.github.io](https://axiomofchoice-hjt.github.io/pages/60450e/))

See `examples/` for usage demos. Detailed articles in `docs/` (Chinese).

## 2. Quick Start

```bash
# Install xmake
curl -fsSL https://xmake.io/shget.text | bash

# Build & run all tests
./run.sh
```

## 3. Directory Structure

```text
TCS-Algorithms/
├── include/tcs/           # Header-only library
├── tests/                 # Catch2 unit tests
├── docs/                  # Algorithm articles (Chinese)
├── examples/              # Usage examples
├── scripts/               # Code quality checks
└── xmake.lua              # Build configuration
```

## 4. Dependencies

- **Compiler**: GCC 14+ / Clang 18+ (C++23 support required)
- **Build tool**: [xmake](https://xmake.io/)
- **Test framework**: [Catch2](https://github.com/catchorg/Catch2) (auto-fetched by xmake)

## 5. Usage

Header-only — copy `include/tcs/` into your project, or integrate via xmake:

```cpp
#include <tcs/bfprt.hpp>
#include <vector>

std::vector<int> arr = {3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5};
int k = 5;
tcs::bfprt::bfprt(arr.data(), arr.data() + k, arr.data() + arr.size());
// arr[k] holds the k-th smallest element
```

## 6. Code Quality

```bash
# Run clang-format and clang-tidy checks
./scripts/code-quality.sh
```

## 7. License

MIT
