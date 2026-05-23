# TCS-Algorithms

Implementations of theoretical computer science algorithms in modern C++.

Built with **C++23**, **xmake**, and **Catch2**.

## 1. Algorithms

1. **BFPRT** (Median of Medians) — `#include <tcs/bfprt.hpp>`
   - $O(n)$ time, $O(\log n)$ extra space (recursion stack)
   - k-th smallest element selection
   - [Blog post](https://axiomofchoice-hjt.github.io/pages/63a6df/) (covers both BFPRT and Inplace Unstable Select)

2. **Inplace Unstable Select** — `#include <tcs/inplace_unstable_select.hpp>`
   - $O(n)$ time, $O(1)$ extra space
   - Inplace k-th smallest selection
   - [Blog post](https://axiomofchoice-hjt.github.io/pages/63a6df/) (same post as BFPRT)

3. **Inplace Stable Partition** — `#include <tcs/inplace_stable_partition.hpp>`
   - $O(n)$ time, $O(1)$ extra space
   - Partition an array around a predicate while preserving relative order
   - [Blog post](https://axiomofchoice-hjt.github.io/pages/0d69d8/)

4. **Inplace Stable Unpartition** — `#include <tcs/inplace_stable_unpartition.hpp>`
   - $O(n)$ time, $O(1)$ extra space
   - Reverse a stable partition to original order via a placement oracle
   - [Blog post](https://axiomofchoice-hjt.github.io/pages/60450e/)

5. **Inplace Stable Merge** — `#include <tcs/inplace_stable_merge.hpp>`
   - $O(n)$ time, $O(1)$ extra space
   - Merge two sorted adjacent subarrays, preserving stability
   - [Blog post](https://axiomofchoice-hjt.github.io/pages/326ae9/)

6. **Inplace Unstable Merge** — `#include <tcs/inplace_unstable_merge.hpp>`
   - $O(n)$ time, $O(1)$ extra space
   - Merge two sorted adjacent subarrays (unstable)
   - [Blog post](https://axiomofchoice-hjt.github.io/pages/c829b5/)

See `examples/` for usage demos. Blog posts are written in Chinese (中文).

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
