# Lean 4 formalization

Machine-checked correctness *and running-time* proofs for the algorithms in
`include/tcs/`, written in Lean 4 against Lean core + Std only: no Mathlib, no
package dependencies, and `lake` alone is enough to build them (no CMake, no
Makefile).

```bash
cd proof
lake build   # type check every proof
./check.sh   # proof-completeness audit: clean rebuild, per-file
             # -DwarningAsError=true, and no `sorry` / `sorryAx`
```

The package is deliberately **not** wired into the xmake build: it has its own
`lakefile.toml` and a pinned `lean-toolchain`, so the C++ build never needs a Lean
toolchain installed.

## What is verified

### Cycle sort — `Tcs/Cyclesort.lean`

`tcs::cyclesort::cyclesort`: the result is a permutation of the input and is sorted
by `proj` (`cyclesort_perm`, `cyclesort_sorted`, and `cyclesort_isSort` for both
halves together). The proof also covers the memory-safety property the C++ relies
on implicitly — that `std::find_if` in the inner loop can never run past the
destination range, where running off the end would be UB — as `exists_partner`.
The `while (true)` inner loop is modelled as a recursion whose fuel is the number
of unsettled positions.

### BFPRT selection — `Tcs/Bfprt.lean`

`tcs::bfprt::bfprt`, matching `tests/test_bfprt.cpp`: the result is a permutation
of the range and its element at index `k = mid - first` has rank `k`
(`bfprtAux_selects`) — its key is the `(k+1)`-th smallest of the range counting
multiplicity. At the `Array` level this is `bfprtRange_selects`, and
`bfprtRange_key_eq_sorted` is exactly the test's assertion: the key at `mid` equals
the key a sorted copy of the range carries there.

`Tcs/Select.lean` holds the rank relation `IsKthSmallest` and the selection
contract `Selects`; `Tcs/Sort.lean` holds `bubbleSort`, a literal model of the C++
`bubble_sort` loop (one pass carries the maximum to the right end, the outer loop
then runs over the shrinking prefix), and `Tcs/Bfprt.lean` holds a `std::partition`
model with its permutation/split lemmas, the median-of-medians group pass
(`placeMedian` / `groupPass`), and `bfprtAux`, which mirrors `bfprt.hpp` line for
line on the element list of the range, with the range length as fuel. `groupPass`
applies the passes in **increasing** group order, as the C++ loop does: that is what
puts the group medians in `[0, len / 5)`, and the order is significant (the reverse
order re-sorts a low group after its median has been moved out).

Correctness does not depend on the median-of-medians *choice*: a three-way
partition selects correctly for whatever pivot it is given, and the recursion
terminates because every recursive range is strictly shorter — the pivot occurs in
the range, so the block it lands in is a proper sub-range. Median of medians is what
makes that shortening *fast*; that running-time fact is formalized separately in
`Tcs/Cost/Bfprt.lean` (see the cost section below), where the group pass is used to
bound the size of the recursive range by `7n/10`.

### In-place unstable merge — `Tcs/UnstableMerge.lean`

`tcs::inplace::unstable_merge::inplace_unstable_merge`, matching
`tests/inplace/test_unstable_merge.cpp`: given two adjacent sorted runs
(`SortedOn proj l 0 k` and `SortedOn proj l k l.length`), the result is a
permutation of the range and is sorted (`unstableMerge_sorted_and_perm`), with the
`Array`-level `unstableMergeArray_sorted_and_perm`.

Every stage of the C++ is modelled in a module of its own. `Tcs/Merge.lean` proves
the rotation model `rot`/`rotRange` (the `std::ranges::rotate` calls),
`mergeWithSwap` — including the buffer-safety condition `output + (last - mid) ≤ first`
that the C++ relies on, and the fact that the buffer ends up holding *exactly* the
pure merge of the two runs, which pins the loop's tie-breaking — and
`mergeByRotation`. `Tcs/UnstableMerge.lean` proves the block phase
(`blockSelectionSort`, and `blockMergePairwise` whose "everything but the last block
is sorted" invariant needs a counting argument on the block order) and assembles the
algorithm.

Because these algorithms are deterministic, the Lean and the C++ results can be
compared element by element: 300 random cases through the whole pipeline (plus
400 + 400 through the two primitives) produced byte-identical arrays, and every pair
of sorted runs of length ≤ 3 over `{0,1,2}` (100 cases) satisfies the contract. The
`bubble_sort` calls are modelled literally in `Tcs/Sort.lean` (the C++ loop, not an
equivalent sort), so that their exact comparison count can be formalized.

### In-place stable merge — `Tcs/StableMerge.lean` (first milestone)

`tcs::inplace::stable_merge::inplace_stable_merge`, matching
`tests/inplace/test_stable_merge.cpp`: unlike the unstable merge above, the result
must also keep the input order of equal keys.

`Tcs/StableMerge.lean` states that contract without ever mentioning positions. For
a key `k`, `keyFilter proj k l` is the subsequence of `l` made of the elements whose
key equals `k`; asking it to be unchanged for every `k` says both that equal keys
keep their input order and that no element was lost or invented.
`StableSort proj l l'` bundles that with sortedness, and it is the contract the
whole pipeline `stable_unique_limit -> align_blocks_limit -> block phases ->
bubble_sort -> rotation merges` has to maintain end to end, so no uniqueness
argument about sorted permutations is needed anywhere.

Proved so far:

* `bubbleSort_stableSort` — `bubble_sort` is a stable sort of *any* list, because it
  only ever swaps two elements of strictly different keys. This closes the
  `block_size <= 4` branch of the C++, which below 25 elements calls `bubble_sort`
  over the whole range (the exhaustive cross-check below exercises exactly that
  branch for every input of length ≤ 24).
* `mergeTwo_stableSort` — the reference merge `mergeTwo` satisfies the same
  contract on two sorted runs, i.e. it takes from the left run exactly on ties.

Still to model: `stable_unique_limit`, `align_blocks_limit`, the label-carrying
`block_selection_sort`/`block_merge_pairwise`/`inplace_merge_with_rotation_indexed`
phases, and the assembly.

## Running time

The correctness proofs above say *what* each algorithm computes. `Tcs/Cost.lean` and
the `Tcs/Cost/` modules add *how much it costs*, also machine-checked.

### The cost model

A cost is a pair: the number of **key comparisons** and the number of **element
moves**, charged the way the C++ operations pay for them.

* one comparison for each evaluation of a scalar key test (`Cmp.ble` / `Cmp.blt`),
  i.e. for each `proj`-compared C++ expression;
* one move per element assignment or copy. `std::swap` is 3 (a temporary plus two
  assignments, exactly how it is written for a non-trivial value type); a by-value
  lambda parameter, as in `std::find_if` and `std::partition`, is 1 per call; a
  linear rotate of `m` elements is `Cost.rot m = 2m`, an upper bound valid for every
  implementation (a cyclic rotate moves each element once, a reversal-based one at
  most twice; libstdc++ uses the former).

Big-O is *uniform over the input family*: `IsBigOWith c size f g` says
`f i ≤ c * g (size i)` for **every** input `i`, where `size` is an explicit size
function, and `CostBigOWith` asks this of both components. Avoiding a supremum over
the inputs keeps the definition constructive — no `Classical.choice` — and makes the
statement stronger than the usual asymptotic reading: one constant works for every
input, not only for large ones.

### What is proved

Every algorithm has a *counting copy* of the verified model with the C++'s control
flow (`...C`), a theorem that the copy computes the model's result (`...C_fst`), and
cost theorems: an exact count where the count is exact, an explicit-constant bound
otherwise, plus a `CostBigOWith` corollary. With `tri k = k(k+1)/2` and
`bs = floor (sqrt n)`:

| algorithm | key comparisons | element moves | module |
|---|---|---|---|
| `bubble_sort`, `n` elements | exactly `n(n-1)/2` | `≤ 3n(n-1)/2` | `Cost/Sort.lean` |
| `cyclesort`, `n` elements | `≤ 7 n^2` | `≤ 7 n^2` | `Cost/Cyclesort.lean` |
| `cyclesort`, number of swaps | — | `≤ n` (the C++'s "O(n) writes") | `Cost/Cyclesort.lean` |
| `bfprt`, `n` elements | `≤ 400 n` | `≤ 400 n` | `Cost/Bfprt.lean` |
| `merge_with_swap`, range `n` | `≤ n` | exactly `3 n` | `Cost/Merge.lean` |
| `inplace_merge_with_rotation`, runs `a`, `b` | `≤ tri (min a b) + (a+b)` | `≤ 2(tri (min a b) + (a+b))` | `Cost/Merge.lean` |
| `block_selection_sort`, `m` blocks | `≤ 3 tri (m-1)` | `≤ 3 bs (m-1)` | `Cost/UnstableMerge.lean` |
| `block_merge_pairwise`, `m` blocks | `≤ 2 bs m` | `≤ 9 bs m` | `Cost/UnstableMerge.lean` |
| `inplace_unstable_merge`, `n` elements | `≤ 100 n` | `≤ 100 n` | `Cost/UnstableMerge.lean` |

The whole-range bound is the interesting one: the aligned prefix has only
`≈ sqrt n` blocks, so the block phases cost `O(bs · m) = O(n)`; the leftover suffix
that is bubble-sorted has length `≤ 3 bs`, so its quadratic cost is still `O(n)`; and
the final rotation merge has `min a b ≤ 3 bs`, so `tri (min a b) ≤ 9 n`. The
`inplace_unstable_merge` statements are the array-level ones
(`unstableMergeArrayC_cmp_le` / `_mv_le` / `_bigO`), with the split index bounded by
the range length.

`merge_with_swap` is where the pipeline spends most of its moves; its move count is
*exactly* `3n`, because the loop takes exactly `last - first` turns and swaps on
every one. The block phases of the unstable merge are the one place where the cost is
not computed by the same function that produces the result: their correctness model
is deliberately abstract (`blkMerge` / `blockMergeStd`, order-equivalent to the C++
but not literally the same element order), so `unstableMergeC` pairs the model's
result with a separate loop-level cost simulation of the C++ on the same blocks
(`unstableMergeC_fst` is `rfl`).

### BFPRT's linearity

`O(n)` for BFPRT is the median-of-medians rank argument, formalized in
`Cost/Bfprt.lean`:

1. `groupPass_take_eq_medians`: after the group pass, index `i < len / 5` holds the
   median of group `i` — this is exactly where the *increasing* pass order fixed
   above matters;
2. `three_mul_medians_count_le` / `_ge`: a sorted group of five whose middle element
   is `≤ t` (resp. `≥ t`) contributes three elements `≤ t` (resp. `≥ t`);
3. `partition_lengths_le_of_medians`: the pivot is a rank-`g/2` element of the `g`
   medians, so at least `g/2 + 1` medians are `≤` it and at least `g - g/2` are `≥`
   it; step 2 then bounds the two partition sides by `n - 3(g/2)` and
   `n - 3(g - g/2)`, i.e. by `7n/10` up to a small constant;
4. the recurrence `T n ≤ T (n/5) + T (7n/10 + c) + a n + b` therefore gives
   `T n ≤ 400 n` (`bfprtAuxC_le_linear`).

### Validation against the C++

The cost model was cross-checked against instrumented copies of the C++
implementations (a key type and an element type whose comparisons and assignments are
counted), on deterministic input families and sizes up to 4096:

* cycle sort: the comparison counts match the C++ *exactly* (five families at sizes
  16, 64 and 256 — the bound `7 n^2` is proved, so the asymptotic claim does not rest
  on the measured range), and the move count is the C++'s plus one key copy per
  `destination_range` call, the by-value argument the C++ makes and the model
  charges;
* BFPRT: the model's comparison count is 1.00–1.24× the C++'s and its move count at
  most 3.5× (the model charges every `std::partition` a full `n` predicate calls plus
  up to `n` swaps, while the C++ performs a data-dependent number of swaps);
* the unstable merge pipeline: comparisons are 1.0–1.7× and moves 0.86–1.33× the
  C++'s over seven families and sizes 64…4096. The one family where the model counts
  *fewer* moves is explained by the abstraction just described: the internal order of
  the block displaced by `merge_with_swap` is not modelled, which shifts the
  inversion count of the final bubble sort. The bound proved here is about the model,
  and the model's constant is comfortably above the C++'s count in all measured
  cases.

## Modelling conventions

Conventions shared by every proof module (`Tcs/Spec.lean` states them):

- an algorithm is `Array α → Array α`, mirroring a C++ iterator range
  `[first, last)`; `Array.swap` / `Array.set` model `std::swap` / assignment;
- a range algorithm is modelled on that range's element list — the C++ never reads
  outside `[first, last)` — and `bfprtRange` splices the result back into the array;
- "rearranged" is `List.Perm` on `Array.toList`;
- "sorted" is `Sorted`, i.e. core's `List.Pairwise`;
- key order is the `Cmp` class (`Tcs/Order.lean`): Lean core and Std ship no order
  classes (`LinearOrder` belongs to Mathlib), so keys carry their own Bool-valued
  decidable total order, matching what the C++ comparison operators compute;
- "rank" is count-based (`Tcs/Select.lean`), which handles duplicate keys exactly:
  two elements of the same rank in one list have equal keys
  (`isKthSmallest_unique`), which is why comparing keys against a sorted copy — as
  the C++ tests do — is the right contract;
- "stable" labels elements with their original index and orders by key only;
- "O(1) extra space" is constructive: algorithms only `swap` / `set` in place.

## Quality gates

- no `sorry` / `admit` / `axiom` / `native_decide` / `unsafe` / `partial` anywhere;
- `#print axioms` for every public theorem reports only `[propext, Quot.sound]`,
  with no `Classical.choice`;
- `check.sh` demands a clean rebuild, a per-file type check with
  `-DwarningAsError=true`, no `sorryAx` in the environment, and — via
  `AxiomAudit.lean` — that no declaration in the `Tcs` namespace reaches
  `Classical.choice`;
- the cost model's charging rules are the C++ operations' own (see "Running time");
  `Nat.sqrt` bounds are reproved constructively in `Cost/UnstableMerge.lean`, because
  core's `Nat.sqrt_le` and `Nat.lt_succ_sqrt` both pull in `Classical.choice` — as do
  `List.take_add` (why `Cost/Bfprt.lean` keeps its own `take_add_groups`) and
  `Nat.lt_of_mul_lt_mul_left`/`_right` (why `Cost/UnstableMerge.lean` keeps
  `um_mul_lt_cancel_right`). A further trap is that `omega` applied to a goal whose
  context still holds list hypotheses can pick up `Classical.choice`; the arithmetic is
  therefore factored into pure-`Nat` helper lemmas, and the axiom audit below is run
  after every change;
- beyond the proofs, the models were cross-checked behaviourally against the C++
  implementations: exhaustive sweeps over all small inputs and random larger ones
  (two independent oracles: a sorted copy and a direct count); for BFPRT, 400 shared
  random cases fed through both implementations (identical `k`-th smallest keys);
  and for the unstable merge — whose stages are deterministic, so the whole output
  array is comparable — 300 + 400 + 400 shared random cases with byte-identical
  arrays.

## Module map

```text
proof/
├── Tcs/Spec.lean               # Specification vocabulary (Sorted / Permutes / IsSort)
├── Tcs/Order.lean              # `Cmp`: a decidable total order on keys
├── Tcs/Count.lean              # Generic `List.countP` lemmas
├── Tcs/Perm.lean               # Swap → `Perm` bridge for in-place algorithms
├── Tcs/Select.lean             # Rank and selection specs (k-th smallest key)
├── Tcs/Sort.lean               # `bubble_sort`, modelled as the C++ loop
├── Tcs/Cyclesort.lean          # Verified cycle sort
├── Tcs/Bfprt.lean              # Verified BFPRT selection
├── Tcs/Merge.lean              # rotate, `merge_with_swap`, `inplace_merge_with_rotation`
├── Tcs/UnstableMerge.lean      # block selection/merge and `inplace_unstable_merge`
├── Tcs/StableMerge.lean        # stability spec; `bubble_sort` branch of `inplace_stable_merge`
├── Tcs/Cost.lean               # Cost model and uniform big-O
├── Tcs/Cost/Sort.lean          # Cost of `bubble_sort`
├── Tcs/Cost/Cyclesort.lean     # Cost of cycle sort
├── Tcs/Cost/Bfprt.lean         # Cost of BFPRT, including linearity
├── Tcs/Cost/Merge.lean         # Cost of the merge primitives
├── Tcs/Cost/UnstableMerge.lean # Cost of the whole merge pipeline
├── AxiomAudit.lean             # `#print axioms` sweep over all `Tcs` declarations
├── lakefile.toml               # Lake package definition
├── lean-toolchain              # Pinned Lean toolchain
└── check.sh                    # Audit: rebuild, per-file strict check, no sorry, no choice
```
