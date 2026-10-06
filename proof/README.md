# Lean 4 formalization

Machine-checked correctness proofs for the algorithms in `include/tcs/`, written
in Lean 4 against Lean core + Std only: no Mathlib, no package dependencies, and
`lake` alone is enough to build them (no CMake, no Makefile).

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
The `bubble_sort` calls are modelled literally in `Tcs/Sort.lean` (the C++ loop, not
an equivalent sort), so that their exact comparison count can be formalized.

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
  `-DwarningAsError=true`, and no `sorryAx` in the environment;
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
├── Tcs/Spec.lean          # Specification vocabulary (Sorted / Permutes / IsSort)
├── Tcs/Order.lean         # `Cmp`: a decidable total order on keys
├── Tcs/Count.lean         # Generic `List.countP` lemmas
├── Tcs/Perm.lean          # Swap → `Perm` bridge for in-place algorithms
├── Tcs/Select.lean        # Rank and selection specs (k-th smallest key)
├── Tcs/Sort.lean          # `bubble_sort`, modelled as the C++ loop
├── Tcs/Cyclesort.lean     # Verified cycle sort
├── Tcs/Bfprt.lean         # Verified BFPRT selection
├── Tcs/Merge.lean         # rotate, `merge_with_swap`, `inplace_merge_with_rotation`
├── Tcs/UnstableMerge.lean # block selection/merge and `inplace_unstable_merge`
├── lakefile.toml          # Lake package definition
├── lean-toolchain         # Pinned Lean toolchain
└── check.sh               # Proof-completeness audit (no sorry / sorryAx)
```
