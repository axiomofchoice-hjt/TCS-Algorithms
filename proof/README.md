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

### In-place stable merge — `Tcs/StableMerge.lean` … `Tcs/StableMergeTop.lean`

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
* `uniqueLimit_sorted_keysNodup` — the buffer the three-argument
  `stable_unique_limit` builds is sorted and its keys are pairwise different, and
  `uniqueLimit_perm` says nothing is lost. The model (`keepUnique`/`uniqueLimitAux`/
  `uniqueLimit`) is the C++ loop, with the buffer held in the accumulator that the
  C++ keeps contiguously just before the scanned position: `UniqueInv` records that
  the buffer's last key is the largest kept key, which is what makes the C++
  comparison against `*(right - 1)` sufficient.
* `scrollRight_spec` — **the scroll-right pass of the stable
  `inplace_merge_with_rotation` is exactly `mergeTwo`** on its two runs. The model
  keeps the state as `P ++ A ++ B` (the final prefix plus the two remaining runs) and
  `fuel` bounds `A.length + B.length`; `splitRight`/`splitEq` are the C++'s two inner
  scans, written as recursions so that "everything below `a`" and "everything equal to
  `a`" stay plain inductions. One turn needs only the two block facts about a merge:
  `mergeTwo_append_right_eq` (a right-run block entirely below the left head is emitted
  first) and `mergeTwo_append_left_eq` (a left run starting at or below the right keys
  is emitted first). `scrollRight_eq_mergeTwo` is the whole pass from an empty prefix.

Cross-checked against the C++ (element-wise, with original indices attached):

* the three-argument overload's net effect is exactly "the first occurrence of each
  of the first `max` distinct keys, then the skipped elements in order" — 0 violations
  in 19,680 randomized sorted runs;
* the four-argument overload returns the same buffer, but its remainder is *not* in
  the stable order (9,280/19,680 differ), so the later stages do real work rather than
  a formality;
* per-key order is preserved by `stable_unique_limit`, `align_blocks_limit`,
  `block_merge_pairwise`, `bubble_sort` and both rotation merges, and only
  `block_selection_sort` reorders equal keys (9,145/26,400 cases), which the pairwise
  merge then repairs — so the invariant to carry through the block phase is exactly
  `∀ k, keyFilter proj k state = keyFilter proj k input`;
* `inplace_merge_with_rotation` alone is the stable merge of its two runs — 0
  mismatches in 41,000 randomized cases.

Still to model: the assembly (see the section at the end of this file). The
four-argument `stable_unique_limit`, `align_blocks_limit`, the dispatch of
`inplace_merge_with_rotation` and the labelled block phase are all modelled and
proved; the block phase is `Tcs/StableBlock.lean`.

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
  `List.take_add` (why `Cost/Bfprt.lean` keeps its own `take_add_groups`),
  `Nat.lt_of_mul_lt_mul_left`/`_right` (why `Cost/UnstableMerge.lean` keeps
  `um_mul_lt_cancel_right`), and `List.drop_take` (why `Tcs/Merge.lean` keeps its own
  `drop_take'`, which `Tcs/StableMerge.lean` reuses for `sorted_subrun`). A
  further trap is that `omega` applied to a goal whose context still holds list
  hypotheses can pick up `Classical.choice`; the arithmetic is therefore factored into
  pure-`Nat` helper lemmas, and the axiom audit below is run after every change;
- because core lemmas are not uniformly choice-free, a *core* lemma is worth checking
  with `#print axioms` before a proof is built on it, not after: both `List.drop_take`
  and `List.take_add` look like pure list plumbing. And since `AxiomAudit.lean` reports
  the offending declaration in `check.sh`'s output, the audit is read from
  `check.sh`'s **exit code** rather than from a filtered view of its output — a piped
  `check.sh | grep` reports `grep`'s status and has already let one tainted commit
  through;
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
├── Tcs/StableBlock.lean        # the labelled block phase, modelled with position tags
├── Tcs/StableBuffer.lean       # why the scratch region's order does not matter
├── Tcs/StableFinish.lean       # the two finishing rotation merges
├── Tcs/StableMergeTop.lean     # the assembly: `inplace_stable_merge` is the stable merge
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

## `inplace_stable_merge`: what is proved and what is left

The top-level target is `Tcs.StableMergeSpec proj L R l` - the result is sorted, it is a
permutation of the two runs, and it keeps every key's subsequence (the part that makes the
merge stable). `mergeTwo_stableMergeSpec` shows `mergeTwo L R` meets it and
`eq_mergeTwo_of_stableMergeSpec` shows that anything meeting it *is* `mergeTwo L R`, so the
specification characterises the stable merge exactly.

Every stage of the routine is proved, and each is in the form the assembly needs (`Perm`
plus per-key preservation, or a full `StableSort`/`StableMergeSpec`):

| stage | result |
| --- | --- |
| `stable_unique_limit` (3-arg) | `uniqueLimit_spec`, plus `uniqueLimit_buf_first` |
| `stable_unique_limit` (4-arg) | `uniqueLimitRange_spec`, plus `uniqueLimitRange_buf_first` |
| `align_blocks_limit` | `alignBlocksLimit_perm`, `alignBlocksLimit_keyFilter` |
| `inplace_merge_with_rotation` | `mergeByRotationStable_spec`, `perm_mergeByRotationStable`, `keyFilter_mergeByRotationStable` |
| `bubble_sort` | `bubbleSort_stableSort`, and `bubbleSort_eq_of_perm_of_keysNodup` for the scratch region |
| block decomposition | `blocksOf_flatten`, `blocksOf_length_le` |
| labelled block phase (`Tcs/StableBlock.lean`) | `blkPhaseData_spec` |
| finishing merges (`Tcs/StableFinish.lean`) | `finishMerge_noTail`, `finishMerge_tail`, `finishMerge_both` |
| assembly (`Tcs/StableMergeTop.lean`) | `stableMergePipeline_stableSort`, `stableMerge_stableMergeSpec` |

The end result is the objective itself:

```lean
stableMerge_stableMergeSpec (proj) (hL : Sorted (KeyLe proj) L) (hR : Sorted (KeyLe proj) R) :
    StableMergeSpec proj L R (stableMerge proj (L ++ R) L.length)
stableMerge_eq_mergeTwo (proj) (hL) (hR) :
    stableMerge proj (L ++ R) L.length = mergeTwo proj L R
```

so the model of `inplace_stable_merge`, run on two adjacent sorted runs, *is* their stable
merge; `stableMergeArray_stableMergeSpec` is the same statement in the C++ signature
(`Array`, `mid`). Nothing in the pipeline is left unproved.

### The assembly (`Tcs/StableMergeTop.lean`)

`stableMerge` is the list-level model of the C++ routine: below 25 elements it is
`bubbleSort`; otherwise it runs `uniqueLimitRange` on the two runs, takes the double-buffer
branch when the buffer came out at its full length `n / sqrt n + sqrt n` and the
single-buffer branch otherwise, and both branches share `stableMergePipeline` -
`alignBlocksLimit`, the labelled block phase `blkPhaseData` on the tagged blocks of the
aligned region, `bubbleSort` of the buffer, and the two finishing rotation merges
(`finishMerge_both`). The pipeline is proved to be a stable sort of `buf ++ L' ++ R'`
(`stableMergePipeline_stableSort`), and `uniqueLimitRange_spec` (the extraction only
permutes `L ++ R`, and preserves every key's subsequence) turns that into
`stableMerge_stableMergeSpec`. The two branch lemmas need one structural fact about
`alignBlocksLimit`: no `block_size`-sized block of its aligned prefix straddles the merge
boundary (which is a multiple of `block_size`), so every such block is internally sorted and
its tags increase - `alignLimit_le_tail_and_blocks` and its overshoot counterpart, which
also give that the untouched tail is sorted.

Two index-normalisation pitfalls cost attempts here and are worth remembering: `simp only`
does *not* rewrite `List.take_left` under the `Sorted` definition (use `rw [...]` then
`exact`), and one expression can need *opposite* normalisations in two places (the `take`
side wants `br ++ (sd ++ tail)`, the `drop` side `(br ++ sd) ++ tail`), so it pays to prove
the small `take_br`/`drop_br`/`drop_br_sd`/`take_drop_br` normalisations separately.

### The labelled block phase, via tags (`Tcs/StableBlock.lean`)

`block_selection_sort` + `block_merge_pairwise` + `inplace_block_merge_pairwise` were the
one part whose invariant was not obvious, because `block_selection_sort` is the single
stage that does *not* preserve per-key order on its own and the later merges repair it by
comparing `(key, label)` pairs. The modelling step is to name the labels: the C++ label of
a block is a buffer value whose order is the order of the blocks in the array, so tagging
an element at position `i` by `(x, i)` and comparing tagged elements by
`KeyLe (tagProj proj)` - the lexicographic order on `(key, tag)` pairs, `Tcs.Order`'s
`instCmpProdNat` - reproduces exactly the C++ tie-break, and turns the block phase into a
plain merge under a total order:

* `seqMergeTag`/`blkSortTag` model the pairwise merges and the block sort; `seqMergeTag`
  keeps only the *sorted* result, which is legitimate precisely because a merge writes a
  prefix of its result and carries the rest as its unfinished tail (the blog's "next merge
  only looks at the last part"), so `done ++ pending` is the merge of everything processed
  so far regardless of where the split falls;
* `tagFrom`/`taggedBlocks`/`tagProj` carry the positions, `blkPhaseData` erases them again;
* `blkPhaseData_spec` is the interface: for tagged blocks that partition a region,
  `blkPhaseData` is **key-sorted**, a **permutation** of the region, and **preserves every
  key's subsequence** - the last point is where stability comes from, because the tags
  increase along the array, so sorting by `(key, tag)` sorts equal keys into their input
  order. The proof of that point is `eq_of_sorted_perm` applied to the `k`-filters of the
  tagged merge and of `tagFrom off l` (both are sorted under the tag order and permutations
  of each other), with antisymmetry supplied by `tagFrom_snd_inj`.

This is a *behavioural* model of the labels, not a refinement: the C++ comparison reads
label *values* out of the buffer, while `StableBlock.lean` compares positions. The two were
cross-checked on the C++ itself, with an exact index-level Python simulation of
`stable_merge.hpp` validated element-wise against a reference stable merge (8008 exhaustive
inputs of length ≤ 10, then 20000 random inputs of length ≤ 120): after the block phase,
in **both** branches, the data region is exactly `sorted(blocks, key=(key, original
position))` and the buffer region keeps its multiset (0 mismatches; 3952 double-buffer and
11861 single-buffer cases). The model encodes exactly those two facts, and it keeps the
buffer region *unchanged*, which is sound because the buffer's keys are pairwise distinct
(`KeysNodup` from `uniqueLimitRange_spec`), so re-sorting it erases any permutation the
C++ may have left there.

The model of the *whole* routine (the `stableMerge` the assembly defines: same branch
tests, same `uniqueLimitRange`/`alignBlocksLimit`, data region `stable_sort_by_key`, buffer
region re-sorted, same two finishing merges) was then compared **element-wise** against the
C++ simulation, with each element carrying its original index so that equality witnesses
stability: 12376 exhaustive cases of length ≤ 11, plus 20000 random cases of length ≤ 200
covering 5005 double-buffer, 12494 single-buffer and 2501 `bubble_sort` runs, plus a further
120000 random cases of length ≤ 400 (29868 double-buffer, 75309 single-buffer, 14823
`bubble_sort`; 1820 exhaustive cases of length ≤ 12) - **0 mismatches** throughout. That is
the sense in which the Lean theorem below is about this C++.

The C++ side carries the other half: `tests/inplace/test_stable_merge.cpp` asserts exactly
`arr.is_stable() && arr == expected` (stability plus equality with a reference stable
merge) over its random families, sizes up to 100000, and the single-key/empty-half edge
cases; `xmake build test && ./build/tests/test --filter inplace_stable_merge` is
`121 passed, 0 failed`.

One consequence worth recording: the block *order* does not matter for the data region
(`seqMergeTag`'s result only depends on the tagged elements, not on how the blocks were
ordered), which is why `blkSortTag` is proved only to permute the blocks and keep each one
intact, and why `block_selection_sort`'s comparison can be modelled by any sort with the
same comparison.

Two faithful-abstraction details that are *not* proved, only cross-checked: (i) the C++
reads label *values* whose relative order stands in for the block order, and its label
array `buf1 + 1` overlaps the scratch block `buf2` by one slot (`labels[n_blocks]` is
`buf2[0]`), so late in the loop a label can be a scrambled scratch element; (ii) the C++
moves buffer elements in and out of the scratch window, so the scratch region only
survives the block phase as a *multiset*. Both are invisible in the cross-check above,
which is why it is stated as a differential test rather than a refinement proof. The part
of (ii) that could bite the model is closed by proof: `Tcs/StableBuffer.lean` shows that
`bubble_sort` is insensitive to the order of a list whose keys are pairwise different
(`bubbleSort_eq_of_perm_of_keysNodup`, using `KeysNodup` from `uniqueLimitRange_spec`), so
however the C++ scrambles the scratch region, re-sorting it gives the model's result.

Core lemmas that are *not* choice-free in this toolchain and therefore have constructive
replacements in the development: `List.take_add` (`Tcs.take_add'`), `List.drop_take`
(`Tcs.drop_take'`), `Nat.sqrt_le`/`Nat.lt_succ_sqrt`, `Nat.lt_of_mul_lt_mul_left`/`_right`.
