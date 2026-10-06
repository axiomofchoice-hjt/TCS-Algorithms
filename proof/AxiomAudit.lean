/-
  Choice-freeness audit.

  The proof tree's headline quality gate (see `README.md`, "Quality gates") is that no
  theorem depends on `Classical.choice`.  `check.sh` only greps for `sorryAx`, so this
  script closes the gap: it walks every declaration in the `Tcs` namespace, prints the
  axiom set each one depends on, and prints one `CHOICE <name>` line per offending
  declaration (which `check.sh` turns into a failure).

  The audit is cheap (~10 s) and is run by `./check.sh`.  It has already earned its
  keep: an `omega` call in a context with list hypotheses, and core's `List.take_add`,
  both sneak `Classical.choice` into an otherwise constructive proof.

  Manual run:
  ```
  lake env lean AxiomAudit.lean
  ```
-/
import Tcs
import Lean

open Lean Elab Command

private def isTcs (n : Name) : Bool := n == `Tcs || (`Tcs).isPrefixOf n

run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, _) in env.constants.toList do
    if isTcs n && !n.isInternal then names := names.push n
  let mut sets : List (List String) := []
  let mut choiceCnt : Nat := 0
  let mut sorryCnt : Nat := 0
  for n in names do
    let axs ← Lean.collectAxioms n
    let l := (axs.toList.map (·.toString)).mergeSort (· ≤ ·)
    if l.contains "Classical.choice" then
      choiceCnt := choiceCnt + 1
      logInfo m!"CHOICE {n} : {l}"
    if l.contains "sorryAx" then
      sorryCnt := sorryCnt + 1
      logInfo m!"SORRY {n} : {l}"
    sets := l :: sets
  logInfo m!"axiom audit: {names.size} declarations under Tcs"
  for l in sets.eraseDups do
    logInfo m!"  axioms {l}: {(sets.filter (· == l)).length}"
  logInfo m!"summary: Classical.choice {choiceCnt}, sorryAx {sorryCnt}"
