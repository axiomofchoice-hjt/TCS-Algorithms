#!/usr/bin/env bash
# Lean proof-completeness audit for proof/: rebuild everything, then type check
# each file with -DwarningAsError=true (which catches `sorry`), then grep for
# sorryAx. Lake only compiles imported modules, so step 2 walks the tree.
#
# Usage: ./proof/check.sh
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

# elan-installed toolchains are not on PATH in a non-interactive shell.
if [ -d "$HOME/.elan/bin" ]; then
    export PATH="$HOME/.elan/bin:$PATH"
fi

if ! command -v lake >/dev/null 2>&1; then
    echo "lake not found: install elan first (https://github.com/leanprover/elan)" >&2
    exit 2
fi

RED=$'\033[0;31m'
GREEN=$'\033[0;32m'
NC=$'\033[0m'
LOG="$PWD/.audit.log"
trap 'rm -f "$LOG"' EXIT
FAIL=0

echo ">>> 1/4 full rebuild (clearing olean cache)"
rm -rf .lake/build/lib/lean
lake build 2>&1 | tee "$LOG" | grep -E "error|warning|Build completed" || true
grep -q "Build completed successfully" "$LOG" || FAIL=1

echo
echo ">>> 2/4 strict per-file type check (-DwarningAsError=true)"
: > "$LOG"
# AxiomAudit.lean is a script, not a proof module: step 4 runs it separately.
mapfile -t FILES < <(find . -name '*.lean' -not -path './.lake/*' \
    -not -name 'AxiomAudit.lean' | sort)
for f in "${FILES[@]}"; do
    out=$(lake env lean -DwarningAsError=true "$f" 2>&1)
    rc=$?
    printf '%s\n' "$out" >> "$LOG"
    if [ "$rc" -ne 0 ]; then
        printf '%s\n' "$out" | grep -E 'error' | head -5 | sed 's/^/       /'
        echo "  x $f (exit $rc)"
        FAIL=1
    fi
done
echo "  scanned ${#FILES[@]} .lean file(s)"

echo
echo ">>> 3/4 axiom audit (no sorryAx)"
if grep "sorryAx" "$LOG" | grep -qv "summary:"; then
    echo "  x a theorem depends on sorryAx:"
    grep -n "sorryAx" "$LOG" | sed 's/^/     /'
    FAIL=1
fi

echo
echo ">>> 4/4 choice-freeness audit (no Classical.choice)"
AXIOMS=$(lake env lean -DwarningAsError=true AxiomAudit.lean 2>&1)
rc=$?
printf '%s\n' "$AXIOMS" | grep -E '^(CHOICE|SORRY|  axioms|axiom audit|summary)' | sed 's/^/  /'
printf '%s\n' "$AXIOMS" >> "$LOG"
if [ "$rc" -ne 0 ] || printf '%s\n' "$AXIOMS" | grep -q "^CHOICE "; then
    echo "  x a theorem depends on Classical.choice:"
    printf '%s\n' "$AXIOMS" | grep "^CHOICE " | head -20 | sed 's/^/     /'
    FAIL=1
fi

echo
if [ "$FAIL" -eq 0 ]; then
    echo "${GREEN}✓ no sorry / admit; all proofs complete${NC}"
else
    echo "${RED}✗ audit failed${NC}"
fi
exit "$FAIL"
