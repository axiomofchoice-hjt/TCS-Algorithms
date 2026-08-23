#!/usr/bin/env bash
# Manual ASan+UBSan build & run (on-demand, not CI).
# Extra arguments are forwarded to the test binary (e.g. --filter <suite>).
#
#   scripts/asan.sh                     # full test suite under ASan+UBSan
#   scripts/asan.sh --filter <suite>    # run a single suite
#
# Restores the default (non-sanitized) xmake config on exit.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
cd "$PROJECT_DIR"

restore() {
    # Explicitly turn *off* the sanitize option: `xmake f -y` alone keeps any
    # previously-set option, so it would leave ASan on for the next build.
    xmake f -y --tcs_sanitize=n >/dev/null 2>&1 || true
}
trap restore EXIT

echo ">>> xmake f --tcs_sanitize=y" >&2
xmake f -y --tcs_sanitize=y

echo ">>> xmake" >&2
xmake -y

echo ">>> xmake run test $*" >&2
xmake run test "$@"

echo ">>> restored default xmake config" >&2
