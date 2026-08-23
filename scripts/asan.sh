#!/usr/bin/env bash
# Manual ASan+UBSan build & run (on-demand, not CI).
#
# Builds the local test/example binaries with AddressSanitizer and
# UndefinedBehaviorSanitizer, then runs the test suite — or a subset of it —
# under the sanitizers. Any extra arguments are forwarded to the test binary,
# so you can scope a run down (useful: sanitizers + a huge parameter range can
# exhaust memory, so pull the trigger surgically):
#
#   scripts/asan.sh                              # full test suite under ASan+UBSan
#   scripts/asan.sh --filter onepass_median      # one suite
#   scripts/asan.sh --filter stable_merge        # by name substring
#
# The xmake config is restored to the default (non-sanitized) state afterward,
# even if the build or test fails.
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
