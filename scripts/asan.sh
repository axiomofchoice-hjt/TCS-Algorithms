#!/usr/bin/env bash
# Manual ASan+UBSan build & run (on-demand, not CI).
# Extra arguments are forwarded to the test binary (e.g. --filter <suite>).
#
#   scripts/asan.sh                     # full test suite under ASan+UBSan
#   scripts/asan.sh --filter <suite>    # run a single suite
#
# Restores the previous (non-sanitized) xmake config and rebuilds on exit.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
cd "$PROJECT_DIR"

# Passing *any* option to `xmake f` resets every option not named on that
# command line back to its default, so the mode and tcs_no_temp_impl are
# captured up front and re-passed to every configure below. Otherwise this
# script would silently downgrade a debug setup to release -- making the
# 1s/file debug budget in AGENTS.md meaningless -- and turn off the true
# in-place primitives it was meant to sanitize.
show="$(xmake show 2>/dev/null | sed -e 's/\x1b\[[0-9;]*m//g' || true)"
prev_mode="$(printf '%s\n' "$show" | sed -n 's/^ *mode: *//p' | head -n1 || true)"
prev_mode="${prev_mode:-debug}"
# `xmake show` exposes the mode but not option values, so read the option from
# the platform config file it points at.
config_dir="$(printf '%s\n' "$show" | sed -n 's/^ *configdir: *//p' | head -n1 || true)"
prev_no_temp_impl=""
if [ -n "$config_dir" ] && [ -f "$config_dir/xmake.conf" ]; then
    prev_no_temp_impl="$(sed -n 's/.*tcs_no_temp_impl *= *\(true\|false\).*/\1/p' \
        "$config_dir/xmake.conf" | head -n1 || true)"
fi
case "${prev_no_temp_impl:-false}" in
    true) prev_no_temp_impl=y ;;
    *) prev_no_temp_impl=n ;;
esac

restore() {
    # Turn *off* the sanitize option (a bare `xmake f -y` keeps it set), keep the
    # mode and tcs_no_temp_impl, and rebuild so the binary on disk matches the
    # restored config.
    xmake f -y -m "$prev_mode" --tcs_no_temp_impl="$prev_no_temp_impl" \
        --tcs_sanitize=n >/dev/null 2>&1 || true
    xmake -y >/dev/null 2>&1 || true
}
trap restore EXIT

echo ">>> xmake f -m $prev_mode --tcs_no_temp_impl=$prev_no_temp_impl --tcs_sanitize=y" >&2
xmake f -y -m "$prev_mode" --tcs_no_temp_impl="$prev_no_temp_impl" --tcs_sanitize=y

echo ">>> xmake" >&2
xmake -y

echo ">>> xmake run test $*" >&2
xmake run test "$@"

echo ">>> restored $prev_mode config (no sanitizers)" >&2
