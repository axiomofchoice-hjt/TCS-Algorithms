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
# command line back to its default, so the build mode is captured up front and
# re-passed to every configure below. Otherwise this script would silently
# downgrade a debug setup to release, making the 1s/file debug budget in
# AGENTS.md meaningless.
#
# `xmake show` locates the platform config file; that file is where the mode is
# actually recorded (`xmake show` prints only the mode). The lookup below fails
# loudly rather than guessing: falling back to `-m debug` is exactly the silent
# misconfiguration this script exists to avoid.
config_dir="$(xmake show 2>/dev/null | sed -e 's/\x1b\[[0-9;]*m//g' |
    sed -n 's/^ *configdir: *//p' | head -n1 || true)"
conf_file="${config_dir:+$config_dir/xmake.conf}"
if [ -z "$config_dir" ] || [ ! -f "$conf_file" ]; then
    echo "asan.sh: cannot locate the xmake config file (configdir='${config_dir:-<none>}'); run 'xmake f' first" >&2
    exit 1
fi

prev_mode="$(sed -n 's/^ *mode *= *"\([^"]*\)".*/\1/p' "$conf_file" | head -n1 || true)"
if [ -z "$prev_mode" ]; then
    echo "asan.sh: $conf_file does not record the build mode; refusing to reconfigure blindly" >&2
    exit 1
fi

restore() {
    # `$?` here is the status the script is exiting with (the test run's status),
    # so capture it before anything else overwrites it.
    local status=$?
    # Turn *off* the sanitize option (a bare `xmake f -y` keeps it set), keep the
    # mode, and rebuild so the binary on disk matches the restored config. These
    # failures must not be swallowed: otherwise the config could be restored
    # while build/tests/test is still sanitized, or vice versa.
    if ! xmake f -y -m "$prev_mode" --tcs_sanitize=n; then
        echo "asan.sh: failed to restore the xmake config; re-run: xmake f -m $prev_mode --tcs_sanitize=n" >&2
        status=1
    elif ! xmake -y; then
        echo "asan.sh: config restored, but the rebuild failed; build/tests/test may still be sanitized" >&2
        status=1
    else
        echo ">>> restored $prev_mode config (no sanitizers)" >&2
    fi
    exit "$status"
}
trap restore EXIT

echo ">>> xmake f -m $prev_mode --tcs_sanitize=y" >&2
xmake f -y -m "$prev_mode" --tcs_sanitize=y

echo ">>> xmake" >&2
xmake -y

echo ">>> xmake run test $*" >&2
xmake run test "$@"
