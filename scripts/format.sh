#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

find "$PROJECT_DIR/include" "$PROJECT_DIR/tests" "$PROJECT_DIR/examples" \
    -type f '(' -name '*.hpp' -o -name '*.h' -o -name '*.cpp' ')' \
    -exec clang-format -i {} +

echo "Formatted all C++ files."
