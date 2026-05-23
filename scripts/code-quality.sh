#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m'

run_step() {
    local name="$1"
    shift
    echo ">>> $name" >&2
    if "$@"; then
        echo -e "${GREEN}✓ $name passed${NC}" >&2
    else
        echo -e "${RED}✗ $name failed${NC}" >&2
        return 1
    fi
    echo >&2
}

# clang-format
run_step "clang-format" find "$PROJECT_DIR/include" "$PROJECT_DIR/tests" \
    -type f '(' -name '*.hpp' -o -name '*.h' -o -name '*.cpp' -o -name '*.cc' -o -name '*.cxx' ')' \
    -exec clang-format --dry-run --Werror {} +

# clang-tidy
find "$PROJECT_DIR/include" "$PROJECT_DIR/tests" \
    -type f '(' -name '*.hpp' -o -name '*.h' -o -name '*.cpp' ')' -print0 \
    | xargs -0 -P "$(nproc)" clang-tidy -p "$PROJECT_DIR/build"
echo -e "${GREEN}✓ clang-tidy passed${NC}"

echo -e "${GREEN}All checks passed!${NC}"
