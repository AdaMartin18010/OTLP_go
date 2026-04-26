#!/usr/bin/env bash
# compliance-check.sh
# Standards compliance checking script for OTLP_go project.
# Usage: ./scripts/compliance-check.sh

set -euo pipefail

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

ERRORS=0
WARNINGS=0

echo "=== OTLP_go Standards Compliance Check ==="

# 1. Stability annotation in each pkg/ directory (first non-test .go file)
echo ""
echo "-> Checking stability annotations in pkg/..."
declare -A checked_dirs
while IFS= read -r -d '' file; do
    dir=$(dirname "$file")
    if [[ -n "${checked_dirs[$dir]:-}" ]]; then
        continue
    fi
    checked_dirs["$dir"]=1
    entry=$(find "$dir" -maxdepth 1 -name '*.go' -not -name '*_test.go' -print0 | sort -z | head -z -n 1 | tr -d '\0')
    if [ -z "$entry" ]; then
        echo -e "${RED}FAIL${NC} No .go files in $dir (cannot add stability annotation)"
        ERRORS=$((ERRORS + 1))
        continue
    fi
    if ! grep -q "Stability:" "$entry"; then
        echo -e "${RED}FAIL${NC} Missing stability annotation in $entry"
        ERRORS=$((ERRORS + 1))
    fi
done < <(find pkg -type f -name '*.go' -not -name '*_test.go' -print0)

# 2. RFC 2119 keywords in docs/ (should be uppercase)
echo ""
echo "-> Checking RFC 2119 keyword usage in docs/..."
while IFS= read -r -d '' file; do
    # heuristic: detect lowercase must/should/may appearing as standalone English words
    matches=$(grep -inE '(^|[[:space:][:punct:]])(must|should|may|must not|should not)([[:space:][:punct:]]|$)' "$file" || true)
    if [ -n "$matches" ]; then
        echo -e "${YELLOW}WARN${NC} Lowercase RFC 2119 keyword candidate in $file:"
        echo "$matches" | head -n 3
        WARNINGS=$((WARNINGS + 1))
    fi
done < <(find docs -type f -name '*.md' -print0)

# 3. Hardcoded semantic convention strings (basic check)
echo ""
echo "-> Checking for hardcoded semantic convention strings..."
bad_lines=$(grep -rEn '"http\.method"|"db\.system"|"service\.name"|"telemetry\.sdk\.language"' pkg/ --include='*.go' | grep -v '_test.go' | grep -v 'semconv' | grep -v 'doc.go' || true)
if [ -n "$bad_lines" ]; then
    echo -e "${RED}FAIL${NC} Hardcoded semantic convention strings found:"
    echo "$bad_lines" | head -n 5
    ERRORS=$((ERRORS + 1))
fi

echo ""
if [ "$ERRORS" -eq 0 ] && [ "$WARNINGS" -eq 0 ]; then
    echo -e "${GREEN}PASS${NC} All compliance checks passed."
    exit 0
elif [ "$ERRORS" -eq 0 ]; then
    echo -e "${YELLOW}WARN${NC} $WARNINGS warning(s) found."
    exit 0
else
    echo -e "${RED}FAIL${NC} $ERRORS error(s) and $WARNINGS warning(s) found."
    exit 1
fi
