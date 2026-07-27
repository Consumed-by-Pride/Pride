#!/bin/bash
# scripts/push.sh — commit and push everything to dev branch
# Usage: bash scripts/push.sh "commit message"
set -e
cd "$(dirname "$0")/.."
git config user.name "Pride Dev" 2>/dev/null || true
git config user.email "pride@pridelang.dev" 2>/dev/null || true
MSG="${1:-wip: auto-commit $(date -u +%Y-%m-%dT%H:%M:%SZ)}"
git add -A
git diff --cached --quiet && echo "Nothing to commit" && exit 0
git commit -m "$MSG"
git push origin dev
echo "Pushed to dev: $MSG"
