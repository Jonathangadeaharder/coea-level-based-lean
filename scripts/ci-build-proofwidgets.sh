#!/usr/bin/env bash
# Pre-build ProofWidgets widget bundle before `lake build` (cold CI cache).
set -euo pipefail

lake update
lake exe cache get

PW="$(find .lake/packages -maxdepth 1 -type d -iname 'proofwidgets*' | head -1)"
WIDGET="${PW:+$PW/widget}"

if [[ -n "$WIDGET" && -f "$WIDGET/package.json" ]]; then
  (
    cd "$WIDGET"
    if [[ -f package-lock.json ]]; then
      npm ci
    else
      npm install
    fi
    npm run build
  )
elif [[ -n "$PW" ]]; then
  lake build ProofWidgets
fi
