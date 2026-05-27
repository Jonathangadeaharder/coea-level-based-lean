#!/usr/bin/env bash
# Pre-build ProofWidgets JS before lake build (cold CI cache).
set -euo pipefail

lake update
lake exe cache get

PW="$(find .lake/packages -maxdepth 1 -type d -iname 'proofwidgets*' | head -1)"
if [[ -n "$PW" && -f "$PW/package.json" ]]; then
  (
    cd "$PW"
    if [[ -f package-lock.json ]]; then
      npm ci
    else
      npm install
    fi
    npm run build
  )
fi

lake build ProofWidgets
