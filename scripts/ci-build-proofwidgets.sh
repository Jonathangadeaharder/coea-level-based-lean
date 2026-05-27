#!/usr/bin/env bash
# Pre-build ProofWidgets JS before lake build (cold CI cache).
set -euo pipefail

lake update

PW="$(find .lake/packages -maxdepth 1 -type d -name 'proofwidgets*' | head -1)"
if [[ -z "$PW" || ! -f "$PW/package.json" ]]; then
  lake build ProofWidgets
  exit 0
fi

(
  cd "$PW"
  if [[ -f package-lock.json ]]; then
    npm ci
  else
    npm install
  fi
  npm run build
)

lake build ProofWidgets
