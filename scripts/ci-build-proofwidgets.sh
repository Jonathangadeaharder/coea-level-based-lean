#!/usr/bin/env bash
# Warm Lean + ProofWidgets caches before `lake build` (cold CI runners).
set -euo pipefail

lake update

PW="$(find .lake/packages -maxdepth 1 -type d -iname 'proofwidgets*' | head -1)"
if [[ -n "$PW" ]]; then
  rm -rf "$PW/.lake/build"
fi

lake exe cache get

# Cloud release can succeed while widgetJsAll trace is still stale on shared runners.
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
  lake --dir "$PW" build widgetJsAll
fi
