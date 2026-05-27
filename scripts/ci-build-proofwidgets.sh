#!/usr/bin/env bash
# Warm Lean + ProofWidgets caches before `lake build` (cold CI runners).
set -euo pipefail

lake update

# Shared .lake symlinks can leave stale ProofWidgets JS; force a cloud refetch.
PW="$(find .lake/packages -maxdepth 1 -type d -iname 'proofwidgets*' | head -1)"
if [[ -n "$PW" ]]; then
  rm -rf "$PW/.lake/build"
fi

lake exe cache get
