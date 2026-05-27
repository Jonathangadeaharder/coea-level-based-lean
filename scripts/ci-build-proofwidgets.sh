#!/usr/bin/env bash
# Warm Lean + ProofWidgets caches before `lake build` (cold CI runners).
set -euo pipefail

lake update
lake exe cache --include-proofwidgets get
