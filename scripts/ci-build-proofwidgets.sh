#!/usr/bin/env bash
# Warm Lean + ProofWidgets caches before `lake build`.
set -euo pipefail

lake update
lake exe cache get
