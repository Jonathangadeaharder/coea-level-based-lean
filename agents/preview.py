#!/usr/bin/env python3
"""Print routing decision as JSON for the UI preview endpoint."""

from __future__ import annotations

import json
import sys
from pathlib import Path

AGENTS_DIR = Path(__file__).resolve().parent
if str(AGENTS_DIR) not in sys.path:
    sys.path.insert(0, str(AGENTS_DIR))

from config import load_config  # noqa: E402
from dispatch import resolve_proof_folder  # noqa: E402
from router import select_prover  # noqa: E402


def preview(node: str, prover: str = "auto") -> dict:
    config = load_config()
    folder = resolve_proof_folder(node, config.project_root)
    override = None if prover == "auto" else prover
    decision = select_prover(folder, config, override=override, auto=prover == "auto")
    return {
        "folder": folder,
        "prover": decision.prover,
        "reason": decision.reason,
    }


def main() -> None:
    if len(sys.argv) < 2:
        print("usage: preview.py <node> [auto|goedel|aristotle]", file=sys.stderr)
        raise SystemExit(2)
    node = sys.argv[1]
    prover = sys.argv[2] if len(sys.argv) > 2 else "auto"
    print(json.dumps(preview(node, prover)))


if __name__ == "__main__":
    main()
