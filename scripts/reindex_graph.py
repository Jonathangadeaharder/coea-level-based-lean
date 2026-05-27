#!/usr/bin/env python3
"""Regenerate .mathprover/graph.json for this Lean project (bootstrap + MathProver indexer)."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--skip-bootstrap",
        action="store_true",
        help="Only backfill runs / merge attempts (requires existing graph.json)",
    )
    ap.add_argument(
        "--decorators",
        action="store_true",
        help="Use MathProver build_graph.py instead of bootstrap_graph.py",
    )
    args = ap.parse_args()

    try:
        from mathprover_bridge import mathprover_home, run_index_runs
    except FileNotFoundError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    if args.decorators:
        build = mathprover_home() / "scripts" / "build_graph.py"
        proc = subprocess.run(
            [sys.executable, str(build), "--root", str(ROOT), "--strict"],
            cwd=mathprover_home(),
            check=False,
        )
        if proc.returncode != 0:
            return proc.returncode
    elif not args.skip_bootstrap:
        bootstrap = ROOT / "scripts" / "bootstrap_graph.py"
        proc = subprocess.run([sys.executable, str(bootstrap)], cwd=ROOT, check=False)
        if proc.returncode != 0:
            return proc.returncode

    backfill = run_index_runs(ROOT, backfill=True)
    if backfill.returncode != 0:
        print(backfill.stderr or backfill.stdout, file=sys.stderr)
        return backfill.returncode
    if backfill.stderr.strip():
        print(backfill.stderr.strip(), file=sys.stderr)

    graph_path = ROOT / ".mathprover" / "graph.json"
    if not graph_path.exists():
        print(f"error: missing {graph_path}", file=sys.stderr)
        return 1

    merged = run_index_runs(ROOT, graph=True)
    if merged.returncode == 0 and merged.stdout.strip():
        graph_path.write_text(merged.stdout.strip() + "\n", encoding="utf-8")
    elif merged.returncode != 0:
        print(merged.stderr or merged.stdout, file=sys.stderr)
        return merged.returncode
    else:
        graph = json.loads(graph_path.read_text(encoding="utf-8"))
        from mathprover_bridge import merge_attempts_into_graph

        graph = merge_attempts_into_graph(ROOT, graph)
        graph_path.write_text(json.dumps(graph, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    nodes = len(json.loads(graph_path.read_text())["nodes"])
    print(f"[reindex_graph] updated {graph_path} ({nodes} nodes)", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
