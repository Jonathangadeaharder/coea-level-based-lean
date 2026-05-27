#!/usr/bin/env python3
"""Bootstrap .mathprover/graph.json from proofs/ folders when Lean decorators are absent."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

NODES = [
    {
        "id": "lbt_axiom",
        "paper_id": "Thm 3.1 (ext.)",
        "paper_name": "Level-Based Theorem (Corus et al. 2018) — trusted external axiom.",
        "lean_theorem": "level_based_theorem",
        "lean_file": "LBTCoupling.lean",
        "lean_line": 470,
        "status": "PROVEN",
        "depends_on": [],
        "importance": 0.95,
        "difficulty": "hard",
        "confidence": 1.0,
        "attempts": 0,
    },
    {
        "id": "L661_sel_prob",
        "paper_id": "Lemma 7.6a",
        "paper_name": "coea_sel_measure is a probability measure (telescoping CDF).",
        "lean_theorem": "coea_sel_measure_prob",
        "lean_file": "LBTCoupling.lean",
        "lean_line": 648,
        "status": "SORRIES",
        "depends_on": [],
        "proof_folder": "L661_coea_sel_measure_prob",
        "importance": 0.85,
        "difficulty": "hard",
        "confidence": 0.5,
        "attempts": 1,
        "isCapstone": False,
    },
    {
        "id": "L669_sel_cdf",
        "paper_id": "Lemma 7.6b",
        "paper_name": "Best-of-λ selection CDF identity.",
        "lean_theorem": "coea_sel_measure_cdf",
        "lean_file": "LBTCoupling.lean",
        "lean_line": 661,
        "status": "SORRIES",
        "depends_on": [],
        "proof_folder": "L669_coea_sel_measure_cdf",
        "importance": 0.85,
        "difficulty": "hard",
        "confidence": 0.5,
        "attempts": 0,
    },
    {
        "id": "L693_sel_mono",
        "paper_id": "Lemma 7.7",
        "paper_name": "Selection is monotone in the level ranking.",
        "lean_theorem": "sel_monotone_level",
        "lean_file": "LBTCoupling.lean",
        "lean_line": 685,
        "status": "SORRIES",
        "depends_on": ["L669_sel_cdf"],
        "proof_folder": "L693_sel_monotone_level",
        "importance": 0.8,
        "difficulty": "hard",
        "confidence": 0.4,
        "attempts": 0,
    },
    {
        "id": "L703_mut_lb",
        "paper_id": "Lemma 7.5",
        "paper_name": "Mutation probability lower bound.",
        "lean_theorem": "mutation_prob_lower_bound",
        "lean_file": "LBTCoupling.lean",
        "lean_line": 935,
        "status": "PROVEN",
        "depends_on": [],
        "proof_folder": "L703_mutation_prob_lower_bound",
        "importance": 0.9,
        "difficulty": "medium",
        "confidence": 1.0,
        "attempts": 3,
    },
    {
        "id": "L715_measure_ge",
        "paper_id": "Lemma 7.8",
        "paper_name": "Measure lower bound from count (coea).",
        "lean_theorem": "coea_measure_ge_from_count",
        "lean_file": "LBTCoupling.lean",
        "lean_line": 935,
        "status": "SORRIES",
        "depends_on": ["L703_mut_lb"],
        "proof_folder": "L715_coea_measure_ge_from_count",
        "importance": 0.85,
        "difficulty": "hard",
        "confidence": 0.45,
        "attempts": 0,
    },
    {
        "id": "L1012_r_local_G2",
        "paper_id": "Lemma G2",
        "paper_name": "Local G2 growth rate — capstone.",
        "lean_theorem": "r_local_G2",
        "lean_file": "LBTCoupling.lean",
        "lean_line": 1224,
        "status": "SORRIES",
        "depends_on": ["L669_sel_cdf", "L715_measure_ge"],
        "proof_folder": "L1012_r_local_G2",
        "importance": 1.0,
        "difficulty": "hard",
        "confidence": 0.35,
        "attempts": 0,
        "isCapstone": True,
    },
]


def worker_state(folder: str) -> str | None:
    path = ROOT / "proofs" / folder / "status.md"
    if not path.exists():
        return None
    m = re.search(r"^state:\s*(\S+)", path.read_text(encoding="utf-8"), re.MULTILINE)
    return m.group(1) if m else None


def main() -> int:
    nodes = []
    for n in NODES:
        node = dict(n)
        folder = node.get("proof_folder")
        if folder:
            ws = worker_state(folder)
            if ws:
                node["worker_state"] = ws
        nodes.append(node)

    graph = {
        "project": {
            "name": ROOT.name,
            "path": str(ROOT),
            "paper": "",
            "authors": "",
            "venue": "",
            "capstone": "L1012_r_local_G2",
            "lastVerified": "",
        },
        "recents": [],
        "nodes": nodes,
        "definitions": [],
        "foundations": [],
        "paperBlocks": [],
        "leanBlocks": [],
        "terms": {},
        "failures": [],
        "activeAgent": None,
    }

    out = ROOT / ".mathprover" / "graph.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(graph, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"[bootstrap_graph] wrote {out} ({len(nodes)} nodes)", file=sys.stderr)

    sys.path.insert(0, str(ROOT / "scripts"))
    try:
        from mathprover_bridge import merge_attempts_into_graph
    except FileNotFoundError as exc:
        print(f"[bootstrap_graph] warning: {exc}", file=sys.stderr)
        return 0

    graph = json.loads(out.read_text(encoding="utf-8"))
    graph = merge_attempts_into_graph(ROOT, graph)
    out.write_text(json.dumps(graph, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
