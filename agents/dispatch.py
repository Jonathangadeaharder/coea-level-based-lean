#!/usr/bin/env python3
"""CLI: dispatch a proof node to Goedel or Aristotle."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

AGENTS_DIR = Path(__file__).resolve().parent
if str(AGENTS_DIR) not in sys.path:
    sys.path.insert(0, str(AGENTS_DIR))

from backends.aristotle import run_aristotle  # noqa: E402
from backends.goedel import run_goedel  # noqa: E402
from config import load_config  # noqa: E402
from resource_guard import ResourceGuardError, ResourceLimits, goedel_exclusive_lock  # noqa: E402
from router import select_prover  # noqa: E402


def resolve_proof_folder(node: str, project_root: Path) -> str:
    proofs = project_root / "proofs"
    node = node.strip().removesuffix("/")

    direct = proofs / node
    if direct.is_dir():
        return node

    matches = sorted(p for p in proofs.glob(f"{node}*") if p.is_dir())
    if len(matches) == 1:
        return matches[0].name

    graph_path = project_root / ".mathprover" / "graph.json"
    if graph_path.exists():
        graph = json.loads(graph_path.read_text(encoding="utf-8"))
        for entry in graph.get("nodes", []):
            node_id = entry.get("id", "")
            theorem = entry.get("lean_theorem", "")
            if node in {node_id, theorem}:
                for folder in proofs.iterdir():
                    if folder.is_dir() and theorem and theorem in folder.name:
                        return folder.name
            if node_id.startswith(node) or node.startswith(node_id.split("_")[0]):
                theorem = entry.get("lean_theorem", "")
                for folder in proofs.iterdir():
                    if folder.is_dir() and theorem and theorem in folder.name:
                        if node_id == node or node in folder.name:
                            return folder.name

    raise FileNotFoundError(
        f"Could not resolve proof folder for node {node!r}. "
        f"Use full folder name under proofs/, e.g. L703_mutation_prob_lower_bound."
    )


def timestamp() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def verify_build(project_root: Path, log_path: Path) -> tuple[bool, str]:
    cmd = ["lake", "build"]
    proc = subprocess.run(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        cwd=project_root,
    )
    with log_path.open("a", encoding="utf-8") as log:
        log.write("\n--- lake build ---\n")
        log.write(f"$ {' '.join(cmd)}\n\n")
        log.write(proc.stdout or "")
    return proc.returncode == 0, proc.stdout or ""


def append_status(proof_dir: Path, *, prover: str, ok: bool, log_rel: str) -> None:
    status = proof_dir / "status.md"
    stamp = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    line = f"\n- [{stamp}] {prover}: {'ok' if ok else 'failed'} — log `{log_rel}`\n"
    if status.exists():
        status.write_text(status.read_text(encoding="utf-8") + line, encoding="utf-8")
    else:
        status.write_text(f"state: {'done' if ok else 'todo'}\n{line}", encoding="utf-8")


def bump_graph_attempts(project_root: Path, folder: str, prover: str, ok: bool) -> None:
    graph_path = project_root / ".mathprover" / "graph.json"
    if not graph_path.exists():
        return
    graph = json.loads(graph_path.read_text(encoding="utf-8"))
    changed = False
    for entry in graph.get("nodes", []):
        theorem = entry.get("lean_theorem", "")
        node_id = entry.get("id", "")
        if theorem and theorem in folder or node_id in folder or folder.endswith(node_id):
            entry["attempts"] = int(entry.get("attempts", 0)) + 1
            if ok:
                entry["status"] = "PROVEN"
            changed = True
            break
    if not changed:
        return
    graph_path.write_text(json.dumps(graph, indent=2) + "\n", encoding="utf-8")


def dispatch(
    node: str,
    *,
    prover: str | None = None,
    auto: bool = True,
    max_tokens: int | None = None,
    skip_verify: bool = False,
) -> int:
    config = load_config()
    root = config.project_root
    folder = resolve_proof_folder(node, root)
    proof_dir = root / "proofs" / folder
    attempt_file = proof_dir / "attempt.lean"
    if not attempt_file.exists():
        raise FileNotFoundError(f"Missing attempt file: {attempt_file}")

    decision = select_prover(
        folder,
        config,
        override=prover,
        auto=auto,
    )
    prover_name = decision.prover
    prover_cfg = config.provers[prover_name]

    attempts_root = root / ".mathprover" / "attempts" / folder
    log_path = attempts_root / f"{timestamp()}.log"
    print(f"node={folder} prover={prover_name} reason={decision.reason}")
    print(f"log={log_path}")

    if prover_name == "goedel":
        limits = ResourceLimits(
            max_concurrent_goedel=config.resources.max_concurrent_goedel,
            min_free_memory_gib=config.resources.min_free_memory_gib,
        )
        try:
            with goedel_exclusive_lock(root, limits):
                result = run_goedel(
                    config=prover_cfg,
                    attempt_file=attempt_file,
                    proof_dir=proof_dir,
                    project_root=root,
                    log_path=log_path,
                    max_tokens=max_tokens,
                    resource_limits=limits,
                )
        except ResourceGuardError as exc:
            raise RuntimeError(str(exc)) from exc
    elif prover_name == "aristotle":
        result = run_aristotle(
            config=prover_cfg,
            project_root=root,
            proof_dir=proof_dir,
            attempt_file=attempt_file,
            log_path=log_path,
        )
    else:
        raise ValueError(f"Unsupported prover: {prover_name}")

    verify_ok = True
    if not skip_verify:
        verify_ok, _ = verify_build(root, log_path)

    ok = result.success and verify_ok
    log_rel = log_path.relative_to(root).as_posix()
    append_status(proof_dir, prover=prover_name, ok=ok, log_rel=log_rel)
    bump_graph_attempts(root, folder, prover_name, ok)

    print(result.message)
    print(f"verify={'ok' if verify_ok else 'failed'}")
    return 0 if ok else 1


def main() -> None:
    parser = argparse.ArgumentParser(description="Dispatch a MathProver proof node.")
    parser.add_argument("--node", required=True, help="Node id or proofs/ folder name")
    parser.add_argument(
        "--prover",
        choices=["goedel", "aristotle", "auto"],
        default="auto",
        help="Prover backend (default: auto via mathprover.toml)",
    )
    parser.add_argument("--max-tokens", type=int, default=None, help="Goedel token limit")
    parser.add_argument("--skip-verify", action="store_true", help="Skip lake build verify")
    args = parser.parse_args()

    override = None if args.prover == "auto" else args.prover
    try:
        code = dispatch(
            args.node,
            prover=override,
            auto=args.prover == "auto",
            max_tokens=args.max_tokens,
            skip_verify=args.skip_verify,
        )
    except Exception as exc:
        print(f"error: {exc}", file=sys.stderr)
        code = 2
    raise SystemExit(code)


if __name__ == "__main__":
    main()
