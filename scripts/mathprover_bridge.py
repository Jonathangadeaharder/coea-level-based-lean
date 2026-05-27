"""Resolve MathProver tooling paths from a Lean project (independent of monorepo layout)."""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path


def mathprover_home() -> Path:
    env = os.environ.get("MATHPROVER_HOME", "").strip()
    if env:
        home = Path(env).expanduser().resolve()
    else:
        # Common sibling clone: phd/lean-runtime-analysis + phd/mathprover
        sibling = Path(__file__).resolve().parents[2] / "mathprover"
        home = sibling.resolve()

    dispatch = home / "agents" / "dispatch.py"
    if not dispatch.is_file():
        raise FileNotFoundError(
            "MathProver not found. Clone https://github.com/VidiomTM/mathprover and set:\n"
            "  export MATHPROVER_HOME=/path/to/mathprover"
        )
    return home


def index_runs_script() -> Path:
    script = mathprover_home() / "scripts" / "index_runs.py"
    if not script.is_file():
        raise FileNotFoundError(f"Missing MathProver indexer: {script}")
    return script


def run_index_runs(
    project_root: Path,
    *,
    backfill: bool = False,
    graph: bool = False,
) -> subprocess.CompletedProcess[str]:
    args = [sys.executable, str(index_runs_script()), "--root", str(project_root.resolve())]
    if backfill:
        args.append("--backfill")
    if graph:
        args.append("--graph")
    env = {**os.environ, "MATHPROVER_HOME": str(mathprover_home())}
    return subprocess.run(
        args,
        cwd=mathprover_home(),
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )


def merge_attempts_into_graph(project_root: Path, graph: dict) -> dict:
    """Merge run history via MathProver's index_runs (requires MATHPROVER_HOME)."""
    home = mathprover_home()
    agents = home / "agents"
    scripts = home / "scripts"
    for path in (agents, scripts):
        if str(path) not in sys.path:
            sys.path.insert(0, str(path))
    os.environ.setdefault("MATHPROVER_HOME", str(home))

    from index_runs import merge_attempts_into_graph as _merge  # noqa: WPS433

    return _merge(project_root.resolve(), graph)
