"""Goedel-Prover-V2-32B MLX backend."""

from __future__ import annotations

import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

from config import ProverConfig


@dataclass
class RunResult:
    prover: str
    success: bool
    log_path: Path
    output_path: Path | None
    message: str


def preflight(config: ProverConfig) -> None:
    run_sh = Path(os.path.expanduser(config.command)).resolve()
    if not run_sh.exists():
        raise RuntimeError(f"Goedel runner not found: {run_sh}")
    preflight_py = run_sh.parent / "preflight.py"
    if preflight_py.exists():
        subprocess.run(
            [sys.executable, str(preflight_py)],
            check=True,
            cwd=run_sh.parent,
        )


def run_goedel(
    *,
    config: ProverConfig,
    attempt_file: Path,
    log_path: Path,
    max_tokens: int | None = None,
) -> RunResult:
    preflight(config)
    run_sh = Path(os.path.expanduser(config.command)).resolve()
    tokens = max_tokens or config.max_tokens
    output_path = log_path.with_suffix(".out.txt")

    cmd = [
        str(run_sh),
        "--lean-file",
        str(attempt_file),
        "--max-tokens",
        str(tokens),
    ]
    log_path.parent.mkdir(parents=True, exist_ok=True)
    with log_path.open("w", encoding="utf-8") as log:
        log.write(f"$ {' '.join(cmd)}\n\n")
        log.flush()
        proc = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            cwd=attempt_file.parents[2],
        )
        log.write(proc.stdout or "")
        if proc.stdout:
            output_path.write_text(proc.stdout, encoding="utf-8")

    ok = proc.returncode == 0
    return RunResult(
        prover="goedel",
        success=ok,
        log_path=log_path,
        output_path=output_path if output_path.exists() else None,
        message="goedel finished" if ok else f"goedel exited {proc.returncode}",
    )
