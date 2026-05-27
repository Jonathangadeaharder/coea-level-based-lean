"""Aristotle cloud prover backend."""

from __future__ import annotations

import os
import shutil
import subprocess
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
    project_id: str | None = None


def preflight(config: ProverConfig) -> None:
    for var in config.requires_env:
        if not os.environ.get(var):
            raise RuntimeError(
                f"{var} is not set. Revoke any exposed key, create a new one at "
                "https://aristotle.harmonic.fun/dashboard/keys and add to ~/.zshrc."
            )
    if shutil.which(config.command) is None:
        raise RuntimeError(
            f"{config.command!r} not found. Install with: uv tool install aristotlelib"
        )


def _build_prompt(proof_dir: Path, attempt_file: Path) -> str:
    paper = proof_dir / "paper_source.md"
    paper_hint = ""
    if paper.exists():
        paper_hint = f" Read strategy from {paper.relative_to(proof_dir.parents[1])}."
    rel = attempt_file.relative_to(proof_dir.parents[1])
    return (
        f"Close ONLY the sorry in {rel}. Do not modify other files.{paper_hint} "
        "Replace the sorry with a complete proof that typechecks in this Lean 4.28 project."
    )


def run_aristotle(
    *,
    config: ProverConfig,
    project_root: Path,
    proof_dir: Path,
    attempt_file: Path,
    log_path: Path,
    wait: bool = True,
) -> RunResult:
    preflight(config)
    prompt = _build_prompt(proof_dir, attempt_file)
    cmd = [
        config.command,
        "submit",
        prompt,
        "--project-dir",
        str(project_root),
    ]
    if wait:
        cmd.append("--wait")

    log_path.parent.mkdir(parents=True, exist_ok=True)
    with log_path.open("w", encoding="utf-8") as log:
        log.write(f"$ {' '.join(cmd)}\n\n")
        log.flush()
        proc = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            cwd=project_root,
        )
        log.write(proc.stdout or "")

    ok = proc.returncode == 0
    project_id = None
    for line in (proc.stdout or "").splitlines():
        if "project" in line.lower() and len(line.split()) >= 2:
            # best-effort parse; aristotle prints project ids in output
            parts = line.strip().split()
            for part in parts:
                if len(part) >= 8 and part.isalnum():
                    project_id = part
                    break

    return RunResult(
        prover="aristotle",
        success=ok,
        log_path=log_path,
        output_path=log_path,
        message="aristotle submit finished" if ok else f"aristotle exited {proc.returncode}",
        project_id=project_id,
    )
