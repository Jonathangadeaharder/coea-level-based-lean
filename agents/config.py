"""Load mathprover.toml configuration."""

from __future__ import annotations

import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

if sys.version_info >= (3, 11):
    import tomllib
else:
    import tomli as tomllib


@dataclass
class ProverConfig:
    name: str
    type: str
    command: str
    max_attempts: int = 8
    max_tokens: int = 8192
    requires_env: list[str] = field(default_factory=list)


@dataclass
class RoutingConfig:
    default_leaf: str
    default_capstone: str
    escalate_after_failures: int
    capstone_node: str
    leaves: list[dict[str, str]]
    second_wave: list[dict[str, Any]]
    capstone: list[dict[str, Any]]


@dataclass
class MathProverConfig:
    project_root: Path
    provers: dict[str, ProverConfig]
    routing: RoutingConfig


def load_config(project_root: Path | None = None) -> MathProverConfig:
    root = (project_root or Path(__file__).resolve().parents[1]).resolve()
    path = root / "mathprover.toml"
    if not path.exists():
        raise FileNotFoundError(f"Missing config: {path}")

    with path.open("rb") as f:
        raw = tomllib.load(f)

    provers: dict[str, ProverConfig] = {}
    for name, block in raw.get("provers", {}).items():
        provers[name] = ProverConfig(
            name=name,
            type=block["type"],
            command=block["command"],
            max_attempts=int(block.get("max_attempts", 8)),
            max_tokens=int(block.get("max_tokens", 8192)),
            requires_env=list(block.get("requires_env", [])),
        )

    routing_raw = raw["routing"]
    routing = RoutingConfig(
        default_leaf=routing_raw["default_leaf"],
        default_capstone=routing_raw["default_capstone"],
        escalate_after_failures=int(routing_raw["escalate_after_failures"]),
        capstone_node=routing_raw["capstone_node"],
        leaves=list(routing_raw.get("leaves", [])),
        second_wave=list(routing_raw.get("second_wave", [])),
        capstone=list(routing_raw.get("capstone", [])),
    )
    return MathProverConfig(project_root=root, provers=provers, routing=routing)
