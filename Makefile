# lean-runtime-analysis — common tasks (requires sibling or env-configured MathProver)

MATHPROVER_HOME ?= $(abspath ../mathprover)
MATHPROVER_PROJECT_PATH ?= $(CURDIR)
NODE ?=
PROVER ?= auto

ifneq (,$(wildcard .env))
include .env
export
endif

export MATHPROVER_HOME MATHPROVER_PROJECT_PATH

.PHONY: help reindex ui dispatch dashboard build agents-sync meta

help:
	@echo "Targets:"
	@echo "  make reindex              Regenerate .mathprover/graph.json"
	@echo "  make ui                   Start MathProver workbench"
	@echo "  make dispatch NODE=...    Dispatch proof worker (PROVER=auto|goedel|aristotle)"
	@echo "  make dashboard            Proof folder status table"
	@echo "  make build                lake build LBTCoupling"
	@echo "  make agents-sync          uv sync in MathProver agents/"
	@echo "  make meta                 Copy meta.json.example → .mathprover/meta.json"
	@echo ""
	@echo "Set MATHPROVER_HOME in .env (see .env.example) if mathprover is not ../mathprover"

reindex:
	python3 scripts/reindex_graph.py

ui: agents-sync
	cd "$(MATHPROVER_HOME)/mathprover-ui" && pnpm install && pnpm dev

dispatch: agents-sync
	@test -n "$(NODE)" || (echo "Usage: make dispatch NODE=L661_coea_sel_measure_prob [PROVER=auto]" && exit 1)
	cd "$(MATHPROVER_HOME)/agents" && uv run python dispatch.py \
		--root "$(MATHPROVER_PROJECT_PATH)" \
		--node "$(NODE)" \
		--prover "$(PROVER)"

dashboard:
	bash proofs/scripts/dashboard.sh

build:
	lake build LBTCoupling

agents-sync:
	@test -d "$(MATHPROVER_HOME)/agents" || (echo "MathProver not found at $(MATHPROVER_HOME)" && exit 1)
	cd "$(MATHPROVER_HOME)/agents" && uv sync

meta:
	@mkdir -p .mathprover
	cp -n .mathprover/meta.json.example .mathprover/meta.json 2>/dev/null || \
		cp .mathprover/meta.json.example .mathprover/meta.json
	@echo "Wrote .mathprover/meta.json (edit for UI foundations/paper blocks)"
