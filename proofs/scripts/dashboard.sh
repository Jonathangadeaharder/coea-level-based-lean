#!/usr/bin/env bash
# Print the state of every proof folder + the global sorry/axiom count.
# Usage: bash proofs/scripts/dashboard.sh

set -euo pipefail
cd "$(dirname "$0")/../.."

echo "=== Proof tree dashboard ==="
echo
printf "%-50s %-12s %s\n" "FOLDER" "STATE" "DEPS"
printf "%-50s %-12s %s\n" "----------------------------------------" "------------" "----"

while IFS= read -r status_md; do
  folder=$(dirname "$status_md" | sed 's|^./||')
  state=$(grep '^state:' "$status_md" | sed 's/state: //')
  deps=$(grep '^depends_on:' "$status_md" | sed 's/depends_on: //')
  printf "%-50s %-12s %s\n" "$folder" "$state" "$deps"
done < <(find proofs -name status.md | sort)

echo
echo "=== Global invariant ==="
echo -n "Sorries in tracked *.lean (excluding proofs/, examples/, .bak, .lake/): "
grep -rn '^\s*sorry\b' --include='*.lean' --exclude-dir='.lake' --exclude-dir='proofs' --exclude-dir='examples' --exclude-dir='.worktrees' --exclude-dir='.git' . | grep -v '\.lean\.bak' | wc -l | tr -d ' '
echo -n "Axioms in tracked *.lean (target: only level_based_theorem): "
grep -rn '^axiom \|^private axiom ' --include='*.lean' --exclude-dir='.lake' --exclude-dir='proofs' --exclude-dir='examples' --exclude-dir='.worktrees' --exclude-dir='.git' . | grep -v '\.lean\.bak' | wc -l | tr -d ' '

echo
echo "=== Frontier (state=todo, no unmet deps) ==="
while IFS= read -r status_md; do
  state=$(grep '^state:' "$status_md" | sed 's/state: //')
  if [ "$state" = "todo" ]; then
    dirname "$status_md" | sed 's|^./||'
  fi
done < <(find proofs -name status.md | sort)

echo
echo "=== MathProver graph ==="
if [ -n "${MATHPROVER_HOME:-}" ] && [ -f scripts/reindex_graph.py ]; then
  echo "Run: python3 scripts/reindex_graph.py"
elif [ -f .mathprover/graph.json ]; then
  echo "Graph: .mathprover/graph.json ($(python3 -c 'import json; print(len(json.load(open(".mathprover/graph.json"))["nodes"]))' 2>/dev/null || echo '?') nodes)"
else
  echo "No graph yet — set MATHPROVER_HOME and run: python3 scripts/reindex_graph.py"
fi
