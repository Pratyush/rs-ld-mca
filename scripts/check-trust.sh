#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$script_dir/.." && pwd)"
cd "$repo_root"

lean_sources=(RSListDecoding.lean)
while IFS= read -r source; do
  lean_sources+=("$source")
done < <(rg --files RSListDecoding --glob '*.lean')

if rg -n -w 'sorry|sorryAx|admit|unsafe' "${lean_sources[@]}"; then
  echo 'Lean source contains a forbidden proof hole or unsafe declaration.' >&2
  exit 1
fi

if rg -n \
  '^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|noncomputable)[[:space:]]+)*(axiom|axioms|constant|constants)([[:space:]]|$)' \
  "${lean_sources[@]}"; then
  echo 'Lean source contains a trust-extending declaration.' >&2
  exit 1
fi

echo 'Trusted-source checks passed.'
