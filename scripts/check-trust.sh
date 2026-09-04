#!/usr/bin/env bash
set -euo pipefail

lean_sources=(RSListDecoding.lean)
while IFS= read -r source; do
  lean_sources+=("$source")
done < <(rg --files RSListDecoding --glob '*.lean')

if rg -n -w 'sorry|sorryAx|admit|unsafe' "${lean_sources[@]}"; then
  echo 'Lean source contains a forbidden proof hole or unsafe declaration.' >&2
  exit 1
fi

audited_sources=()
for source in "${lean_sources[@]}"; do
  if [[ "$source" != RSListDecoding/Assumptions.lean ]]; then
    audited_sources+=("$source")
  fi
done

if rg -n \
  '^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|noncomputable)[[:space:]]+)*(axiom|axioms|constant|constants)([[:space:]]|$)' \
  "${audited_sources[@]}"; then
  echo 'Trust-extending declarations are allowed only in RSListDecoding/Assumptions.lean.' >&2
  exit 1
fi

echo 'Trusted-source checks passed.'
