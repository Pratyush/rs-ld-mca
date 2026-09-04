# Reed--Solomon list-decoding Lean certificate

This is the source-only Lean certificate for the combinatorial and algorithmic
Reed--Solomon list-decoding theorems. It does not contain Mathlib, the local
`.lake` build/cache directory, the LaTeX manuscript, generated PDFs, editor
configuration, or Git history.

The exact propositions are in `RSListDecoding/Statements.lean`. The short
trusted surface is `RSListDecoding/Main.lean`:

- `RSListDecoding.combinatorial_main` proves the list-size theorem.
- `RSListDecoding.algorithmic_main` proves exact decoder correctness and the
  finite-field-operation bound.

The only project-specific assumptions are the cardinality and algorithmic
clauses of Kopparty's Theorem 4.3, both declared and documented in
`RSListDecoding/Assumptions.lean`. The kernel dependency checks are in
`RSListDecoding/Audit/AxiomAudit.lean`.

## Verification

Install `elan`, then run:

~~~bash
lake exe cache get
lake build --wfail
lake env lean --trust=0 RSListDecoding/Main.lean -DwarningAsError=true
./scripts/check-trust.sh
~~~

The first command downloads Mathlib's compiled cache outside the certificate
sources. The pinned versions are recorded in `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`.

The runtime theorem counts base-field additions, subtractions, negations,
multiplications, inversions, and equality tests. It is not a bit-complexity,
memory-use, or wall-clock-time claim.
