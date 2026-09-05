#!/usr/bin/env python3
"""Exhaust received words for one tiny full-kernel configuration."""

from __future__ import annotations

import argparse
import itertools
import json
from typing import Iterable

from full_kernel_experiment import ExperimentParameters, parse_csv, run_experiment


def sweep(
    *, q: int, d: int, m: int, W: int, C: int, n: int, A: int, K: int,
    B: int, alphas: tuple[int, ...], max_received_words: int,
) -> dict[str, int | bool]:
    received_words = q**n
    if received_words > max_received_words:
        raise ValueError(
            f"sweep needs {received_words} received words, above limit {max_received_words}"
        )
    nonempty = 0
    first_strictly_worse = 0
    every_basis_strictly_worse = 0
    some_basis_strictly_worse = 0
    maximum_first_excess = 0
    maximum_minimum_basis_excess = 0
    for received in itertools.product(range(q), repeat=n):
        result = run_experiment(
            ExperimentParameters(
                q=q, d=d, m=m, W=W, C=C, n=n, A=A, K=K, B=B,
                alphas=alphas, received=received,
            )
        )
        if result["kernel_dimension"] == 0:
            continue
        nonempty += 1
        roots = result["root_enumeration"]
        common = roots["full_kernel_common_roots"]
        counts = roots["basis_interpolant_root_counts"]
        first_excess = counts[0] - common
        minimum_excess = min(counts) - common
        first_strictly_worse += first_excess > 0
        some_basis_strictly_worse += any(count > common for count in counts)
        every_basis_strictly_worse += all(count > common for count in counts)
        maximum_first_excess = max(maximum_first_excess, first_excess)
        maximum_minimum_basis_excess = max(
            maximum_minimum_basis_excess, minimum_excess
        )
    return {
        "received_words": received_words,
        "nonempty_kernels": nonempty,
        "first_basis_strictly_worse": first_strictly_worse,
        "some_basis_strictly_worse": some_basis_strictly_worse,
        "every_basis_strictly_worse": every_basis_strictly_worse,
        "maximum_first_excess_roots": maximum_first_excess,
        "maximum_minimum_basis_excess_roots": maximum_minimum_basis_excess,
        "a_basis_vector_always_realized_common_roots": (
            maximum_minimum_basis_excess == 0
        ),
    }


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    for name in ("q", "d", "m", "W", "C", "n", "A", "K", "B"):
        result.add_argument(f"--{name}", type=int, required=True)
    result.add_argument("--alphas", type=parse_csv, required=True)
    result.add_argument("--max-received-words", type=int, default=100_000)
    return result


def main(argv: Iterable[str] | None = None) -> int:
    args = parser().parse_args(argv)
    if len(args.alphas) != args.n:
        raise ValueError("alphas must have length n")
    print(json.dumps(sweep(**vars(args)), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
