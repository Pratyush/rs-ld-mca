#!/usr/bin/env python3
"""Exact small-field check of the paper's local-rank subtraction.

For tiny ``d,m,W`` this constructs the universal map

    Gamma : V -> F_q[T,E,Y_1,...,Y_d]_{T+dE<m}

by expanding ``U = E + sum_j (-1)^(j+1) T^(j-1)Y_j``.  It then compares
the matrix rank with the kernel-subtracted bound of Lemmas 3.11--3.12.
This is an experiment, not a replacement for the Lean proof.
"""

from __future__ import annotations

import argparse
import itertools
import json
from typing import Iterable, Iterator

from exact_quadratic_evaluator import Parameters, paper_local_rank_count
from full_kernel_experiment import LocalExponent, local_mul, local_pow, rref_and_nullspace


def higher_exponents(d: int, budget: int) -> Iterator[tuple[int, ...]]:
    """Enumerate ``(Y_2,...,Y_d)`` exponents of anisotropic weight at most budget."""
    if d <= 1:
        yield ()
        return
    ranges = [range(budget // weight + 1) for weight in range(1, d)]
    for exponent in itertools.product(*ranges):
        if sum(weight * value for weight, value in enumerate(exponent, start=1)) <= budget:
            yield exponent


def v_monomials(d: int, m: int, W: int) -> list[LocalExponent]:
    """The monomial basis of the paper's intermediate space ``V``."""
    return [
        (t, u, y1) + higher
        for t in range(m)
        for u in range(t + 1)
        for y1 in range(m + 1)
        for higher in higher_exponents(d, W + t)
    ]


def rewrite_v_monomial(
    exponent: LocalExponent, q: int, d: int, m: int
) -> dict[LocalExponent, int]:
    """Rewrite one ``T,U,Y`` monomial and project to contact order below ``m``."""
    width = d + 2
    zero: LocalExponent = (0,) * width
    t, u, *jets = exponent
    base = list(zero)
    base[0] = t
    for index, value in enumerate(jets):
        base[index + 2] = value
    result = {tuple(base): 1}

    rewrite_u: dict[LocalExponent, int] = {}
    e_term = list(zero)
    e_term[1] = 1
    rewrite_u[tuple(e_term)] = 1
    for index in range(d):
        term = list(zero)
        term[0] = index
        term[index + 2] = 1
        rewrite_u[tuple(term)] = 1 if index % 2 == 0 else -1 % q
    result = local_mul(result, local_pow(rewrite_u, u, q, m), q, m)
    return {
        local_exponent: coefficient
        for local_exponent, coefficient in result.items()
        if local_exponent[0] + d * local_exponent[1] < m
    }


def run_local_rank_experiment(q: int, d: int, m: int, W: int) -> dict[str, int | bool]:
    if q < 2 or any(q % divisor == 0 for divisor in range(2, int(q**0.5) + 1)):
        raise ValueError("q must be prime")
    if d < 1 or m < 1 or W < 0:
        raise ValueError("d and m must be positive and W nonnegative")
    monomials = v_monomials(d, m, W)
    expansions = [rewrite_v_monomial(exponent, q, d, m) for exponent in monomials]
    rows = sorted({exponent for expansion in expansions for exponent in expansion})
    row_number = {exponent: index for index, exponent in enumerate(rows)}
    matrix = [[0] * len(monomials) for _ in rows]
    for column, expansion in enumerate(expansions):
        for exponent, coefficient in expansion.items():
            matrix[row_number[exponent]][column] = coefficient
    rank, kernel_basis = rref_and_nullspace(matrix, q)
    dummy = Parameters(d=d, m=m, W=W, C=0, n=1, A=1, K=2, B=1)
    paper_bound = paper_local_rank_count(dummy)
    return {
        "q": q,
        "d": d,
        "m": m,
        "W": W,
        "domain_dimension": len(monomials),
        "codomain_support": len(rows),
        "rank": rank,
        "kernel_dimension": len(kernel_basis),
        "paper_rank_bound": paper_bound,
        "rank_le_paper_bound": rank <= paper_bound,
        "rank_eq_paper_bound": rank == paper_bound,
    }


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--q", type=int, required=True)
    result.add_argument("--d", type=int, required=True)
    result.add_argument("--m", type=int, required=True)
    result.add_argument("--W", type=int, required=True)
    return result


def main(argv: Iterable[str] | None = None) -> int:
    args = parser().parse_args(argv)
    print(json.dumps(run_local_rank_experiment(args.q, args.d, args.m, args.W), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
