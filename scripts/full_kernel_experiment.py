#!/usr/bin/env python3
"""Small-field experiment for using the full interpolation kernel.

This is deliberately an exact, dense reference implementation, not a decoder.
It constructs the interpolation matrix from the same two local substitutions as
the Lean development, computes a basis of its nullspace over a prime field, and
compares polynomial solutions of

* one nonzero interpolant from that nullspace, and
* every interpolant in a nullspace basis.

The experiment is intended for tiny parameters.  Its purpose is to test whether
the *common* differential zero set has far fewer free initial coefficients than
the zero set of a single nonlinear differential equation.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from collections import defaultdict
from dataclasses import asdict, dataclass
from typing import Iterable, Iterator, Sequence


LocalExponent = tuple[int, ...]  # (T, E, Y_1, ..., Y_d)
GlobalExponent = tuple[int, ...]  # (X, Y_0, ..., Y_d)
Polynomial = tuple[int, ...]  # coefficients in ascending order


@dataclass(frozen=True)
class ExperimentParameters:
    q: int
    d: int
    m: int
    W: int
    C: int
    n: int
    A: int
    K: int
    B: int
    alphas: tuple[int, ...]
    received: tuple[int, ...]

    def validate(self) -> None:
        if self.q < 2 or any(
            self.q % divisor == 0 for divisor in range(2, math.isqrt(self.q) + 1)
        ):
            raise ValueError("q must be prime")
        if self.d < 1 or self.m < 1 or self.K < 1:
            raise ValueError("d, m, and K must be positive")
        if len(self.alphas) != self.n or len(self.received) != self.n:
            raise ValueError("alphas and received must have length n")
        if len(set(value % self.q for value in self.alphas)) != self.n:
            raise ValueError("evaluation points must be distinct modulo q")
        if not 0 <= self.A <= self.n:
            raise ValueError("A must lie between zero and n")


def poly_trim(poly: Sequence[int], q: int) -> Polynomial:
    values = [value % q for value in poly]
    while values and values[-1] == 0:
        values.pop()
    return tuple(values)


def poly_add(left: Polynomial, right: Polynomial, q: int) -> Polynomial:
    size = max(len(left), len(right))
    return poly_trim(
        [
            (left[i] if i < len(left) else 0)
            + (right[i] if i < len(right) else 0)
            for i in range(size)
        ],
        q,
    )


def poly_scale(poly: Polynomial, scalar: int, q: int) -> Polynomial:
    return poly_trim([scalar * value for value in poly], q)


def poly_mul(left: Polynomial, right: Polynomial, q: int) -> Polynomial:
    if not left or not right:
        return ()
    result = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] = (result[i + j] + a * b) % q
    return poly_trim(result, q)


def poly_pow(poly: Polynomial, exponent: int, q: int) -> Polynomial:
    result: Polynomial = (1,)
    base = poly
    while exponent:
        if exponent & 1:
            result = poly_mul(result, base, q)
        base = poly_mul(base, base, q)
        exponent //= 2
    return result


def hasse_derivative(poly: Polynomial, order: int, q: int) -> Polynomial:
    if order >= len(poly):
        return ()
    return poly_trim(
        [math.comb(index + order, order) * poly[index + order]
         for index in range(len(poly) - order)],
        q,
    )


def poly_evaluate(poly: Polynomial, point: int, q: int) -> int:
    result = 0
    for coefficient in reversed(poly):
        result = (result * point + coefficient) % q
    return result


def weak_compositions(total: int, length: int) -> Iterator[tuple[int, ...]]:
    if length == 0:
        if total == 0:
            yield ()
        return
    if length == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for tail in weak_compositions(total - first, length - 1):
            yield (first,) + tail


def global_monomials(p: ExperimentParameters) -> list[GlobalExponent]:
    """Enumerate exactly the eligible monomials of ``interpolationSpace``."""
    result: list[GlobalExponent] = []
    max_jet_degree = min(p.B, (p.m * p.A - 1) // max(p.K - 1, 1))
    if p.K == 1:
        max_jet_degree = p.B
    for jet_degree in range(max_jet_degree + 1):
        for jets in weak_compositions(jet_degree, p.d + 1):
            if p.d >= 1 and jets[1] > p.m:
                continue
            higher_degree = sum(jets[2:])
            higher_weight = sum((order - 1) * jets[order] for order in range(2, p.d + 1))
            if higher_degree > p.C or higher_weight > p.W:
                continue
            weighted_jet_degree = (p.K - 1) * jet_degree
            if weighted_jet_degree >= p.m * p.A:
                continue
            for x_exponent in range(p.m * p.A - weighted_jet_degree):
                result.append((x_exponent,) + jets)
    return result


def local_mul(
    left: dict[LocalExponent, int],
    right: dict[LocalExponent, int],
    q: int,
    m: int,
) -> dict[LocalExponent, int]:
    result: defaultdict[LocalExponent, int] = defaultdict(int)
    for left_exponent, left_coefficient in left.items():
        for right_exponent, right_coefficient in right.items():
            exponent = tuple(a + b for a, b in zip(left_exponent, right_exponent))
            # Every later constraint discards T degree at least m, and all
            # substitutions have nonnegative T degree.
            if exponent[0] >= m:
                continue
            result[exponent] = (
                result[exponent] + left_coefficient * right_coefficient
            ) % q
    return {exponent: value for exponent, value in result.items() if value}


def local_pow(
    poly: dict[LocalExponent, int], exponent: int, q: int, m: int
) -> dict[LocalExponent, int]:
    zero = (0,) * len(next(iter(poly)))
    result = {zero: 1}
    base = poly
    while exponent:
        if exponent & 1:
            result = local_mul(result, base, q, m)
        base = local_mul(base, base, q, m)
        exponent //= 2
    return result


def expand_global_monomial(
    exponent: GlobalExponent, alpha: int, y: int, p: ExperimentParameters
) -> dict[LocalExponent, int]:
    """Apply ``contactTranslate`` and retain contact order below ``m``."""
    width = p.d + 2
    zero: LocalExponent = (0,) * width

    x_local: dict[LocalExponent, int] = {zero: alpha % p.q}
    t = list(zero)
    t[0] = 1
    x_local[tuple(t)] = 1

    y0_local: dict[LocalExponent, int] = {zero: y % p.q}
    te = list(zero)
    te[0] = 1
    te[1] = 1
    y0_local[tuple(te)] = 1
    for order in range(1, p.d + 1):
        term = list(zero)
        term[0] = order
        term[1 + order] = 1
        y0_local[tuple(term)] = 1 if (order + 1) % 2 == 0 else -1 % p.q

    result = local_pow(x_local, exponent[0], p.q, p.m)
    result = local_mul(result, local_pow(y0_local, exponent[1], p.q, p.m), p.q, p.m)
    for order in range(1, p.d + 1):
        if exponent[1 + order] == 0:
            continue
        visible = list(zero)
        visible[1 + order] = exponent[1 + order]
        result = local_mul(result, {tuple(visible): 1}, p.q, p.m)

    return {
        local_exponent: coefficient
        for local_exponent, coefficient in result.items()
        if local_exponent[0] + p.d * local_exponent[1] < p.m
    }


def interpolation_matrix(
    p: ExperimentParameters, monomials: Sequence[GlobalExponent]
) -> tuple[list[list[int]], list[tuple[int, LocalExponent]]]:
    expansions: list[list[dict[LocalExponent, int]]] = []
    row_keys: set[tuple[int, LocalExponent]] = set()
    for point, (alpha, received) in enumerate(zip(p.alphas, p.received)):
        at_point = [
            expand_global_monomial(monomial, alpha, received, p)
            for monomial in monomials
        ]
        expansions.append(at_point)
        for expansion in at_point:
            row_keys.update((point, exponent) for exponent in expansion)

    ordered_rows = sorted(row_keys)
    row_number = {key: index for index, key in enumerate(ordered_rows)}
    matrix = [[0] * len(monomials) for _ in ordered_rows]
    for point, at_point in enumerate(expansions):
        for column, expansion in enumerate(at_point):
            for exponent, coefficient in expansion.items():
                matrix[row_number[(point, exponent)]][column] = coefficient
    return matrix, ordered_rows


def rref_and_nullspace(matrix: Sequence[Sequence[int]], q: int) -> tuple[int, list[list[int]]]:
    if not matrix:
        return 0, []
    work = [[value % q for value in row] for row in matrix]
    rows = len(work)
    columns = len(work[0])
    pivot_columns: list[int] = []
    pivot_row = 0
    for column in range(columns):
        selected = next((row for row in range(pivot_row, rows) if work[row][column]), None)
        if selected is None:
            continue
        work[pivot_row], work[selected] = work[selected], work[pivot_row]
        inverse = pow(work[pivot_row][column], q - 2, q)
        work[pivot_row] = [(inverse * value) % q for value in work[pivot_row]]
        for row in range(rows):
            if row == pivot_row or work[row][column] == 0:
                continue
            factor = work[row][column]
            work[row] = [
                (value - factor * pivot_value) % q
                for value, pivot_value in zip(work[row], work[pivot_row])
            ]
        pivot_columns.append(column)
        pivot_row += 1
        if pivot_row == rows:
            break

    free_columns = [column for column in range(columns) if column not in set(pivot_columns)]
    basis: list[list[int]] = []
    for free in free_columns:
        vector = [0] * columns
        vector[free] = 1
        for row, pivot in enumerate(pivot_columns):
            vector[pivot] = -work[row][free] % q
        basis.append(vector)
    return len(pivot_columns), basis


def specialize_monomial(
    exponent: GlobalExponent, message: Polynomial, q: int
) -> Polynomial:
    result = poly_pow((0, 1), exponent[0], q)
    for order, power in enumerate(exponent[1:]):
        if power:
            result = poly_mul(
                result,
                poly_pow(hasse_derivative(message, order, q), power, q),
                q,
            )
    return result


def specialize_interpolant(
    coefficients: Sequence[int],
    specialized_monomials: Sequence[Polynomial],
    q: int,
) -> Polynomial:
    result: Polynomial = ()
    for coefficient, monomial in zip(coefficients, specialized_monomials):
        if coefficient:
            result = poly_add(result, poly_scale(monomial, coefficient, q), q)
    return result


def run_experiment(
    p: ExperimentParameters, *, enumerate_limit: int = 2_000_000
) -> dict[str, object]:
    p.validate()
    monomials = global_monomials(p)
    matrix, row_keys = interpolation_matrix(p, monomials)
    rank, kernel_basis = rref_and_nullspace(matrix, p.q)
    result: dict[str, object] = {
        "parameters": asdict(p),
        "global_monomials": len(monomials),
        "constraint_rows": len(row_keys),
        "constraint_rank": rank,
        "kernel_dimension": len(kernel_basis),
    }
    message_count = p.q ** p.K
    if message_count > enumerate_limit:
        result["root_enumeration"] = {
            "status": "skipped",
            "message_count": message_count,
            "enumerate_limit": enumerate_limit,
        }
        return result
    if not kernel_basis:
        result["root_enumeration"] = {
            "status": "empty-kernel",
            "message_count": message_count,
        }
        return result

    basis_root_counts = [0] * len(kernel_basis)
    common_root_count = 0
    agreement_candidates = 0
    common_roots_by_agreement = [0] * (p.n + 1)
    for coefficients in itertools.product(range(p.q), repeat=p.K):
        message = poly_trim(coefficients, p.q)
        specialized = [specialize_monomial(monomial, message, p.q) for monomial in monomials]
        basis_zeros = [
            not specialize_interpolant(vector, specialized, p.q)
            for vector in kernel_basis
        ]
        for index, is_zero in enumerate(basis_zeros):
            basis_root_counts[index] += is_zero
        common_zero = all(basis_zeros)
        agreement = sum(
            poly_evaluate(message, alpha, p.q) == received % p.q
            for alpha, received in zip(p.alphas, p.received)
        )
        if agreement >= p.A:
            agreement_candidates += 1
        if common_zero:
            common_root_count += 1
            common_roots_by_agreement[agreement] += 1

    result["root_enumeration"] = {
        "status": "complete",
        "message_count": message_count,
        "one_interpolant_roots": basis_root_counts[0],
        "basis_interpolant_root_counts": basis_root_counts,
        "minimum_basis_interpolant_roots": min(basis_root_counts),
        "maximum_basis_interpolant_roots": max(basis_root_counts),
        "full_kernel_common_roots": common_root_count,
        "agreement_candidates": agreement_candidates,
        "common_roots_by_agreement": common_roots_by_agreement,
        "one_free_coefficients_log_q": (
            math.log(basis_root_counts[0], p.q) if basis_root_counts[0] else None
        ),
        "common_free_coefficients_log_q": math.log(common_root_count, p.q) if common_root_count else None,
    }
    return result


def parse_csv(text: str) -> tuple[int, ...]:
    return tuple(int(value) for value in text.split(",") if value != "")


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    for name in ("q", "d", "m", "W", "C", "n", "A", "K", "B"):
        result.add_argument(f"--{name}", type=int, required=True)
    result.add_argument("--alphas", type=parse_csv, required=True)
    result.add_argument("--received", type=parse_csv, required=True)
    result.add_argument("--enumerate-limit", type=int, default=2_000_000)
    return result


def main(argv: Iterable[str] | None = None) -> int:
    args = parser().parse_args(argv)
    parameters = ExperimentParameters(
        q=args.q,
        d=args.d,
        m=args.m,
        W=args.W,
        C=args.C,
        n=args.n,
        A=args.A,
        K=args.K,
        B=args.B,
        alphas=args.alphas,
        received=args.received,
    )
    print(json.dumps(run_experiment(parameters, enumerate_limit=args.enumerate_limit), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
