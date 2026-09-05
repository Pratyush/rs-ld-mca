#!/usr/bin/env python3
"""Exact finite evaluator for the quadratic-multiplicity certificate.

The program evaluates the two natural-number expressions in
`quadratic_adaptive_listDecodable_of_exact_sum` without floating-point
arithmetic.  All inputs are already-rounded integers.

For constant adaptive slack, the good higher-jet count is computed as the
sum of the first W coefficients of the Gaussian binomial

    [C + d - 1 choose d - 1]_x.

This is the generating function for partitions of weight at most W, with at
most C parts, each at most d-1.  The general adaptive case walks through the
same Gaussian rectangles one degree at a time.  Consecutive rectangle counts
give the exact-degree histogram, so the algorithm uses O(W) memory rather
than a (C+1) by (W+1) bivariate table.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
import time
from dataclasses import asdict, dataclass
from typing import Iterable


@dataclass(frozen=True)
class Parameters:
    d: int
    m: int
    W: int
    C: int
    n: int
    A: int
    K: int
    B: int

    def validate(self) -> None:
        for name, value in asdict(self).items():
            if value < 0:
                raise ValueError(f"{name} must be nonnegative")
        if self.d == 0:
            raise ValueError("d must be positive")
        if self.K <= 1:
            raise ValueError("K must be at least 2")


def _check_size(name: str, value: int, maximum: int | None) -> None:
    if maximum is not None and value > maximum:
        raise ValueError(
            f"{name} requires {value:,} states, exceeding the configured "
            f"limit {maximum:,}"
        )


def partition_coefficients(max_part: int, max_weight: int) -> list[int]:
    """Coefficients of product_(i=1..max_part) (1-x^i)^(-1)."""
    if max_part < 0 or max_weight < 0:
        raise ValueError("partition bounds must be nonnegative")
    coefficients = [0] * (max_weight + 1)
    coefficients[0] = 1
    for part in range(1, max_part + 1):
        for weight in range(part, max_weight + 1):
            coefficients[weight] += coefficients[weight - part]
    return coefficients


def partition_cumulative(max_part: int, max_weight: int) -> list[int]:
    """Counts partitions of weight at most each index."""
    coefficients = partition_coefficients(max_part, max_weight)
    running = 0
    for weight, coefficient in enumerate(coefficients):
        running += coefficient
        coefficients[weight] = running
    return coefficients


def gaussian_rectangle_coefficients(
    max_parts: int, max_part: int, max_weight: int
) -> list[int]:
    """Truncated coefficients of [max_parts+max_part choose max_part]_x.

    The product formula is applied one factor at a time.  Division by
    `(1-x^i)` is the ascending unbounded-knapsack recurrence; multiplication
    by `(1-x^(max_parts+i))` is a descending subtraction.
    """
    if min(max_parts, max_part, max_weight) < 0:
        raise ValueError("Gaussian-binomial bounds must be nonnegative")
    coefficients = [0] * (max_weight + 1)
    coefficients[0] = 1
    for i in range(1, max_part + 1):
        # A partition in a `max_parts` by `i` rectangle has degree at most
        # `max_parts*i`; avoiding the known-zero tail matters when W is large.
        current_limit = min(max_weight, max_parts * i)
        for weight in range(i, current_limit + 1):
            coefficients[weight] += coefficients[weight - i]
        shift = max_parts + i
        for weight in range(current_limit, shift - 1, -1):
            coefficients[weight] -= coefficients[weight - shift]
    if any(value < 0 for value in coefficients):
        raise ArithmeticError("negative Gaussian-binomial coefficient")
    return coefficients


def good_higher_exponent_count(d: int, W: int, C: int) -> int:
    """Exact cardinality of `goodHigherExponents d W C`."""
    return sum(gaussian_rectangle_coefficients(C, d - 1, W))


def degree_weight_histogram(
    d: int, W: int, C: int, *, max_cells: int | None = 20_000_000
) -> list[int]:
    """Count good exponents by ordinary degree.

    Entry h counts vectors c with sum(c_i)=h and sum(i*c_i)<=W for
    i=1,...,d-1.  This is the exact fallback when adaptive slack is not
    constant over the good shell.
    """
    cells = (C + 1) * (W + 1)
    _check_size("adaptive histogram", cells, max_cells)
    table = [[0] * (W + 1) for _ in range(C + 1)]
    table[0][0] = 1
    for part in range(1, d):
        for degree in range(1, C + 1):
            row = table[degree]
            previous = table[degree - 1]
            for weight in range(part, W + 1):
                row[weight] += previous[weight - part]
    return [sum(row) for row in table]


def adaptive_weighted_partition_count(
    d: int,
    W: int,
    C: int,
    m: int,
    cap: int,
    *,
    max_updates: int | None = None,
) -> int:
    """Weighted good-exponent count using one polynomial in ``x``.

    Let ``F_h(x) = [h+d-1 choose d-1]_x``.  Its coefficients count
    partitions with at most ``h`` positive parts, each at most ``d-1``.
    Hence ``sum_[w<=W] (F_h-F_(h-1))[x^w]`` is exactly the number of good
    higher-jet exponents of ordinary degree ``h``.  We update rectangles by

        F_h = F_(h-1) * (1-x^(h+d-1)) / (1-x^h).

    Only degrees ``h <= min(C, cap)`` can have positive adaptive slack.
    The returned value omits the outer factor ``K-1``.
    """
    if min(d, W, C, m, cap) < 0:
        raise ValueError("adaptive count bounds must be nonnegative")
    if d == 0:
        raise ValueError("d must be positive")

    coefficients = [0] * (W + 1)
    coefficients[0] = 1
    previous_total = 0
    weighted = 0
    max_degree = min(C, cap, W)
    _check_size(
        "adaptive Gaussian-prefix update budget",
        (max_degree + 1) * (W + 1),
        max_updates,
    )

    for degree in range(max_degree + 1):
        if degree > 0:
            current_limit = min(W, degree * (d - 1))
            for weight in range(degree, current_limit + 1):
                coefficients[weight] += coefficients[weight - degree]
            shift = degree + d - 1
            for weight in range(current_limit, shift - 1, -1):
                coefficients[weight] -= coefficients[weight - shift]
            if any(value < 0 for value in coefficients[: current_limit + 1]):
                raise ArithmeticError("negative Gaussian-binomial coefficient")

        rectangle_total = sum(coefficients)
        exact_degree_count = rectangle_total - previous_total
        if exact_degree_count < 0:
            raise ArithmeticError("Gaussian rectangle counts decreased")
        slack = min(m, cap - degree)
        weighted += exact_degree_count * math.comb(slack + 2, 3)
        previous_total = rectangle_total

    return weighted


def adaptive_slack(m: int, A: int, K: int, B: int, degree: int) -> int:
    weighted_cap = (m * A) // (K - 1)
    return min(m, max(B - degree, 0), max(weighted_cap - degree, 0))


def global_count(
    parameters: Parameters, *, max_cells: int | None = 20_000_000
) -> tuple[int, str, int]:
    """Evaluate `quadraticAdaptiveGlobalCount` with explicit W and C.

    Returns `(count, method, good_count)`.
    """
    p = parameters
    cap = min(p.B, (p.m * p.A) // (p.K - 1))
    if cap >= p.m and p.C <= cap - p.m:
        good = good_higher_exponent_count(p.d, p.W, p.C)
        simplex = math.comb(p.m + 2, 3)
        return (p.K - 1) * good * simplex, "gaussian-constant-slack", good

    weighted = adaptive_weighted_partition_count(
        p.d, p.W, p.C, p.m, cap, max_updates=max_cells
    )
    good = good_higher_exponent_count(p.d, p.W, p.C)
    return (p.K - 1) * weighted, "gaussian-adaptive-prefix", good


def local_count(parameters: Parameters) -> int:
    """Evaluate `coupledContactEnvelopeCount d m W` exactly.

    Contact pairs `(t,b)` are aggregated by `r=t+d*b`.  For fixed r, with
    h=floor(r/d), their total first-jet coefficient is

      (h+1)(m+r+1) - d*h(h+1)/2.
    """
    p = parameters
    cumulative = partition_cumulative(p.d - 1, p.W + p.m - 1)
    total = 0
    for contact_order in range(p.m):
        h = contact_order // p.d
        coefficient = (
            (h + 1) * (p.m + contact_order + 1)
            - p.d * h * (h + 1) // 2
        )
        total += coefficient * cumulative[p.W + contact_order]
    return total


def paper_local_rank_count(parameters: Parameters) -> int:
    """Evaluate the kernel-subtracted local-rank bound from Lemma 3.11.

    For a fixed intermediate ``T`` degree ``r``, put

        h_r = ceil((m-r)/d).

    The intermediate space has ``(r+1)(m+1) N_d(W+r)`` monomials.  The
    explicit kernel constructed in the paper removes

        max(0, (r-h_r+1)(m-h_r+1)) N_d(W+r)

    of them.  Unlike :func:`local_count`, this is a rank bound for the
    local map rather than the cardinality of an output support envelope.
    """
    p = parameters
    cumulative = partition_cumulative(p.d - 1, p.W + p.m - 1)
    total = 0
    for r in range(p.m):
        h_r = (p.m - r + p.d - 1) // p.d
        ambient = (r + 1) * (p.m + 1)
        kernel = max(0, (r - h_r + 1) * (p.m - h_r + 1))
        total += (ambient - kernel) * cumulative[p.W + r]
    return total


def sharpened_support_local_count(parameters: Parameters) -> int:
    """Count the sharper output support before the paper's kernel quotient.

    The rewrite invariants give ``E-degree <= T-degree`` and higher-jet
    weight at most ``W + T-degree``.  This bound is slightly weaker than the
    kernel-subtracted rank, but can be proved using support containment alone.
    """
    p = parameters
    cumulative = partition_cumulative(p.d - 1, p.W + p.m - 1)
    total = 0
    for t in range(p.m):
        max_e = min((p.m - 1 - t) // p.d, t)
        total += (max_e + 1) * (p.m + t + 1) * cumulative[p.W + t]
    return total


def evaluate(
    parameters: Parameters, *, max_cells: int | None = 20_000_000
) -> dict[str, int | str | bool | dict[str, int]]:
    parameters.validate()
    started = time.perf_counter()
    local = local_count(parameters)
    paper_local = paper_local_rank_count(parameters)
    sharpened_support_local = sharpened_support_local_count(parameters)
    global_value, method, good = global_count(parameters, max_cells=max_cells)
    scaled_local = parameters.n * local
    scaled_paper_local = parameters.n * paper_local
    scaled_sharpened_support_local = parameters.n * sharpened_support_local
    elapsed_ms = round((time.perf_counter() - started) * 1000)
    return {
        "parameters": asdict(parameters),
        "local_count": local,
        "n_times_local_count": scaled_local,
        "paper_local_rank_count": paper_local,
        "n_times_paper_local_rank_count": scaled_paper_local,
        "sharpened_support_local_count": sharpened_support_local,
        "n_times_sharpened_support_local_count": scaled_sharpened_support_local,
        "global_count": global_value,
        "strict_certificate": scaled_local < global_value,
        "gap": global_value - scaled_local,
        "paper_rank_strict_certificate": scaled_paper_local < global_value,
        "paper_rank_gap": global_value - scaled_paper_local,
        "sharpened_support_strict_certificate": (
            scaled_sharpened_support_local < global_value
        ),
        "sharpened_support_gap": global_value - scaled_sharpened_support_local,
        "good_higher_exponent_count": good,
        "global_method": method,
        "elapsed_ms": elapsed_ms,
    }


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("d", "m", "W", "C", "n", "A", "K", "B"):
        parser.add_argument(f"--{name}", type=int, required=True)
    parser.add_argument(
        "--max-cells",
        type=int,
        default=20_000_000,
        help="maximum coefficient updates for the one-dimensional adaptive path",
    )
    parser.add_argument(
        "--compact", action="store_true", help="emit one-line JSON"
    )
    parser.add_argument(
        "--criterion",
        choices=("coupled", "sharpened", "paper"),
        default="coupled",
        help=(
            "certificate controlling the exit status; 'sharpened' has a Lean "
            "support proof, while 'paper' is currently evaluator-only"
        ),
    )
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    parameters = Parameters(
        d=args.d,
        m=args.m,
        W=args.W,
        C=args.C,
        n=args.n,
        A=args.A,
        K=args.K,
        B=args.B,
    )
    try:
        result = evaluate(parameters, max_cells=args.max_cells)
    except (ArithmeticError, MemoryError, ValueError) as error:
        print(json.dumps({"error": str(error)}), file=sys.stderr)
        return 2
    print(json.dumps(result, indent=None if args.compact else 2, sort_keys=True))
    certificate_key = {
        "coupled": "strict_certificate",
        "sharpened": "sharpened_support_strict_certificate",
        "paper": "paper_rank_strict_certificate",
    }[args.criterion]
    return 0 if result[certificate_key] else 1


if __name__ == "__main__":
    raise SystemExit(main())
