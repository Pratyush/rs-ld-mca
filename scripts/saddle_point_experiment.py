#!/usr/bin/env python3
"""Exact finite diagnostics for the Gaussian-rectangle saddle point.

For the quadratic schedule ``m=c*d^2``, ``C=a*m`` and
``W=floor(a*d*m/(1+log d))``, this compares partitions with parts at most
``d-1`` against the subset having at most ``C`` parts.  It also computes the
canonical independent-geometric saddle and the normal prediction for the
conditional height cutoff.

The coefficient arrays contain arbitrary-precision integers.  Moderate
values such as ``d <= 24`` are the intended validation range.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from typing import Iterable

from exact_quadratic_evaluator import (
    gaussian_rectangle_coefficients,
    partition_coefficients,
)


@dataclass(frozen=True)
class SaddleParameters:
    d: int
    c: float
    a: float

    @property
    def m(self) -> int:
        return math.floor(self.c * self.d * self.d)

    @property
    def C(self) -> int:
        return math.floor(self.a * self.m)

    @property
    def W(self) -> int:
        return math.floor(self.a * self.d * self.m / (1.0 + math.log(self.d)))


def geometric_moments(d: int, tau: float) -> dict[str, float]:
    mean_weight = 0.0
    mean_height = 0.0
    var_weight = 0.0
    var_height = 0.0
    covariance = 0.0
    for part in range(1, d):
        z = math.exp(-tau * part)
        mean = z / (1.0 - z)
        variance = z / ((1.0 - z) ** 2)
        mean_height += mean
        mean_weight += part * mean
        var_height += variance
        covariance += part * variance
        var_weight += part * part * variance
    return {
        "mean_weight": mean_weight,
        "mean_height": mean_height,
        "var_weight": var_weight,
        "var_height": var_height,
        "covariance": covariance,
    }


def solve_tau(d: int, target_weight: int) -> float:
    low = 1e-16
    high = 1.0
    while geometric_moments(d, high)["mean_weight"] > target_weight:
        high *= 2.0
    for _ in range(100):
        middle = (low + high) / 2.0
        if geometric_moments(d, middle)["mean_weight"] > target_weight:
            low = middle
        else:
            high = middle
    return (low + high) / 2.0


def evaluate(parameters: SaddleParameters) -> dict[str, object]:
    d, m, C, W = parameters.d, parameters.m, parameters.C, parameters.W
    if d < 2 or m < 1 or C < 0 or W < 0:
        raise ValueError("parameters must give d >= 2 and nonnegative budgets")

    unbounded = partition_coefficients(d - 1, W + m)
    bounded = gaussian_rectangle_coefficients(C, d - 1, W)
    unbounded_exact = unbounded[W]
    bounded_exact = bounded[W]
    unbounded_cumulative = sum(unbounded[: W + 1])
    bounded_cumulative = sum(bounded)

    tau = solve_tau(d, W)
    moments = geometric_moments(d, tau)
    conditional_variance = (
        moments["var_height"]
        - moments["covariance"] ** 2 / moments["var_weight"]
    )
    conditional_z = (C + 0.5 - moments["mean_height"]) / math.sqrt(
        conditional_variance
    )
    normal_prediction = 0.5 * (1.0 + math.erf(conditional_z / math.sqrt(2.0)))

    shell_ratio = sum(unbounded[: W + m + 1]) / bounded_cumulative
    return {
        "parameters": asdict(parameters),
        "rounded": {"m": m, "C": C, "W": W},
        "tau": tau,
        "tau_first_order": (1.0 + math.log(d)) / (parameters.a * m),
        "moments": moments,
        "correlation": moments["covariance"] / math.sqrt(
            moments["var_weight"] * moments["var_height"]
        ),
        "conditional_z": conditional_z,
        "normal_cap_prediction": normal_prediction,
        "exact_weight_cap_fraction": bounded_exact / unbounded_exact,
        "cumulative_cap_fraction": bounded_cumulative / unbounded_cumulative,
        "shell_ratio": shell_ratio,
        "shell_ratio_over_d_pow_one_over_a": shell_ratio / d ** (1.0 / parameters.a),
        "log_counts": {
            "unbounded_exact": math.log(unbounded_exact),
            "bounded_exact": math.log(bounded_exact),
            "unbounded_cumulative": math.log(unbounded_cumulative),
            "bounded_cumulative": math.log(bounded_cumulative),
        },
    }


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--d", type=int, nargs="+", required=True)
    result.add_argument("--c", type=float, required=True)
    result.add_argument("--a", type=float, required=True)
    return result


def main(argv: Iterable[str] | None = None) -> int:
    args = parser().parse_args(argv)
    rows = [evaluate(SaddleParameters(d=d, c=args.c, a=args.a)) for d in args.d]
    print(json.dumps(rows, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
