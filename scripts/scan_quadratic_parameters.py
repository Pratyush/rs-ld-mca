#!/usr/bin/env python3
"""Search exact finite quadratic certificates and emit reproducible tuples.

Rates, agreement fractions, and shell coefficients are parsed as exact
fractions.  A logarithm is used only to propose an integer W; every reported
certificate records that integer and is evaluated using exact arithmetic.
The resulting tuple targets `explicit_adaptive_listDecodable_of_exact_sum`,
whose trusted statement contains no logarithm or real-valued rounding.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from decimal import Decimal, localcontext
from fractions import Fraction
from typing import Iterable

from exact_quadratic_evaluator import Parameters, evaluate


def parse_fraction(text: str) -> Fraction:
    value = Fraction(text)
    if value <= 0:
        raise argparse.ArgumentTypeError("fractions must be positive")
    return value


def parse_int_list(text: str) -> list[int]:
    values = [int(item) for item in text.split(",")]
    if not values or any(value <= 0 for value in values):
        raise argparse.ArgumentTypeError("expected comma-separated positive integers")
    return values


def parse_fraction_list(text: str) -> list[Fraction]:
    values = [parse_fraction(item) for item in text.split(",")]
    if not values:
        raise argparse.ArgumentTypeError("expected comma-separated fractions")
    return values


def parse_range(text: str) -> range:
    pieces = [int(item) for item in text.split(":" )]
    if len(pieces) not in (2, 3):
        raise argparse.ArgumentTypeError("range must be START:STOP[:STEP]")
    start, stop = pieces[:2]
    step = pieces[2] if len(pieces) == 3 else 1
    if start <= 0 or stop < start or step <= 0:
        raise argparse.ArgumentTypeError("invalid positive integer range")
    return range(start, stop + 1, step)


def floor_fraction(value: Fraction) -> int:
    return value.numerator // value.denominator


def ceil_fraction(value: Fraction) -> int:
    return -((-value.numerator) // value.denominator)


def proposed_weight(a: Fraction, d: int, m: int) -> int:
    """Stable high-precision floor used only to propose an explicit W."""
    floors: list[int] = []
    for precision in (80, 140):
        with localcontext() as context:
            context.prec = precision
            numerator = (
                Decimal(a.numerator) * Decimal(d) * Decimal(m)
            )
            denominator = Decimal(a.denominator) * (Decimal(1) + Decimal(d).ln())
            floors.append(int(numerator / denominator))
    if floors[0] != floors[1]:
        raise ArithmeticError("the proposed W is too close to an integer boundary")
    return floors[0]


def is_prime_64(n: int) -> bool:
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for prime in small:
        if n % prime == 0:
            return n == prime
    shift, odd = 0, n - 1
    while odd % 2 == 0:
        shift += 1
        odd //= 2
    for base in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        if base % n == 0:
            continue
        value = pow(base, odd, n)
        if value in (1, n - 1):
            continue
        for _ in range(shift - 1):
            value = value * value % n
            if value == n - 1:
                break
        else:
            return False
    return True


def next_prime(n: int) -> int:
    candidate = max(2, n)
    if candidate == 2:
        return 2
    if candidate % 2 == 0:
        candidate += 1
    while not is_prime_64(candidate):
        candidate += 2
    return candidate


@dataclass(frozen=True)
class SearchRecord:
    rate: str
    agreement: str
    shell_coefficient: str
    extension_degree: int
    q: int
    k: int
    c: int
    criterion: str
    result: dict[str, object]
    hypotheses: dict[str, bool]

    @property
    def passes(self) -> bool:
        certificate_key = {
            "coupled": "strict_certificate",
            "sharpened": "sharpened_support_strict_certificate",
            "paper": "paper_rank_strict_certificate",
        }[self.criterion]
        return bool(self.result[certificate_key]) and all(
            self.hypotheses.values()
        )


def make_record(
    *,
    rate: Fraction,
    agreement: Fraction,
    a: Fraction,
    c: int,
    d: int,
    n: int,
    extension_degree: int,
    max_updates: int | None,
    criterion: str = "coupled",
) -> SearchRecord:
    A = ceil_fraction(agreement * n)
    K = floor_fraction(rate * n)
    if K <= 1:
        raise ValueError("rate and n must give K at least two")
    m = c * d * d
    W = proposed_weight(a, d, m)
    C = floor_fraction(a * m)
    B = (m * A) // (K - 1)
    field_floor = max(n, K, B + 1)
    if extension_degree == 1:
        field_floor = max(field_floor, m * A)
    elif extension_degree == 2:
        field_floor = max(field_floor, math.isqrt(m * A - 1) + 1)
    else:
        raise ValueError("extension degree must be one or two")
    q = next_prime(field_floor)
    parameters = Parameters(d=d, m=m, W=W, C=C, n=n, A=A, K=K, B=B)
    result = evaluate(parameters, max_cells=max_updates)
    hypotheses = {
        "d_pos": d > 0,
        "m_pos": m > 0,
        "d_lt_K": d < K,
        "k_le_K": K <= K,
        "K_le_q": K <= q,
        "B_pos": B > 0,
        "B_lt_q": B < q,
        "field_budget": m * A <= q**extension_degree,
        "degree_budget": C <= B,
        "weighted_budget": (K - 1) * C <= m * A,
        "q_prime": is_prime_64(q),
    }
    return SearchRecord(
        rate=str(rate),
        agreement=str(agreement),
        shell_coefficient=str(a),
        extension_degree=extension_degree,
        q=q,
        k=K,
        c=c,
        criterion=criterion,
        result=result,
        hypotheses=hypotheses,
    )


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rate", type=parse_fraction, required=True)
    parser.add_argument("--agreement", type=parse_fraction, required=True)
    parser.add_argument("--n", type=int, default=100_000)
    parser.add_argument("--d", type=parse_range, default=parse_range("4:40:2"))
    parser.add_argument("--c", type=parse_int_list, default=parse_int_list("4,8,16,32"))
    parser.add_argument(
        "--a",
        type=parse_fraction_list,
        default=parse_fraction_list("1/4,1/2,3/4,1,5/4,3/2,7/4,2"),
    )
    parser.add_argument("--extension-degree", type=int, choices=(1, 2), default=2)
    parser.add_argument("--max-updates", type=int, default=100_000_000)
    parser.add_argument("--top", type=int, default=10)
    parser.add_argument("--passing-only", action="store_true")
    parser.add_argument("--compact", action="store_true")
    parser.add_argument(
        "--criterion",
        choices=("coupled", "sharpened", "paper"),
        default="coupled",
    )
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    if args.n <= 0 or args.top <= 0 or args.max_updates <= 0:
        raise SystemExit("n, top, and max-updates must be positive")
    records: list[SearchRecord] = []
    skipped: list[dict[str, object]] = []
    for d in args.d:
        for c in args.c:
            for a in args.a:
                try:
                    record = make_record(
                        rate=args.rate,
                        agreement=args.agreement,
                        a=a,
                        c=c,
                        d=d,
                        n=args.n,
                        extension_degree=args.extension_degree,
                        max_updates=args.max_updates,
                        criterion=args.criterion,
                    )
                except (ArithmeticError, MemoryError, ValueError) as error:
                    skipped.append({"d": d, "c": c, "a": str(a), "error": str(error)})
                    continue
                if not args.passing_only or record.passes:
                    records.append(record)

    def score(record: SearchRecord) -> tuple[int, Fraction]:
        result = record.result
        local_key = {
            "coupled": "n_times_local_count",
            "sharpened": "n_times_sharpened_support_local_count",
            "paper": "n_times_paper_local_rank_count",
        }[record.criterion]
        local = int(result[local_key])
        global_value = int(result["global_count"])
        return (1 if record.passes else 0, Fraction(global_value, max(1, local)))

    records.sort(key=score, reverse=True)
    output = {
        "search": {
            "rate": str(args.rate),
            "agreement": str(args.agreement),
            "n": args.n,
            "extension_degree": args.extension_degree,
        },
        "records": [
            {**asdict(record), "passes": record.passes}
            for record in records[: args.top]
        ],
        "skipped": skipped,
    }
    print(json.dumps(output, indent=None if args.compact else 2, sort_keys=True))
    return 0 if any(record.passes for record in records) else 1


if __name__ == "__main__":
    raise SystemExit(main())
