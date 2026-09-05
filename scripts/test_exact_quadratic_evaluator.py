#!/usr/bin/env python3

import itertools
import math
import unittest

from exact_quadratic_evaluator import (
    Parameters,
    adaptive_weighted_partition_count,
    adaptive_slack,
    degree_weight_histogram,
    evaluate,
    gaussian_rectangle_coefficients,
    good_higher_exponent_count,
    local_count,
    partition_cumulative,
)


def tuples_with_entries(length: int, maximum: int):
    return itertools.product(range(maximum + 1), repeat=length)


class ExactQuadraticEvaluatorTests(unittest.TestCase):
    def test_partition_cumulative_against_enumeration(self):
        for d in range(1, 6):
            for W in range(9):
                expected = sum(
                    1
                    for c in tuples_with_entries(d - 1, W)
                    if sum((i + 1) * value for i, value in enumerate(c)) <= W
                )
                self.assertEqual(partition_cumulative(d - 1, W)[W], expected)

    def test_gaussian_rectangle_against_enumeration(self):
        for d in range(1, 6):
            for W in range(8):
                for C in range(6):
                    expected = sum(
                        1
                        for c in tuples_with_entries(d - 1, W)
                        if sum(c) <= C
                        and sum((i + 1) * value for i, value in enumerate(c)) <= W
                    )
                    self.assertEqual(good_higher_exponent_count(d, W, C), expected)
                    coefficients = gaussian_rectangle_coefficients(C, d - 1, W)
                    self.assertEqual(sum(coefficients), expected)

    def test_degree_histogram_against_enumeration(self):
        for d in range(1, 6):
            for W in range(7):
                for C in range(5):
                    expected = [0] * (C + 1)
                    for c in tuples_with_entries(d - 1, W):
                        degree = sum(c)
                        weight = sum((i + 1) * value for i, value in enumerate(c))
                        if degree <= C and weight <= W:
                            expected[degree] += 1
                    self.assertEqual(degree_weight_histogram(d, W, C), expected)

    def test_aggregated_local_count_against_definition(self):
        p = Parameters(d=3, m=8, W=5, C=4, n=7, A=4, K=3, B=9)
        counts = partition_cumulative(p.d - 1, p.W + p.m - 1)
        expected = 0
        for t in range(p.m):
            for b in range(p.m // p.d + 1):
                if t + p.d * b < p.m:
                    expected += (p.m + t + 1) * counts[p.W + t + p.d * b]
        self.assertEqual(local_count(p), expected)

    def test_constant_slack_fast_path_matches_adaptive_histogram(self):
        p = Parameters(d=5, m=12, W=14, C=4, n=2, A=12, K=4, B=50)
        result = evaluate(p)
        histogram = degree_weight_histogram(p.d, p.W, p.C)
        expected = (p.K - 1) * sum(
            count * math.comb(adaptive_slack(p.m, p.A, p.K, p.B, degree) + 2, 3)
            for degree, count in enumerate(histogram)
        )
        self.assertEqual(result["global_method"], "gaussian-constant-slack")
        self.assertEqual(result["global_count"], expected)

    def test_general_adaptive_path(self):
        p = Parameters(d=4, m=9, W=9, C=7, n=3, A=4, K=5, B=10)
        result = evaluate(p)
        histogram = degree_weight_histogram(p.d, p.W, p.C)
        expected = (p.K - 1) * sum(
            count * math.comb(adaptive_slack(p.m, p.A, p.K, p.B, degree) + 2, 3)
            for degree, count in enumerate(histogram)
        )
        self.assertEqual(result["global_method"], "gaussian-adaptive-prefix")
        self.assertEqual(result["global_count"], expected)

    def test_one_variable_adaptive_count_against_histogram(self):
        for d in range(1, 7):
            for W in range(8):
                for C in range(7):
                    for m in range(1, 6):
                        for cap in range(8):
                            histogram = degree_weight_histogram(d, W, C)
                            expected = sum(
                                count
                                * math.comb(min(m, max(cap - degree, 0)) + 2, 3)
                                for degree, count in enumerate(histogram)
                                if degree <= cap
                            )
                            self.assertEqual(
                                adaptive_weighted_partition_count(
                                    d, W, C, m, cap, max_updates=None
                                ),
                                expected,
                            )

    def test_one_variable_resource_guard(self):
        with self.assertRaisesRegex(ValueError, "update budget"):
            adaptive_weighted_partition_count(
                5, 20, 10, 8, 9, max_updates=100
            )


if __name__ == "__main__":
    unittest.main()
