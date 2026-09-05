#!/usr/bin/env python3

import unittest

from saddle_point_experiment import SaddleParameters, evaluate, geometric_moments


class SaddlePointExperimentTests(unittest.TestCase):
    def test_moments_against_truncated_direct_sum(self) -> None:
        d = 5
        tau = 0.7
        moments = geometric_moments(d, tau)
        direct_height = 0.0
        direct_weight = 0.0
        for part in range(1, d):
            z = __import__("math").exp(-tau * part)
            direct_height += sum(k * (1 - z) * z**k for k in range(100))
            direct_weight += part * sum(k * (1 - z) * z**k for k in range(100))
        self.assertAlmostEqual(moments["mean_height"], direct_height)
        self.assertAlmostEqual(moments["mean_weight"], direct_weight)

    def test_cap_fraction_is_probability(self) -> None:
        row = evaluate(SaddleParameters(d=6, c=2.0, a=1.5))
        self.assertGreaterEqual(row["exact_weight_cap_fraction"], 0.0)
        self.assertLessEqual(row["exact_weight_cap_fraction"], 1.0)
        self.assertGreaterEqual(row["cumulative_cap_fraction"], 0.0)
        self.assertLessEqual(row["cumulative_cap_fraction"], 1.0)


if __name__ == "__main__":
    unittest.main()
