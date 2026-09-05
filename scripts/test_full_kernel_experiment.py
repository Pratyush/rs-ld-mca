#!/usr/bin/env python3

import unittest

from full_kernel_experiment import (
    ExperimentParameters,
    expand_global_monomial,
    hasse_derivative,
    rref_and_nullspace,
)


class FullKernelExperimentTests(unittest.TestCase):
    def test_nullspace(self) -> None:
        rank, basis = rref_and_nullspace([[1, 2, 3], [2, 4, 1]], 5)
        self.assertEqual(rank, 1)
        self.assertEqual(len(basis), 2)
        for vector in basis:
            self.assertTrue(all(sum(a * b for a, b in zip(row, vector)) % 5 == 0
                                for row in [[1, 2, 3], [2, 4, 1]]))

    def test_hasse_derivative(self) -> None:
        # D^(2)(1 + 2X + 3X^2 + 4X^3) = 3 + 12X over F_7.
        self.assertEqual(hasse_derivative((1, 2, 3, 4), 2, 7), (3, 5))

    def test_y0_contact_expansion(self) -> None:
        p = ExperimentParameters(
            q=7, d=2, m=5, W=3, C=3, n=1, A=1, K=2, B=3,
            alphas=(0,), received=(3,),
        )
        # Global exponent (0,1,0,0) is Y_0.  Under contactTranslate it is
        # y + T E + T Y_1 - T^2 Y_2.
        expansion = expand_global_monomial((0, 1, 0, 0), 0, 3, p)
        self.assertEqual(
            expansion,
            {
                (0, 0, 0, 0): 3,
                (1, 1, 0, 0): 1,
                (1, 0, 1, 0): 1,
                (2, 0, 0, 1): 6,
            },
        )


if __name__ == "__main__":
    unittest.main()
