#!/usr/bin/env python3

import unittest

from full_kernel_sweep import sweep


class FullKernelSweepTests(unittest.TestCase):
    def test_small_sweep(self) -> None:
        row = sweep(
            q=3, d=2, m=2, W=1, C=2, n=3, A=2, K=2, B=2,
            alphas=(0, 1, 2), max_received_words=100,
        )
        self.assertEqual(row["received_words"], 27)
        self.assertTrue(row["a_basis_vector_always_realized_common_roots"])


if __name__ == "__main__":
    unittest.main()
