#!/usr/bin/env python3

import unittest

from local_rank_experiment import run_local_rank_experiment


class LocalRankExperimentTests(unittest.TestCase):
    def test_paper_bound_matches_tiny_exact_ranks(self) -> None:
        for q in (5, 7):
            for d in (1, 2, 3):
                for m in (1, 2, 3, 4):
                    for W in (0, 1, 2):
                        with self.subTest(q=q, d=d, m=m, W=W):
                            row = run_local_rank_experiment(q, d, m, W)
                            self.assertTrue(row["rank_le_paper_bound"])
                            self.assertTrue(row["rank_eq_paper_bound"])


if __name__ == "__main__":
    unittest.main()
