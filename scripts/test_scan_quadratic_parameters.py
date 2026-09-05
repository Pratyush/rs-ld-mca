#!/usr/bin/env python3

import unittest
from fractions import Fraction

from scan_quadratic_parameters import (
    ceil_fraction,
    floor_fraction,
    is_prime_64,
    make_record,
    next_prime,
    proposed_weight,
)


class QuadraticParameterScannerTests(unittest.TestCase):
    def test_fraction_rounding(self):
        self.assertEqual(floor_fraction(Fraction(17, 5)), 3)
        self.assertEqual(ceil_fraction(Fraction(17, 5)), 4)

    def test_primes(self):
        self.assertTrue(is_prime_64(2))
        self.assertTrue(is_prime_64(1_000_003))
        self.assertFalse(is_prime_64(1_000_005))
        self.assertEqual(next_prime(100), 101)

    def test_proposed_weight_is_reproducible(self):
        self.assertEqual(proposed_weight(Fraction(1), 10, 3200), 9689)

    def test_record_checks_every_explicit_hypothesis(self):
        record = make_record(
            rate=Fraction(1, 10),
            agreement=Fraction(3, 10),
            a=Fraction(2),
            c=4,
            d=4,
            n=1000,
            extension_degree=2,
            max_updates=2_000_000,
        )
        self.assertTrue(all(record.hypotheses.values()))
        self.assertEqual(record.result["parameters"]["m"], 64)


if __name__ == "__main__":
    unittest.main()
