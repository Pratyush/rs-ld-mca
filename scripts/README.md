# Exact finite certificate evaluator

`exact_quadratic_evaluator.py` evaluates the strict inequality in
`quadratic_adaptive_listDecodable_of_exact_sum` using Python integers only.
The inputs `W` and `C` must already be the integer values of
`quadraticShellWeight` and `quadraticShellDegree`; the evaluator deliberately
does not approximate the real logarithm or silently round a rate.

Example:

```bash
python3 scripts/exact_quadratic_evaluator.py \
  --d 10 --m 3200 --W 19378 --C 6400 \
  --n 1000 --A 300 --K 100 --B 9697
```

Exit status is zero exactly when the strict certificate holds, one when it
does not hold, and two for an invalid or infeasible request.  The JSON output
contains the two exact counts, their signed gap, and the computation method.

The fast `gaussian-constant-slack` method applies when

```text
C <= min(B, floor(m*A/(K-1))) - m.
```

It uses

```text
#goodHigherExponents = sum_[w=0..W] [x^w] [C+d-1 choose d-1]_x
```

and is one-dimensional in `W`.  Otherwise the exact adaptive slack depends
on the ordinary degree.  The program now walks through the Gaussian
rectangles

```text
[h+d-1 choose d-1]_x
  = [h+d-2 choose d-1]_x * (1-x^(h+d-1))/(1-x^h).
```

The difference of consecutive rectangle counts is the number of good
exponents of ordinary degree exactly `h`.  Weighting these differences by
`choose(min(m,cap-h)+2,3)` evaluates the fully adaptive sum with `O(W)`
memory and `O(W*min(C,cap))` exact integer updates.  `--max-cells` remains
the compatibility spelling for the maximum allowed number of coefficient
updates; memory use is only `O(W)`.

Run the independent brute-force cross-checks with

```bash
cd scripts
python3 -m unittest -v test_exact_quadratic_evaluator.py
```

The evaluator checks the combinatorial inequality only.  The other theorem
hypotheses—primality, distinct evaluation points, field-size conditions, and
the identities defining rounded `W` and `C`—remain separate proof
obligations.

## Certified integer-parameter search

`scan_quadratic_parameters.py` searches exact tuples for the theorem
`explicit_adaptive_listDecodable_of_exact_sum`.  Its trusted target uses the
reported integers `m,W,C,A,K,B` directly.  The real logarithm is used only as
a heuristic for proposing `W`; it is not part of the certificate.

For example:

```bash
python3 scripts/scan_quadratic_parameters.py \
  --rate 1/10 --agreement 3/10 --d 4:32:2 --c 8,16,32
```

Each JSON record includes every arithmetic theorem hypothesis, a prime field
size, both exact dimension counts, and the signed strict-inequality gap.
