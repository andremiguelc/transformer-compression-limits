# Lean Formalization

Formalized proofs of rate-distortion theory bounds in Lean 4.

## Contents

- `RateDistortion/` - Rate-distortion bounds for Gaussian sources
  - `Basic.lean` - Scalar Gaussian R(D) bound
  - `WaterFilling.lean` - Vector case with water-filling (planned)

## Building

```bash
lake build
```

This directory formalizes the theoretical baseline (Shannon R(D) bounds) that empirical compression methods are compared against in the notebooks.
