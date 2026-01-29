# Lean Formalization

Formalized proofs of rate-distortion theory bounds in Lean 4.

## Contents

- `RateDistortion/` - Rate-distortion bounds for Gaussian sources
  - `Basic.lean` - Core definitions (log2, entropy, SLB, log-concavity)
  - `Axioms.lean` - Centralized axioms with references
  - `RateDistortion.lean` - R(D) definition and RD gap
  - `GaussianSmoothing.lean` - de Bruijn framework theorems
  - `GGD/` - GGD-specific material, split by topic
    - `Basic.lean` - Density and scale definitions
    - `Moments.lean` - Normalization and moment formulas (stubs)
    - `Entropy.lean` - GGD entropy formulas (stubs)
    - `FisherInfo.lean` - Score and Fisher information (stubs)
    - `LogConcave.lean` - Log-concavity proof (stub)
  - `GGDRDBound.lean` - Main RD gap bound (stubs)
  - `ECSQ.lean` - Optional ECSQ scaffolding
  - `Entropy.lean` - Deprecated shim (re-exports `Basic`)
  - `Quantization.lean` - Deprecated shim (re-exports `RateDistortion` and `ECSQ`)

## Building

```bash
lake build
```

This directory formalizes the theoretical baseline (Shannon R(D) bounds) that empirical compression methods are compared against in the notebooks.
