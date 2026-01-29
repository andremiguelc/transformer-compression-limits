# Lean Formalization

Formalized proofs of rate-distortion theory bounds in Lean 4.

## Contents

- `RateDistortion/` - Rate-distortion bounds for GGD sources
  - `Basic.lean` - Core definitions (log2, entropy, SLB, log-concavity)
  - `Axioms.lean` - Centralized axioms (de Bruijn, test channel, Fisher info, GGD integrals)
  - `RateDistortion.lean` - R(D) definition and RD gap
  - `GaussianSmoothing.lean` - de Bruijn framework: `rdGap_via_deBruijn` and `rdGap_bound_via_fisherBound` (proved)
  - `GGD/` - GGD-specific material, split by topic
    - `Basic.lean` - Density and scale definitions
    - `Moments.lean` - Normalization (`ggd_integral_eq_one`), moments (`ggd_abs_moment_integral`, `ggd_second_moment`) — all proved
    - `Entropy.lean` - GGD entropy formulas (sorry)
    - `FisherInfo.lean` - Score and Fisher information (sorry)
    - `LogConcave.lean` - Log-concavity proof (partially proved)
  - `GGDRDBound.lean` - Main RD gap bound `ggd_rd_gap_bound_fisher` (proved), log-form and bits conversion (sorry)
  - `ECSQ.lean` - Optional ECSQ scaffolding
  - `Entropy.lean` - Deprecated shim
  - `Quantization.lean` - Deprecated shim

## Status

The main theorem `ggd_rd_gap_bound_fisher` (Goal B in nats) is fully proved, reducing to axioms in `Axioms.lean`. See `GOALS.md` in the project root for detailed progress.

## Building

```bash
lake build
```
