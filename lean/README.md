# Lean Formalization

Formalized proofs of rate-distortion theory bounds in Lean 4.

## Contents

- `RateDistortion/` - Rate-distortion bounds for GGD sources
  - `Basic.lean` - Core definitions (log2, entropy, SLB in bits/nats, log-concavity)
  - `Axioms.lean` - Centralized axioms (de Bruijn, test channel, Fisher info, GGD integrals)
  - `RateDistortion.lean` - R(D) in nats/bits and RD gap
  - `GaussianSmoothing.lean` - de Bruijn framework: `rdGap_via_deBruijn` and `rdGap_bound_via_fisherBound` (proved)
  - `GGD/` - GGD-specific material, split by topic
    - `Basic.lean` - Density and scale definitions
    - `Moments.lean` - Normalization, moments, base integrals — all proved (including `integral_exp_abs_beta`, `integral_power_exp_abs_beta`)
    - `Entropy.lean` - GGD entropy in nats and bits — proved
    - `FisherInfo.lean` - Score and Fisher information (sorry — closed forms pending)
    - `LogConcave.lean` - Log-concavity for β ≥ 1 — proved
  - `GGDRDBound.lean` - Main RD gap bound `ggd_rd_gap_bound_fisher` (proved), log-form and bits conversion (sorry)
  - `ECSQ.lean` - Optional ECSQ scaffolding
  - `Entropy.lean` - Deprecated shim
  - `Quantization.lean` - Deprecated shim

## Status

The main theorem `ggd_rd_gap_bound_fisher` (Goal B in nats) is fully proved, reducing to axioms in `Axioms.lean`. Additionally, GGD log-concavity, entropy (nats/bits), and all integration lemmas (moments, normalization, base integrals) are fully proved. See `GOALS.md` in the project root for detailed progress.

## Building

```bash
lake build
```
