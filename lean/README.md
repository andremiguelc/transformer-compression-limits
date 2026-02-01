# Lean Formalization

Formalized proofs of rate-distortion theory bounds in Lean 4.

## Contents

- `RateDistortion/` - Rate-distortion bounds for GGD sources
  - `Basic.lean` - Core definitions (log2, entropy, SLB in bits/nats, log-concavity)
  - `Axioms/` - Standard information-theoretic results taken as axioms
  - `RateDistortion.lean` - R(D) in nats/bits and RD gap
  - `GaussianSmoothing.lean` - de Bruijn framework: `rdGap_via_deBruijn` and `rdGap_bound_via_fisherBound` (proved)
  - `GGD/` - GGD-specific material, split by topic
    - `Basic.lean` - Density and scale definitions
    - `Moments.lean` - Normalization, moments, base integrals (proved)
    - `Entropy.lean` - GGD entropy in nats and bits (proved)
    - `FisherInfo.lean` - Score and Fisher information (proved)
    - `FisherInfoBounds.lean` - Numerical Fisher info bounds (partial)
    - `LogConcave.lean` - Log-concavity for β ≥ 1 (proved)
  - `GGDRDBound.lean` - Main RD gap bound `ggd_rd_gap_bound_fisher` (proved), bits conversion (proved), log-form (open)
  - `ECSQ.lean` - ECSQ scaffolding

## Building

```bash
lake build
```
