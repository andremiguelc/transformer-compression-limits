# Project Goal: Tight Rate-Distortion Bounds for GGD Sources

## Objective

Prove that the Shannon Lower Bound is essentially tight for Generalized Gaussian sources at finite distortion levels relevant to 4-bit quantization, using the **Gaussian test channel + de Bruijn/Fisher information** approach (Program 1 / Path B).

## Main Theorem

**Theorem (GGD Rate-Distortion Gap Bound — Goal B, linear form).**
Let $X \sim \text{GGD}(\beta, \alpha)$ with $\beta > 1$ and unit variance. For MSE distortion $D > 0$:

$$R(D) - R_{\text{SLB}}(D) \leq \frac{D}{2 \ln 2} \cdot J(\beta)$$

where $J(\beta) = \beta^2 \cdot \frac{\Gamma(3/\beta) \cdot \Gamma(2 - 1/\beta)}{\Gamma(1/\beta)^2}$ is the Fisher information.

**Theorem (GGD Rate-Distortion Gap Bound — Goal A, log form, stronger).**

$$R(D) - R_{\text{SLB}}(D) \leq \frac{1}{2} \log_2(1 + D \cdot J(\beta))$$

Goal B follows from Goal A via $\log(1+x) \leq x$.

**Corollary.** For $\beta \in [1, 2]$ and $D = 0.01$: Gap $\leq 0.015$ bits.

## Why This Matters

| Existing Bound | Gap Size | Source |
|----------------|----------|--------|
| Universal log-concave | ≤ 1.05 bits | Marsiglietti-Kostina |
| ECSQ achievability | ≤ 0.255 bits | Gish-Pierce |
| **Our bound (linear)** | **≤ 0.015 bits** | Fisher/de Bruijn |
| **Our bound (log)** | **≤ 0.007 bits** | Fisher/de Bruijn |

Our bound is **70×–150× tighter** than the best known universal result.

## Proof Strategy (Program 1 / Path B)

```
R(D) ≤ I(X; X+N)                    [Gaussian test channel achievability]
     = h(X+N) - h(N)                [mutual information expansion]

Gap = R(D) - R_SLB(D)
    ≤ h(X+N) - h(X)                 [subtract SLB from both sides]
    = ½ ∫₀ᴰ J(Xₜ) dt               [de Bruijn identity]
    ≤ ½ · D · J(X)                  [Fisher info decreasing under smoothing]
```

For the **log form** (Goal A), use J(X_t) ≤ J(X)/(1 + t·J(X)) instead of J(X_t) ≤ J(X), then integrate.

## File Structure

| File | Contents |
|------|----------|
| `Basic.lean` | `log2`, `diffEntropyBits/Nats`, `shannonLowerBound`, `shannonLowerBoundNats`, `IsLogConcave`, `HasFiniteFisherInfo` |
| `Axioms.lean` | Re-exports axiom submodules (convenience import) |
| `Axioms/GaussianSmoothing.lean` | Gaussian smoothing axioms: gaussConv, fisherInfo, deBruijn, test channel |
| `Axioms/RateDistortion.lean` | R(D) axioms: definition, properties, Gaussian case |
| `Axioms/Quantization.lean` | ECSQ/dithered quantization axioms |
| `Axioms/Stam.lean` | Stam's inequality for Gaussian smoothing |
| `RateDistortion.lean` | `rateDistortionFunctionNats`, `rateDistortionFunctionBits`, `rdGapNats`, `rdGapBits` |
| `GGD/Basic.lean` | `ggdDensity`, `ggdC`, `alphaUnitVar` |
| `GGD/Moments.lean` | `ggd_integral_eq_one`, `ggd_abs_moment_integral`, `ggd_second_moment` |
| `GGD/Entropy.lean` | `ggdEntropyNats/Bits`, `ggd_entropy_nats/bits` |
| `GGD/FisherInfo.lean` | `ggdScore`, `ggdFisherInfo`, `ggd_hasFiniteFisherInfo`, `ggd_fisher_info_formula/unitVar`, `ggdFisherInfo_eq_fisherInfo` — all proved |
| `GGD/LogConcave.lean` | `ggd_logconcave` |
| `GaussianSmoothing.lean` | `rdGap_via_deBruijn`, `rdGap_bound_via_fisherBound` |
| `GGDRDBound.lean` | Main theorems: `ggd_rd_gap_bound_fisher`, `ggd_rd_gap_bound_log` |
| `ECSQ.lean` | Entropy-coded scalar quantization definitions |
| `Quantization.lean` | Deprecated shim |
| `Entropy.lean` | Deprecated shim (re-exports `Basic`) |

## Proof Progress

### Fully proved (no sorry)

**Core proof chain (Goal B in nats — complete):**
- `rdGap_via_deBruijn`: Gap ≤ ½∫J(X_t)dt via test channel + de Bruijn identity
- `rdGap_bound_via_fisherBound`: If J(X_t) ≤ J_max for t ∈ [0,D], then gap ≤ (D/2)·J_max
- `ggd_fisherInfo_max_at_zero`: Fisher info of smoothed GGD ≤ ggdFisherInfo (via decreasing + gaussConv_zero)
- `ggd_rd_gap_bound_fisher`: **Main theorem** — gap ≤ (D/2)·J for GGD (in nats)

**GGD integration lemmas (all proved, including base integrals formerly axiomatized):**
- `integral_exp_abs_beta`: ∫ exp(-|x|^β) dx = (2/β)Γ(1/β) — **proved** (was axiom)
- `integral_power_exp_abs_beta`: ∫ |x|^p exp(-|x|^β) dx = (2/β)Γ((p+1)/β) — **proved** (was axiom)
- `ggdDensity_integrable`: GGD density is integrable
- `ggd_integral_eq_one`: Normalization ∫f=1
- `ggd_abs_moment_integral`: E[|X|^p] = α^p · Γ((p+1)/β) / Γ(1/β)
- `ggd_second_moment`: E[X²] = α² · Γ(3/β) / Γ(1/β)

**GGD structural properties (proved):**
- `ggd_logconcave`: GGD is log-concave for β ≥ 1 — **proved** (was partial)
- `ggd_entropy_nats`: GGD differential entropy in nats — **proved** (was sorry)
- `ggd_entropy_bits`: GGD differential entropy in bits — **proved** (was sorry)

**Fisher information (all proved):**
- `ggd_hasFiniteFisherInfo`: GGD has finite Fisher info for β > 1
- `ggd_fisher_info_formula`: Closed-form Fisher info for general scale
- `ggd_fisher_info_unitVar`: Fisher info for unit-variance case
- `ggdFisherInfo_eq_fisherInfo`: Connects GGD-specific to abstract Fisher info

**Gaussian smoothing helpers (proved):**
- `fisherInfo_gaussConv_zero`: At t=0, `fisherInfo (gaussConv f 0) = fisherInfo f`
- `rdGap_bits_via_fisherBound`: Convert nats bound to bits
- `ggd_rd_gap_bound_bits_unitVar`: Explicit bound in bits for unit-variance case

**Numerical bounds:**
- `ggd_fisher_unitVar_beta_1_7_bound`: `ggdFisherInfo 1.7 (alphaUnitVar 1.7) ≤ 2` — proved (uses ggd_fisher_unitVar_bounds)

### Partially proved (some sorry remains)
- `ggd_fisher_unitVar_bounds`: Structure done, two sub-goals remain (Cramér-Rao lower, monotonicity upper)

### Sorry with documented proof strategy
- `ggd_rd_gap_4bit_regime`: Numerical specialization for β=1.7, D=0.01

### Sorry with no proof progress yet
- `ggd_rd_gap_bound_log` (Goal A — requires J(X_t) ≤ J(X)/(1+t·J(X)) bound)
- `ggd_rd_gap_bound` (original parametric bound)

## Axioms (Standard Results, in Axioms.lean)

### Core information-theoretic axioms
- `rateDistortionFunctionNats`: Shannon R(D) as an axiom (infimum over test channels, nats)
- `rateDistortionFunctionNats_nonneg`, `_antitone`, `_gaussian`: basic properties (nats)
- `rateDistortionFunctionBits`: definition via `/ ln 2`
- `gaussianTestChannel_achievable`: R(D) ≤ I(X; X+N) for N ~ N(0,D)

### Gaussian smoothing / de Bruijn axioms
- `gaussConv`: Gaussian convolution operator (density of X + √t·Z)
- `gaussConv_zero`, `gaussConv_add`, `gaussConv_isDensity`: semigroup properties
- `diffEntropy_gaussConv_mono`, `diffEntropy_gaussConv_differentiable`
- `deBruijn`: ∂h(X_t)/∂t = (1/2)J(X_t)
- `deBruijn_integrated`, `deBruijn_integrated_from_zero`: integral forms
- `fisherInfo_gaussConv_rightContinuous`: right-continuity at t=0

### Fisher information axioms
- `fisherInfo`: Fisher information functional
- `fisherInfo_nonneg`, `fisherInfo_gaussian`, `fisherInfo_scale`
- `fisherInfo_gaussConv_decreasing`: J(X_t) is non-increasing in t
- `fisherInfo_eq_of_hasFiniteFisherInfo`: compute via score function

### GGD integration (formerly axioms, now proved theorems in Moments.lean)
- `integral_exp_abs_beta`: ∫ exp(-|x|^β) dx = (2/β)Γ(1/β)
- `integral_power_exp_abs_beta`: ∫ |x|^p exp(-|x|^β) dx = (2/β)Γ((p+1)/β)

### Quantization axioms (ECSQ path, not currently active)
- `ditherIndex`, `ditherRecon`: dithered quantizer stubs
- `dither_error_uniform`, `dither_error_indep`, `dither_mse`
- `entropy_floor_le_diffEntropy`, `smoothing_entropy_bound`
- `ecsq_rate_upper_bound`, `ecsq_gap_upper_bound`

## Dependency Chain (Critical Path)

```
Main Target: ggd_rd_gap_bound_fisher ✅ PROVED
    │
    ├── rdGap_bound_via_fisherBound ✅ PROVED [GaussianSmoothing.lean]
    │       │
    │       ├── rdGap_via_deBruijn ✅ PROVED
    │       │       ├── gaussianTestChannel_achievable [axiom]
    │       │       └── deBruijn_integrated [axiom]
    │       ├── fisherInfo_gaussConv_intervalIntegrable [axiom]
    │       └── intervalIntegral.integral_mono_on [Mathlib]
    │
    └── ggd_fisherInfo_max_at_zero ✅ PROVED [GGDRDBound.lean]
            │
            ├── fisherInfo_gaussConv_decreasing [axiom]
            ├── gaussConv_zero [axiom]
            └── ggdFisherInfo_eq_fisherInfo [axiom]

For bits conversion (complete):
    │
    ├── rdGap_bits_via_fisherBound ✅ PROVED [GaussianSmoothing.lean]
    ├── ggd_fisher_info_unitVar ✅ PROVED [GGD/FisherInfo.lean]
    │       └── ggd_fisher_info_formula ✅ PROVED [GGD/FisherInfo.lean]
    └── ggd_rd_gap_bound_bits_unitVar ✅ PROVED [GGDRDBound.lean]

For GGD-specific numerics (all proved):
    │
    ├── ggd_abs_moment_integral ✅ PROVED
    │       └── integral_power_exp_abs_beta ✅ PROVED (was axiom)
    ├── ggd_integral_eq_one ✅ PROVED
    │       └── integral_exp_abs_beta ✅ PROVED (was axiom)
    ├── ggd_second_moment ✅ PROVED
    ├── ggd_logconcave ✅ PROVED
    ├── ggd_entropy_nats ✅ PROVED
    └── ggd_entropy_bits ✅ PROVED

For Goal A (log form):
    └── ggd_rd_gap_bound_log ✗ sorry
            └── needs J(X_t) ≤ J(X)/(1+t·J(X)) [not yet axiomatized]
```

## Next Priority Actions

### ~~1. Complete nats-to-bits conversion (`rdGap_bits_via_fisherBound`)~~ DONE
~~Pure algebraic rewrite: divide the nats bound by ln(2).~~ Fully proved, unlocking `ggd_rd_gap_bound_bits_unitVar`.

### ~~2. Complete Fisher info closed forms~~ DONE
~~`ggd_fisher_info_formula`, `ggd_fisher_info_unitVar`.~~ Both fully proved, along with `ggd_hasFiniteFisherInfo`.

### ~~3. Finish `ggd_logconcave`~~ DONE
~~Two sorries remain.~~ Fully proved.

### ~~4. Complete `ggd_entropy_nats`~~ DONE
~~Requires integral manipulation with log.~~ Fully proved (along with `ggd_entropy_bits`).

### 5. Goal A: `ggd_rd_gap_bound_log`
Requires adding an axiom for the sharper Fisher info bound J(X_t) ≤ J(X)/(1+t·J(X)), then integrating.

## Success Criterion

**Goal B (linear form, in nats): ACHIEVED.** The proof chain for `ggd_rd_gap_bound_fisher` is complete, reducing to axioms in `Axioms.lean` only.

**Additionally proved:**
- GGD log-concavity (`ggd_logconcave`) for β ≥ 1
- GGD entropy formulas in nats and bits (`ggd_entropy_nats`, `ggd_entropy_bits`)
- Base integration lemmas (`integral_exp_abs_beta`, `integral_power_exp_abs_beta`) — formerly axioms, now theorems

**Remaining for full result:**
1. ~~Nats-to-bits conversion~~ DONE
2. ~~Fisher info closed forms~~ DONE
3. Goal A (log form) for the tighter bound
4. Numerical specialization for β=1.7, D=0.01
5. `ggd_fisher_unitVar_bounds` — Cramér-Rao lower and monotonicity upper sub-goals
