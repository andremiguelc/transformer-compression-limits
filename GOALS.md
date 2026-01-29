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
| `Basic.lean` | `log2`, `diffEntropyBits/Nats`, `shannonLowerBound`, `IsLogConcave`, `HasFiniteFisherInfo` |
| `Axioms.lean` | All axioms: deBruijn, gaussConv, fisherInfo, test channel, GGD integration |
| `RateDistortion.lean` | `rateDistortionFunction` (axiom), `rdGap` definition |
| `GGD/Basic.lean` | `ggdDensity`, `ggdC`, `alphaUnitVar` |
| `GGD/Moments.lean` | `ggd_integral_eq_one`, `ggd_abs_moment_integral`, `ggd_second_moment` |
| `GGD/Entropy.lean` | `ggdEntropyNats/Bits`, `ggd_entropy_nats/bits` |
| `GGD/FisherInfo.lean` | `ggdScore`, `ggdFisherInfo`, `ggd_fisher_info_formula/unitVar` |
| `GGD/LogConcave.lean` | `ggd_logconcave` |
| `GaussianSmoothing.lean` | `rdGap_via_deBruijn`, `rdGap_bound_via_fisherBound` |
| `GGDRDBound.lean` | Main theorems: `ggd_rd_gap_bound_fisher`, `ggd_rd_gap_bound_log` |
| `ECSQ.lean` | Entropy-coded scalar quantization definitions |
| `Quantization.lean` | Deprecated shim |
| `Entropy.lean` | Deprecated shim (re-exports `Basic`) |

## Proof Progress

### Proved (no sorry)
- `fisherInfo_gaussConv_zero`: At t=0, `fisherInfo (gaussConv f 0) = fisherInfo f`
- `ggd_fisher_unitVar_beta_1_7_bound`: `ggdFisherInfo 1.7 (alphaUnitVar 1.7) ≤ 2` (from `ggd_fisher_unitVar_bounds`)

### Partially proved (some sorry remains)
- `ggd_logconcave`: Triangle inequality done, convexity of `z ↦ z^β` and final combination remain
- `ggd_fisher_unitVar_bounds`: Structure done, two sub-goals remain (Cramér-Rao lower, monotonicity upper)

### Outlined with proof strategy (sorry, strategy documented)
- `ggd_integral_eq_one`: Change of variables + `integral_exp_abs_beta` axiom
- `ggd_abs_moment_integral`: Change of variables + `integral_power_exp_abs_beta` axiom
- `ggd_second_moment`: Follows from `ggd_abs_moment_integral` with p=2
- `ggd_entropy_nats`: Expand integral, use normalization + moment formula
- `ggd_entropy_bits`: Convert from nats via `/ ln 2`
- `ggd_rd_gap_bound_fisher`: Apply `rdGap_bound_via_fisherBound` + `ggd_fisherInfo_max_at_zero`

### Sorry with no proof progress yet
- `ggdDensity_integrable`
- `ggd_hasFiniteFisherInfo`
- `ggd_fisher_info_formula`
- `ggd_fisher_info_unitVar`
- `ggd_fisherInfo_max_at_zero`
- `rdGap_via_deBruijn`
- `rdGap_bound_via_fisherBound`
- `rdGap_bits_via_fisherBound`
- `ggd_rd_gap_bound_bits_unitVar`
- `ggd_rd_gap_bound_log` (Goal A)
- `ggd_rd_gap_4bit_regime`
- `ggd_rd_gap_bound` (original parametric bound)

## Axioms (Standard Results, in Axioms.lean)

### Core information-theoretic axioms
- `rateDistortionFunction`: Shannon R(D) as an axiom (infimum over test channels)
- `rateDistortionFunction_nonneg`, `_antitone`, `_gaussian`: basic properties
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

### GGD-specific axioms
- `integrable_exp_abs_beta`, `integrable_power_exp_abs_beta`: integrability
- `integral_exp_abs_beta`: ∫ exp(-|x|^β) dx = (2/β)Γ(1/β)
- `integral_power_exp_abs_beta`: ∫ |x|^p exp(-|x|^β) dx = (2/β)Γ((p+1)/β)
- `ggdFisherInfo_eq_fisherInfo`: connects GGD-specific to abstract Fisher info

### Quantization axioms (ECSQ path, not currently active)
- `ditherIndex`, `ditherRecon`: dithered quantizer stubs
- `dither_error_uniform`, `dither_error_indep`, `dither_mse`
- `entropy_floor_le_diffEntropy`, `smoothing_entropy_bound`
- `ecsq_rate_upper_bound`, `ecsq_gap_upper_bound`

## Dependency Chain (Critical Path)

```
Main Target: ggd_rd_gap_bound_fisher (or ggd_rd_gap_bound_log)
    │
    ├── rdGap_bound_via_fisherBound [GaussianSmoothing.lean]
    │       │
    │       ├── gaussianTestChannel_achievable [axiom]
    │       ├── deBruijn_integrated_from_zero [axiom]
    │       └── interval integral bound [needs MeasureTheory.integral_le_of_le]
    │
    └── ggd_fisherInfo_max_at_zero [GGDRDBound.lean]
            │
            ├── fisherInfo_gaussConv_decreasing [axiom]
            ├── gaussConv_zero [axiom]
            └── ggdFisherInfo_eq_fisherInfo [axiom]

For GGD-specific numerics:
    │
    ├── ggd_fisher_info_unitVar
    │       └── ggd_fisher_info_formula
    │               └── ggd_abs_moment_integral (with p = 2β-2)
    │                       └── integral_power_exp_abs_beta [axiom]
    │
    └── ggd_entropy_nats
            ├── ggd_integral_eq_one
            │       └── integral_exp_abs_beta [axiom]
            └── ggd_abs_moment_integral (with p = β)
                    └── integral_power_exp_abs_beta [axiom]
```

## Next Priority Actions

### 1. Complete `rdGap_bound_via_fisherBound` (the bridge theorem)
This is the central theorem connecting axioms to the gap bound. It requires:
- `gaussianTestChannel_achievable` (axiom) for R(D) ≤ I(X; X+N)
- `deBruijn_integrated_from_zero` (axiom) for h(X+N) - h(X) = ½∫J(X_t)dt
- Interval integral monotonicity: if J(X_t) ≤ J_max for t ∈ [0,D], then ∫ ≤ D·J_max

### 2. Complete `ggd_fisherInfo_max_at_zero`
Uses `fisherInfo_gaussConv_decreasing` + `gaussConv_zero` + `ggdFisherInfo_eq_fisherInfo`.

### 3. Finish `ggd_logconcave`
One sorry remains: convexity of `z ↦ z^β` on `[0,∞)` for `β ≥ 1`. Check if `Mathlib.Analysis.SpecialFunctions.Pow.NNReal` has what's needed.

### 4. Complete GGD integration proofs
All reduce to the axioms `integral_exp_abs_beta` / `integral_power_exp_abs_beta` plus algebraic manipulation (factoring out constants, scaling).

## Success Criterion

A complete proof of `ggd_rd_gap_bound_fisher` with explicit dependence on $\beta$ and $D$, reducing to the axioms listed above. The proof chain should be:

1. `ggd_rd_gap_bound_fisher` calls `rdGap_bound_via_fisherBound` + `ggd_fisherInfo_max_at_zero`
2. `rdGap_bound_via_fisherBound` uses `gaussianTestChannel_achievable` + `deBruijn_integrated_from_zero` + integral bound
3. `ggd_fisherInfo_max_at_zero` uses `fisherInfo_gaussConv_decreasing` + `gaussConv_zero` + `ggdFisherInfo_eq_fisherInfo`

All intermediate steps should be proved, with only the axioms in `Axioms.lean` remaining as sorry-free assumptions.
