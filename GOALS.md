# Project Goal: Tight Rate-Distortion Bounds for GGD Sources

## Objective

Prove that the Shannon Lower Bound is tight for Generalized Gaussian sources at finite distortion levels relevant to 4-bit quantization.

## Main Theorem

**Theorem (GGD Rate-Distortion Gap Bound).**
Let $X \sim \text{GGD}(\beta, \alpha)$ with $\beta > 1$ and unit variance. For MSE distortion $D > 0$:

$$R(D) - R_{\text{SLB}}(D) \leq \frac{D}{2 \ln 2} \cdot J(\beta)$$

where $J(\beta) = \beta^2 \cdot \frac{\Gamma(3/\beta) \cdot \Gamma(2 - 1/\beta)}{\Gamma(1/\beta)^2}$ is the Fisher information.

**Corollary.** For $\beta \in [1, 2]$ and $D = 0.01$: Gap $\leq 0.015$ bits.

## Why This Matters

| Existing Bound | Gap Size | Source |
|----------------|----------|--------|
| Universal log-concave | ≤ 1.05 bits | Marsiglietti-Kostina |
| ECSQ achievability | ≤ 0.255 bits | Gish-Pierce |
| **Our bound** | **≤ 0.015 bits** | Fisher/de Bruijn |

Our bound is **70× tighter** than the best known universal result.

## Proof Strategy

```
R(D) ≤ I(X; X+N)                    [Gaussian test channel achievability]
     = h(X+N) - h(N)                [mutual information expansion]

Gap = R(D) - R_SLB(D)
    ≤ h(X+N) - h(X)                 [subtract SLB from both sides]
    = ½ ∫₀ᴰ J(Xₜ) dt               [de Bruijn identity]
    ≤ ½ · D · J(X)                  [Fisher info decreasing under smoothing]
```

## File Structure

| File | Contents |
|------|----------|
| `Entropy.lean` | log₂, differential entropy, Shannon lower bound |
| `GGD.lean` | GGD density, moments, entropy, Fisher information, log-concavity |
| `GaussianSmoothing.lean` | Gaussian convolution, de Bruijn identity, Fisher monotonicity |
| `GGDRDBound.lean` | Main theorem connecting GGD to the bound |
| `Quantization.lean` | Rate-distortion function definition |

## Key Lemmas Needed

1. **`ggd_integral_eq_one`**: GGD integrates to 1
2. **`ggd_entropy_nats`**: Closed-form entropy $h(X) = \frac{1}{\beta} + \ln\frac{2\alpha\Gamma(1/\beta)}{\beta}$
3. **`ggd_fisher_info_formula`**: Closed-form Fisher information
4. **`ggd_logconcave`**: GGD is log-concave for $\beta \geq 1$
5. **`ggd_fisherInfo_max_at_zero`**: $J(X_t) \leq J(X)$ for all $t \geq 0$

## Axioms (Standard Results)

- `deBruijn`: $\frac{d}{dt} h(X_t) = \frac{1}{2} J(X_t)$
- `fisherInfo_gaussConv_decreasing`: Fisher info monotone under smoothing
- `gaussianTestChannel_achievable`: $R(D) \leq I(X; X + N)$ for $N \sim \mathcal{N}(0, D)$

## Success Criterion

A complete proof of `ggd_rd_gap_bound_fisher` with explicit dependence on $\beta$ and $D$, reducing to the axioms above.