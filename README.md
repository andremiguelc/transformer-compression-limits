# Information-Theoretic Bounds for Transformer Weight Quantization

An investigation into the fundamental limits of transformer weight compression, combining empirical analysis with rate-distortion theory to identify opportunities for theoretical contributions.

## Research Question

**How far are current quantization methods from Shannon's theoretical limits, and what structural properties of transformer weights enable (or limit) compression?**

This project pursues a theory-first approach: characterizing the gap between practice and information-theoretic bounds, then identifying which gaps represent genuine algorithmic opportunities versus fundamental limits.

---

## Key Empirical Findings

All experiments conducted on **Llama-3.2-1B** using the notebooks in this repository.

### 1. Weight Distribution: Generalized Gaussian with β ≈ 1.7

Transformer MLP weights follow a **Generalized Gaussian Distribution (GGD)** with shape parameter:

$$X \sim \mathrm{GGD}(\beta), \quad \beta \in [1.62, 1.86] \text{ across layers}$$

This is "medium-tailed" behavior—between pure Gaussian (β = 2) and Laplacian (β = 1). Critically:

| Metric | Value | Interpretation |
|--------|-------|----------------|
| Mean β | ~1.7 | Slightly heavier tails than Gaussian |
| KL(weights ∥ Gaussian) | ~0.004 bits | Weights are *essentially Gaussian* |
| Entropy bonus Δh | ~0.02 bits | Minimal gain from GGD-aware codebooks |

**Implication**: The "non-Gaussianity bonus" is negligible. Modern transformer weights (Llama-3, Mistral) are well-behaved—no extreme outliers like older architectures (OPT, BLOOM).  
*Note:* An earlier ~0.26-bit estimate came from a unit-mixed entropy formula; the corrected bits entropy uses a $1/(\beta\ln 2)$ term.

### 2. The Gap from Shannon Bound

At 4-bit quantization (NF4), measured on MLP down-projection layers:

| Quantity | Value |
|----------|-------|
| NF4 weight MSE | ~2.3 × 10⁻⁶ |
| True scalar R(D) via Blahut-Arimoto | ~3.4 bits |
| Shannon Lower Bound (SLB, corrected) | ~3.41 bits |
| **True SLB gap** | **≈ 0.00 bits (≈ −0.002)** |
| NF4 operating rate | 4.0 bits |
| **NF4 − R(D)** | **~0.60 bits** |

The apparent gap is **not** a fundamental R(D)−SLB gap. Instead:
- **≈ 0 bits**: Inherent gap between scalar R(D) and SLB (essentially tight at D≈10⁻²)
- **~0.60 bits**: Suboptimality of NF4 relative to optimal scalar quantization (uniform grid + blockwise overhead)

### 3. Functional vs Weight Distortion: The Amplification Problem

The most striking finding—weight MSE is a **poor proxy** for model quality:

$$\frac{\text{Logits MSE}}{\text{Weight MSE}} \approx 5 \times 10^5 \text{ to } 7 \times 10^5$$

This massive amplification factor explains why:
- Methods like AWQ/GPTQ (which optimize for activations) beat naive weight quantization
- The true optimization objective is $\Delta W^\top G \Delta W$ where G is Fisher/Hessian-like
- Small subsets of weights disproportionately affect outputs

### 4. Cross-Entropy Impact

| Method | ΔCE (vs FP16) | Interpretation |
|--------|---------------|----------------|
| NF4 4-bit | ~0.032 | ~3% perplexity increase |
| FP4 4-bit | ~0.041 | Slightly worse than NF4 |

Both are practical for deployment. The gap from "perfect" 4-bit quantization is small in end-task terms.

---

## Theoretical Framework

### Shannon Lower Bound (SLB)

For any source X with differential entropy h(X):

$$R(D) \geq R_{\mathrm{SLB}}(D) = h(X) - \frac{1}{2}\log_2(2\pi e D)$$

For GGD(β) with unit variance:

$$h_{\mathrm{GGD}}(\beta) = \frac{1}{\beta \ln 2} + \log_2\left(\frac{2\alpha_{\text{unit}}(\beta)\Gamma(1/\beta)}{\beta}\right)$$

where $\alpha_{\text{unit}}(\beta) = \sqrt{\Gamma(1/\beta)/\Gamma(3/\beta)}$.

### Known Constant-Gap Result

For log-concave sources (including GGD with β ≥ 1):

$$0 \leq R(D) - R_{\mathrm{SLB}}(D) \leq \log_2\sqrt{\frac{\pi e}{2}} \approx 1 \text{ bit}$$

This is a *universal* bound—holds for all distortion levels. Our empirical finding is sharper: **gap ≈ 0 bits (≈ −0.002)** at 4-bit distortion levels for β ≈ 1.7.

### The Functional Distortion Geometry

True model degradation follows:

$$D_{\mathrm{func}}(\Delta W) = \mathbb{E}_x\|f(W + \Delta W, x) - f(W, x)\|^2 \approx \mathrm{vec}(\Delta W)^\top G \, \mathrm{vec}(\Delta W)$$

where $G = \mathbb{E}_x[J_x^\top J_x]$ is the Fisher/Gram matrix. High condition number κ(G) ≫ 1 explains the amplification phenomenon.

---

## Theorem Opportunities

Based on the empirical findings, five concrete theorem targets have been identified:

### Opportunity 1: Quadratic R(D) Bounds for GGD

**Target**: Prove explicit two-sided bounds for β ∈ [1.6, 1.9]:

$$R_{\mathrm{SLB}}(D) \leq R(D) \leq R_{\mathrm{SLB}}(D) + \Delta_\beta(D)$$

with Δ_β explicit and on the order of 10⁻² bits in the 4-bit regime.

**Why it matters**: Converts empirical observation into a theorem; clarifies when codebook engineering yields diminishing returns.

### Opportunity 2: NF4 Mismatch Penalty

**Target**: Bound the cost of using a Gaussian-tuned codebook (NF4) on GGD(β) weights:

$$\frac{D(Q_{\mathrm{NF4}}; \mathrm{GGD})}{D^*(\mathrm{GGD})} \leq \Phi(D_{\mathrm{KL}}(\mathrm{GGD} \| \mathcal{N}), R)$$

**Why it matters**: Predicts when NF4 is "close enough" despite β ≠ 2, and when optimized codebooks should win.

### Opportunity 3: Price of Uniformity

**Target**: Quantify the rate loss from hardware-friendly uniform grids vs Lloyd-Max:

$$R_{\mathrm{uniform}}(D) \leq R^*(D) + \rho(\beta)$$

**Why it matters**: Guides whether LUT-based nonuniform quantization is worth kernel complexity.

### Opportunity 4: Blockwise Absmax as Order Statistics

**Target**: For group quantization with absmax scaling S = max|X_i|:

$$D_n^{\mathrm{absmax}} - D_n^{\mathrm{quantile}} \geq \Psi(n, \beta)$$

**Why it matters**: Explains why percentile scaling beats absmax for heavy-tailed weights; guides group size selection.

### Opportunity 5: Functional Amplification via Fisher Geometry

**Target**: Prove G is highly anisotropic under transformer assumptions:

$$\kappa(G) = \frac{\lambda_{\max}(G)}{\lambda_{\min}(G)} \gg 1$$

and derive optimal bit allocation as water-filling over G's eigenmodes.

**Why it matters**: Provides principled bridge from weight MSE to accuracy loss; explains "protect important weights" heuristics.

---

## Repository Structure

```
├── README.md                              # This file
├── notebooks/
│   ├── 01_weight_statistics.ipynb         # GGD fitting, kurtosis, KL analysis
│   ├── 02_1_quantization_rate_distortion.ipynb  # Scalar/group quantization R(D)
│   └── 02_2_quantization_rate_distortion.ipynb  # NF4/FP4 comparison, BA solver
├── lean/                                  # Formal proofs in Lean 4 (Mathlib)
│   ├── RateDistortion/
│   │   ├── Basic.lean                     # Core definitions (log2, entropy, SLB)
│   │   ├── Axioms/                        # Standard results taken as axioms
│   │   ├── RateDistortion.lean            # R(D) in nats/bits, RD gap
│   │   ├── GaussianSmoothing.lean         # de Bruijn framework (proved)
│   │   ├── GGD/                           # GGD-specific proofs
│   │   │   ├── Basic.lean                 #   Density, normalization constants
│   │   │   ├── Moments.lean               #   Integrals and moments (proved)
│   │   │   ├── Entropy.lean               #   Entropy in nats/bits (proved)
│   │   │   ├── FisherInfo.lean            #   Fisher information (proved)
│   │   │   ├── FisherInfoBounds.lean      #   Numerical bounds (partial)
│   │   │   └── LogConcave.lean            #   Log-concavity for β ≥ 1 (proved)
│   │   ├── GGDRDBound.lean               # Main theorem (proved)
│   │   └── ECSQ.lean                     # ECSQ scaffolding
│   └── lakefile.toml                      # Lean build config (Mathlib v4.26.0)
└── requirements.txt                       # Python dependencies for notebooks
```

---

## Lean Formalization

The formal proofs are in Lean 4 with Mathlib. The main result and its dependencies are fully proved.

### GGD Rate-Distortion Gap Bound (proved)

For $X \sim \text{GGD}(\beta, \alpha)$ with $\beta > 1$ and unit variance, for MSE distortion $D > 0$:

$$R(D) - R_{\text{SLB}}(D) \leq \frac{D}{2 \ln 2} \cdot J(\beta)$$

where $J(\beta) = \beta^2 \cdot \frac{\Gamma(3/\beta) \cdot \Gamma(2 - 1/\beta)}{\Gamma(1/\beta)^2}$ is the Fisher information. This bound is **70–150× tighter** than the best known universal result (~1.05 bits).

### Proof Strategy

```
R(D) ≤ I(X; X+N)                    [Gaussian test channel]
Gap = R(D) - R_SLB(D)
    ≤ h(X+N) - h(X)                 [subtract SLB]
    = ½ ∫₀ᴰ J(Xₜ) dt               [de Bruijn identity]
    ≤ ½ · D · J(X)                  [Fisher info decreasing under smoothing]
```

### Proof Status

| Component | Status |
|-----------|--------|
| Main RD gap bound (`ggd_rd_gap_bound_fisher`) | Proved |
| Bits conversion (`ggd_rd_gap_bound_bits_unitVar`) | Proved |
| de Bruijn framework (`rdGap_via_deBruijn`) | Proved |
| GGD entropy in nats/bits | Proved |
| GGD Fisher information closed form | Proved |
| GGD log-concavity for β ≥ 1 | Proved |
| GGD normalization and moments | Proved |
| Base integration lemmas | Proved |
| Log-form bound (gap ≤ ½ log₂(1 + D·J)) | Open |
| Numerical specialization (β=1.7, D=0.01) | Open |

The proof reduces to axioms for standard information-theoretic results (R(D) definition, de Bruijn identity, Fisher info monotonicity under Gaussian convolution) documented in `lean/RateDistortion/Axioms/`.

### Building

```bash
cd lean && lake build
```

---

## Key Numerical Results Summary

### Weight Distribution (Llama-3.2-1B MLP down_proj)

```
Layer β (GGD shape):  1.62 - 1.86 (mean ~1.7)
Kurtosis:             3.2 - 4.1 (Gaussian = 3)
KL to Gaussian:       ~0.004 bits
Entropy vs Gaussian:  Δh ≈ 0.02 bits
```

### Rate-Distortion at 4-bit (normalized distortion D ≈ 10⁻²)

```
Shannon Lower Bound:           3.41 bits
True scalar R(D) [BA solver]:  3.40 bits  
Gap R(D) - SLB:                -0.002 bits (≈ 0)
NF4 operating point:           4.0 bits
Gap NF4 - R(D):                0.60 bits
```

### β-Dependence of SLB Gap (at fixed D_ref)

| β | R(D) | R_SLB | Gap |
|---|------|-------|-----|
| 1.3 | 3.373 | 3.375 | -0.002 |
| 1.7 | 3.404 | 3.406 | -0.002 |
| 2.0 | 3.408 | 3.410 | -0.002 |

Across β, the gap is essentially zero (small negative values reflect BA discretization).

---

## Strategic Conclusions

### What the Numbers Say

1. **KL = 0.004 bits**: Don't bother modeling the distribution more precisely. Gaussian is fine.

2. **Δh = 0.02 bits**: There's a tiny theoretical gain from GGD-aware quantization, but NF4 is already close.

3. **SLB gap ≈ 0 bits**: The fundamental gap is essentially zero; the ~0.6-bit headroom is from quantizer constraints, not R(D)−SLB.

4. **Amplification = 10⁵-10⁶**: The real opportunity is in functional distortion, not weight MSE.

5. **β = 1.7**: Modern architectures are well-behaved. No extreme outliers to handle.

### Research Direction: Theory over Algorithms

The universal ~1-bit bound is real but loose; empirically the gap is ~0 for GGD. The more promising direction is **theoretical formalization**:

- **What exists**: Empirical measurements of β, gaps, amplification ratios
- **What's missing**: Proofs that these observations are fundamental

Formalizable contributions that don't require GPU clusters:
1. Rate-distortion bound for GGD sources (closed-form R(D) for β ∈ (1,2))
2. Gap bound for scalar uniform quantization of sub-Gaussian sources
3. Optimality conditions for group quantization

---

## References

### Foundational Papers

1. **Gao et al. (ICML 2019)**: "Rate Distortion For Model Compression" — R(D) for neural networks
2. **QuIP (NeurIPS 2023)**: Incoherence + lattice codebooks for 2-bit quantization
3. **QuIP# (ICML 2024)**: Hadamard transforms + E8 lattice
4. **GPFQ (SIAM 2024)**: Provable post-training quantization guarantees
5. **AWQ (MLSys 2024)**: Activation-aware weight quantization

### Information Theory

- Cover & Thomas, *Elements of Information Theory* (Ch. 10: Rate-Distortion)
- Berger, *Rate Distortion Theory* (1971)

### Quantization Theory

- Lloyd (1982): Optimal scalar quantization
- Gray & Neuhoff (1998): Quantization survey

---

## Reproducibility

**Model**: `meta-llama/Llama-3.2-1B` via HuggingFace
**Quantization**: `bitsandbytes` NF4/FP4 (4-bit, group size 64)
**Compute**: Google Colab T4 GPU sufficient for all experiments

```bash
pip install -r requirements.txt
```

---

## Future Work

### Formalization
- [ ] Prove log-form bound (gap ≤ ½ log₂(1 + D·J)) — tighter than current linear bound
- [ ] Numerical specialization for β = 1.7, D = 0.01

### Empirical
- [ ] Complete Blahut-Arimoto analysis across all layer types
- [ ] Fisher diagonal estimation for amplification analysis
- [ ] Test on Llama-3.2-3B and Mistral-7B for architecture comparison

### Extensions
- [ ] Hardware-constrained R(D) with per-group scaling
- [ ] Vector quantization bounds (E8 lattice analysis)
- [ ] Multi-layer error propagation analysis

---

## Contact

This is an independent research project investigating the theoretical foundations of transformer compression. Contributions, discussions, and collaboration opportunities welcome.

**Focus areas**: Rate-distortion theory, information theory, formal verification (Lean), transformer inference efficiency.
