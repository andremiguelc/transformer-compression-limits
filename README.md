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
| Entropy bonus Δh | ~0.26 bits | Minimal gain from GGD-aware codebooks |

**Implication**: The "non-Gaussianity bonus" is negligible. Modern transformer weights (Llama-3, Mistral) are well-behaved—no extreme outliers like older architectures (OPT, BLOOM).

### 2. The Gap from Shannon Bound

At 4-bit quantization (NF4), measured on MLP down-projection layers:

| Quantity | Value |
|----------|-------|
| NF4 weight MSE | ~2.3 × 10⁻⁶ |
| Gaussian Shannon bound D | ~3.6 × 10⁻⁷ |
| **Naive gap** | ~0.86 bits |
| True scalar R(D) via Blahut-Arimoto | ~3.4 bits |
| Shannon Lower Bound (SLB) | ~3.14 bits |
| **True SLB gap** | **~0.26 bits** |

The apparent 0.86-bit gap decomposes into:
- **~0.26 bits**: Inherent gap between scalar R(D) and SLB (not recoverable by any scalar quantizer)
- **~0.6 bits**: Suboptimality of NF4 relative to optimal scalar quantization

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

$$h_{\mathrm{GGD}}(\beta) = \frac{1}{\beta} - \log_2\left(\frac{\beta}{2\Gamma(1/\beta)}\right)$$

### Known Constant-Gap Result

For log-concave sources (including GGD with β ≥ 1):

$$0 \leq R(D) - R_{\mathrm{SLB}}(D) \leq \log_2\sqrt{\frac{\pi e}{2}} \approx 1 \text{ bit}$$

This is a *universal* bound—holds for all distortion levels. Our empirical finding is sharper: **~0.26 bits at 4-bit distortion levels** for β ≈ 1.7.

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

with Δ_β explicit and ~0.2-0.4 bits in the 4-bit regime.

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
└── lean/                                  # Formal proofs in Lean 4 (Mathlib)
```

---

## Key Numerical Results Summary

### Weight Distribution (Llama-3.2-1B MLP down_proj)

```
Layer β (GGD shape):  1.62 - 1.86 (mean ~1.7)
Kurtosis:             3.2 - 4.1 (Gaussian = 3)
KL to Gaussian:       ~0.004 bits
Entropy vs Gaussian:  Δh ≈ 0.26 bits
```

### Rate-Distortion at 4-bit (normalized distortion D ≈ 10⁻²)

```
Shannon Lower Bound:           3.14 bits
True scalar R(D) [BA solver]:  3.40 bits  
Gap R(D) - SLB:                0.26 bits
NF4 operating point:           4.0 bits
Gap NF4 - R(D):                0.60 bits
```

### β-Dependence of SLB Gap (at fixed D_ref)

| β | R(D) | R_SLB | Gap |
|---|------|-------|-----|
| 1.3 | 3.37 | 3.04 | 0.34 |
| 1.7 | 3.40 | 3.15 | 0.26 |
| 2.0 | 3.41 | 3.19 | 0.22 |

As β → 2 (more Gaussian), the gap shrinks—Gaussian sources make SLB tightest.

---

## Strategic Conclusions

### What the Numbers Say

1. **KL = 0.004 bits**: Don't bother modeling the distribution more precisely. Gaussian is fine.

2. **Δh = 0.26 bits**: There's a small theoretical gain from GGD-aware quantization, but NF4 is already close.

3. **SLB gap = 0.26 bits**: Scalar codebook engineering has ~0.6 bits of headroom, not 0.86 bits.

4. **Amplification = 10⁵-10⁶**: The real opportunity is in functional distortion, not weight MSE.

5. **β = 1.7**: Modern architectures are well-behaved. No extreme outliers to handle.

### Research Direction: Theory over Algorithms

The ~1 bit gap is real but small. The more promising direction is **theoretical formalization**:

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
**Dependencies**: `torch`, `transformers`, `scipy`, `bitsandbytes`

---

## Future Work

### Near-term
- [ ] Complete Blahut-Arimoto analysis across all layer types
- [ ] Implement Fisher diagonal estimation for amplification analysis
- [ ] Test on Llama-3.2-3B and Mistral-7B for architecture comparison

### Formalization (Lean 4)
- [x] Formalize GGD density, normalization, moments (proved)
- [x] Prove main RD gap bound via Gaussian test channel + de Bruijn + Fisher info (proved, modulo axioms)
- [ ] Complete nats-to-bits conversion for explicit bound in bits
- [ ] Prove GGD Fisher information closed form
- [ ] Prove log-form bound (Goal A: gap ≤ ½ log₂(1 + D·J))
- [ ] Formalize GGD entropy formula

### Extensions
- [ ] Hardware-constrained R(D) with per-group scaling
- [ ] Vector quantization bounds (E8 lattice analysis)
- [ ] Multi-layer error propagation analysis

---

## Contact

This is an independent research project investigating the theoretical foundations of transformer compression. Contributions, discussions, and collaboration opportunities welcome.

**Focus areas**: Rate-distortion theory, information theory, formal verification (Lean), transformer inference efficiency.