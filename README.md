# Information-Theoretic Bounds for Transformer Weight Quantization

An investigation into the fundamental limits of transformer weight compression, combining empirical analysis with rate-distortion theory.

## Research Question

**How far are current quantization methods from Shannon's theoretical limits, and what structural properties of transformer weights enable (or limit) compression?**

See [paper/rd_gap_formalization.pdf](paper/rd_gap_formalization.pdf) for the formal write-up.

---

## Main Results

All experiments on **Llama-3.2-1B** MLP layers. Key findings:

| Finding | Value | Implication |
|---------|-------|-------------|
| GGD shape β | 1.62–1.86 (mean ~1.7) | Medium-tailed, between Gaussian and Laplacian |
| KL(weights ∥ Gaussian) | ~0.004 bits | Weights are essentially Gaussian—don't over-model |
| R(D) − SLB gap | ≈ 0 bits | Shannon bound is tight; no fundamental gap |
| NF4 − R(D) gap | ~0.60 bits | Headroom is from quantizer constraints, not theory |
| Logits/Weight MSE ratio | 10⁵–10⁶ | Weight MSE is a poor proxy for model quality |

**Takeaway**: Modern transformer weights are well-behaved (β ≈ 1.7, no extreme outliers). The ~0.6-bit gap from optimal comes from practical constraints (uniform grids, blockwise scaling), not information-theoretic limits. The real opportunity is in functional distortion geometry, not weight-space optimization.

---

## Lean Formalization

The main theorem is fully proved in Lean 4 with Mathlib:

**GGD Rate-Distortion Gap Bound**: For $X \sim \text{GGD}(\beta)$ with $\beta > 1$ and unit variance:

$$R(D) - R_{\text{SLB}}(D) \leq \frac{D}{2 \ln 2} \cdot J(\beta)$$

where $J(\beta)$ is the Fisher information. This bound is **70–150× tighter** than the universal ~1-bit result.

```bash
cd lean && lake build
```

See the paper for proof details and status of individual components.

---

## Repository Structure

```
├── paper/                    # Formal write-up (PDF)
├── notebooks/
│   ├── 01_weight_statistics.ipynb         # GGD fitting, KL analysis
│   ├── 02_1_quantization_rate_distortion.ipynb  # Scalar R(D)
│   └── 02_2_quantization_rate_distortion.ipynb  # NF4/FP4, Blahut-Arimoto
├── lean/                     # Lean 4 proofs (Mathlib v4.26.0)
│   └── RateDistortion/       # Core definitions, GGD proofs, main theorem
└── requirements.txt
```

---

## Future Work

- [ ] Prove tighter log-form bound: gap ≤ ½ log₂(1 + D·J)
- [ ] Fisher diagonal estimation for amplification analysis
- [ ] Vector quantization bounds (E8 lattice)
- [ ] Test on larger models (Llama-3.2-3B, Mistral-7B)

---

## Reproducibility

```bash
pip install -r requirements.txt
```

Model: `meta-llama/Llama-3.2-1B` via HuggingFace
Quantization: `bitsandbytes` NF4/FP4 (4-bit, group size 64)
Compute: Google Colab T4 GPU sufficient

---

## References

- Gao et al., "Rate Distortion For Model Compression" (ICML 2019)
- QuIP (NeurIPS 2023), QuIP# (ICML 2024)
- GPFQ (SIAM 2024), AWQ (MLSys 2024)
- Cover & Thomas, *Elements of Information Theory*
