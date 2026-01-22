# Transformer Compression Limits

Empirical and theoretical investigation of information-theoretic bounds for transformer weight compression.

## Research Questions
1. How far are current quantization methods from Shannon's rate-distortion bound?
2. What structure in transformer weights enables compression beyond i.i.d. assumptions?
3. Can we derive tighter R(D) bounds for structured weight matrices?

## Structure
- `notebooks/` — Colab notebooks (empirical analysis)
- `lean/` — Formalized proofs (rate-distortion theory)

## Key Findings
*In progress*

## References
- [AWQ: Activation-aware Weight Quantization](https://arxiv.org/abs/2306.00978)
- [QuIP#: 2-bit Quantization](https://arxiv.org/abs/2402.04396)