import RateDistortion.Basic
import RateDistortion.Axioms.RateDistortion

noncomputable section
namespace RateDistortion

/-- RD gap relative to the Shannon lower bound (nats). -/
def rdGapNats (f : ℝ → ℝ) (D : ℝ) : ℝ :=
  rateDistortionFunctionNats f D - shannonLowerBoundNats (diffEntropyNats f) D

/-- RD gap relative to the Shannon lower bound (bits). -/
def rdGapBits (f : ℝ → ℝ) (D : ℝ) : ℝ :=
  rateDistortionFunctionBits f D - shannonLowerBound (diffEntropyBits f) D

/-- Backward-compatible alias: RD gap in bits. -/
abbrev rdGap (f : ℝ → ℝ) (D : ℝ) : ℝ := rdGapBits f D

end RateDistortion
