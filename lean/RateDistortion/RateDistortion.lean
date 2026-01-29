import RateDistortion.Basic
import RateDistortion.Axioms

noncomputable section
namespace RateDistortion

/-- RD gap relative to the Shannon lower bound. -/
def rdGap (f : ℝ → ℝ) (D : ℝ) : ℝ :=
  rateDistortionFunction f D - shannonLowerBound (diffEntropyBits f) D

end RateDistortion
