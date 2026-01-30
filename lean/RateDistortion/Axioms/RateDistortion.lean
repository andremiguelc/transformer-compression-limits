import Mathlib
import RateDistortion.Basic

noncomputable section
namespace RateDistortion

section RateDistortion
/-- Shannon rate–distortion function for a density `f` (nats). -/
axiom rateDistortionFunctionNats (f : ℝ → ℝ) (D : ℝ) : ℝ

/-- Shannon rate–distortion function for a density `f` (bits). -/
def rateDistortionFunctionBits (f : ℝ → ℝ) (D : ℝ) : ℝ :=
  rateDistortionFunctionNats f D / Real.log 2

/-- R(D) is non-negative (nats). -/
axiom rateDistortionFunctionNats_nonneg (f : ℝ → ℝ) (D : ℝ) (hD : 0 < D) :
  0 ≤ rateDistortionFunctionNats f D

/-- R(D) is non-increasing in D (nats). -/
axiom rateDistortionFunctionNats_antitone (f : ℝ → ℝ) :
  Antitone (rateDistortionFunctionNats f)

/-- R(D) achieves the Shannon lower bound for Gaussian sources (nats). -/
axiom rateDistortionFunctionNats_gaussian (σ D : ℝ) (hσ : 0 < σ) (hD : 0 < D)
    (hDσ : D ≤ σ ^ 2) :
  rateDistortionFunctionNats
      (fun x => (1 / (σ * Real.sqrt (2 * Real.pi))) * Real.exp (- x ^ 2 / (2 * σ ^ 2))) D =
    (1 / 2) * Real.log (σ ^ 2 / D)
end RateDistortion

end RateDistortion
