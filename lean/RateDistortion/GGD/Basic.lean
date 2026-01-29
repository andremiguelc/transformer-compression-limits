import Mathlib
import RateDistortion.Basic

noncomputable section
namespace RateDistortion

/-- Normalization constant for the GGD density. -/
def ggdC (beta alpha : ℝ) : ℝ :=
  beta / (2 * alpha * Real.Gamma (1 / beta))

/-- GGD density kernel. -/
def ggdDensity (beta alpha x : ℝ) : ℝ :=
  ggdC beta alpha * Real.exp ( - (|x| / alpha) ^ beta )

/-- Unit-variance scale parameter for a given beta. -/
def alphaUnitVar (beta : ℝ) : ℝ :=
  Real.sqrt (Real.Gamma (1 / beta) / Real.Gamma (3 / beta))

end RateDistortion
