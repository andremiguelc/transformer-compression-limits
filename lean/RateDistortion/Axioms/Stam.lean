import Mathlib
import RateDistortion.Basic
import RateDistortion.Axioms.GaussianSmoothing

noncomputable section
namespace RateDistortion

section Stam
/--
Stam / Blachman–Stam inequality for Gaussian smoothing, in bound form.

This implies the reciprocal Fisher information inequality and yields
`J(X_t) ≤ J(X) / (1 + t·J(X))`, which is exactly what is needed for Goal A.
-/
axiom fisherInfo_gaussConv_stam (f : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf : IsDensity f) (hfi : HasFiniteFisherInfo f) :
  fisherInfo (gaussConv f t) ≤ fisherInfo f / (1 + t * fisherInfo f)
end Stam

end RateDistortion
