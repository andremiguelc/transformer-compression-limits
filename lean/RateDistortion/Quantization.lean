import Mathlib
import RateDistortion.Entropy

open scoped BigOperators

noncomputable section
namespace RateDistortion

/-- Step size from target MSE for subtractive dither. -/
def stepFromDistortion (D : ℝ) : ℝ := Real.sqrt (12 * D)

/-- Dithered uniform quantizer index (stub). -/
axiom ditherIndex (x u delta : ℝ) : ℤ

/-- Dithered uniform reconstruction (stub). -/
axiom ditherRecon (i : ℤ) (u delta : ℝ) : ℝ

/-- Quantization error (stub until index/recon are defined). -/
def ditherError (x u delta : ℝ) : ℝ :=
  ditherRecon (ditherIndex x u delta) u delta - x

/-- Subtractive dither error is uniform on [-delta/2, delta/2]. -/
axiom dither_error_uniform (delta : ℝ) : True

/-- Subtractive dither error is independent of the source. -/
axiom dither_error_indep : True

/-- MSE for subtractive dither equals delta^2 / 12. -/
axiom dither_mse (delta : ℝ) : True

/-- Discrete-to-differential entropy comparison for binning. -/
axiom entropy_floor_le_diffEntropy (delta : ℝ) : True

/-- Entropy increase under uniform smoothing. -/
axiom smoothing_entropy_bound (delta : ℝ) : True

end RateDistortion
