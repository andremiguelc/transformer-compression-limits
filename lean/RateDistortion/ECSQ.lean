import RateDistortion.Basic
import RateDistortion.Axioms

open scoped BigOperators

noncomputable section
namespace RateDistortion

/-- Step size from target MSE for subtractive dither. -/
def stepFromDistortion (D : ℝ) : ℝ := Real.sqrt (12 * D)

/-- Quantization error (stub until index/recon are defined). -/
def ditherError (x u delta : ℝ) : ℝ :=
  ditherRecon (ditherIndex x u delta) u delta - x

/-- A tail function for later bookkeeping. -/
def tailMass (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∫ x : ℝ, (if T ≤ |x| then f x else 0)

/-- A Lipschitz-type control for a derivative. -/
def lipConst (f' : ℝ → ℝ) : ℝ :=
  sInf {L : ℝ | 0 ≤ L ∧ ∀ x, |f' x| ≤ L}

/-- The classic scalar ECSQ constant: 1/2 log2((2πe)/12). -/
def ecsqConstant : ℝ :=
  (1 / 2) * log2 ((2 * Real.pi * Real.exp 1) / 12)

end RateDistortion
