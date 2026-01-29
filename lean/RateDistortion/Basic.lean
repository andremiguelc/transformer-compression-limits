import Mathlib

open scoped BigOperators
open MeasureTheory

noncomputable section
namespace RateDistortion

/-- Base-2 logarithm. -/
def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- Differential entropy in bits for a density on R. -/
def diffEntropyBits (f : ℝ → ℝ) : ℝ :=
  - ∫ x : ℝ, f x * log2 (f x)

/-- Differential entropy in nats for a density on R. -/
def diffEntropyNats (f : ℝ → ℝ) : ℝ :=
  - ∫ x : ℝ, f x * Real.log (f x)

/-- Discrete entropy in bits for a pmf on Z. -/
def discreteEntropyBits (p : ℤ → ℝ) : ℝ :=
  - ∑' k : ℤ, p k * log2 (p k)

/-- Shannon lower bound for MSE, given h(X) in bits. -/
def shannonLowerBound (hX D : ℝ) : ℝ :=
  hX - (1 / 2) * log2 (2 * Real.pi * Real.exp 1 * D)

/-- Shannon lower bound for MSE, given h(X) in nats. -/
def shannonLowerBoundNats (hX D : ℝ) : ℝ :=
  hX - (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * D)

/--
Log-concavity predicate for a nonnegative density.

This is a lightweight definition to support later GGD-specific lemmas; it can be
refined once we commit to a particular formalization in Mathlib.
-/
def IsLogConcave (f : ℝ → ℝ) : Prop :=
  ∀ x y t : ℝ, 0 ≤ t ∧ t ≤ 1 →
    f (t * x + (1 - t) * y) ≥
      Real.exp (t * Real.log (f x) + (1 - t) * Real.log (f y))

/--
A (probability) density on ℝ: nonnegative, integrable, and integrates to 1.
-/
def IsDensity (f : ℝ → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ Integrable (μ := volume) f ∧ (∫ x : ℝ, f x = 1)

/--
A density has finite Fisher information if its score is square-integrable.
-/
def HasFiniteFisherInfo (f : ℝ → ℝ) : Prop :=
  ∃ score : ℝ → ℝ,
    (∀ x, f x ≠ 0 → score x = deriv (fun y => Real.log (f y)) x) ∧
      Integrable (fun x => (score x) ^ 2 * f x) volume

end RateDistortion
