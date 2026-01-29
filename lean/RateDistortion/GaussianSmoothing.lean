import Mathlib
import RateDistortion.Basic
import RateDistortion.Axioms

open scoped BigOperators
open MeasureTheory

noncomputable section
namespace RateDistortion

/-!
# Gaussian Smoothing and de Bruijn Identity

This file contains the main theorems using the Gaussian smoothing axioms
collected in `RateDistortion.Axioms`.
-/

/--
Gap bound via de Bruijn identity (in nats).

The RD gap is bounded by the entropy increase under Gaussian smoothing,
which equals (1/2) times the integral of Fisher information.
-/
theorem rdGap_via_deBruijn (f : ℝ → ℝ) (D : ℝ) (hD : 0 < D) :
  rateDistortionFunctionNats f D - diffEntropyNats f + (1/2) * Real.log (2 * Real.pi * Real.exp 1 * D)
    ≤ (1/2) * ∫ s in (0:ℝ)..D, fisherInfo (gaussConv f s) := by
  have hAch := gaussianTestChannel_achievable f D hD
  have hDeb := deBruijn_integrated f D hD
  have h1 :
      rateDistortionFunctionNats f D - diffEntropyNats f +
        (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * D)
        ≤ gaussianTestChannelRate f D - diffEntropyNats f +
          (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * D) := by
    linarith
  have h2 :
      gaussianTestChannelRate f D - diffEntropyNats f +
        (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * D)
        = diffEntropyNats (gaussConv f D) - diffEntropyNats f := by
    simp [gaussianTestChannelRate, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  calc
    rateDistortionFunctionNats f D - diffEntropyNats f +
        (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * D)
        ≤ gaussianTestChannelRate f D - diffEntropyNats f +
          (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * D) := h1
    _ = diffEntropyNats (gaussConv f D) - diffEntropyNats f := h2
    _ = (1 / 2) * ∫ s in (0:ℝ)..D, fisherInfo (gaussConv f s) := by
          simpa using hDeb

/--
If Fisher information is bounded by J_max along the Gaussian smoothing path,
then the RD gap is at most (D/2)·J_max.
-/
theorem rdGap_bound_via_fisherBound (f : ℝ → ℝ) (D J_max : ℝ)
    (hD : 0 < D) (hJ : ∀ s, 0 ≤ s → s ≤ D → fisherInfo (gaussConv f s) ≤ J_max) :
  rateDistortionFunctionNats f D - diffEntropyNats f +
      (1/2) * Real.log (2 * Real.pi * Real.exp 1 * D)
    ≤ (D / 2) * J_max := by
  have h0 := rdGap_via_deBruijn f D hD
  have hJ' : ∀ s, s ∈ Set.Icc (0:ℝ) D → fisherInfo (gaussConv f s) ≤ J_max := by
    intro s hs
    exact hJ s hs.1 hs.2
  have hf : IntervalIntegrable (fun s => fisherInfo (gaussConv f s)) volume (0:ℝ) D :=
    fisherInfo_gaussConv_intervalIntegrable f D
  have hg : IntervalIntegrable (fun _ : ℝ => J_max) volume (0:ℝ) D := by
    simpa using (intervalIntegrable_const (μ := (volume)) (a := (0:ℝ)) (b := D) (c := J_max))
  have hmono :
      (∫ s in (0:ℝ)..D, fisherInfo (gaussConv f s))
        ≤ ∫ s in (0:ℝ)..D, J_max := by
    refine intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := D)
      (μ := volume) (f := fun s => fisherInfo (gaussConv f s))
      (g := fun _ => J_max) (hab := le_of_lt hD) (hf := hf) (hg := hg) hJ'
  have hconst :
      (∫ s in (0:ℝ)..D, J_max) = D * J_max := by
    simpa using (intervalIntegral.integral_const (c := J_max) (a := (0:ℝ)) (b := D))
  calc
    rateDistortionFunctionNats f D - diffEntropyNats f +
        (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * D)
        ≤ (1 / 2) * ∫ s in (0:ℝ)..D, fisherInfo (gaussConv f s) := h0
    _ ≤ (1 / 2) * ∫ s in (0:ℝ)..D, J_max := by
          nlinarith [hmono]
    _ = (D / 2) * J_max := by
          simp [hconst, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]

/--
Convert the nats bound to bits for practical use.
-/
theorem rdGap_bits_via_fisherBound (f : ℝ → ℝ) (D J_max : ℝ)
    (hD : 0 < D) (hJ : ∀ s, 0 ≤ s → s ≤ D → fisherInfo (gaussConv f s) ≤ J_max) :
  rateDistortionFunctionBits f D - diffEntropyBits f +
      (1/2) * log2 (2 * Real.pi * Real.exp 1 * D)
    ≤ (D / (2 * Real.log 2)) * J_max := by
  -- TODO: convert the nats bound to bits (algebraic rewrite + monotonicity of 1/log 2)
  sorry

end RateDistortion
