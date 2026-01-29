import Mathlib
import RateDistortion.Axioms
import RateDistortion.GGD.Basic

open scoped BigOperators
open MeasureTheory

noncomputable section
namespace RateDistortion

/-!
## Helper lemmas for GGD integration

The key to proving normalization and moments is the change of variables u = (|x|/α)^β.
This transforms the integral into a form involving the Gamma function.
-/

/-- The GGD density is integrable. -/
theorem ggdDensity_integrable {beta alpha : ℝ} (hbeta : 0 < beta) (halpha : 0 < alpha) :
  Integrable (ggdDensity beta alpha) volume := by
  -- Follows from integrable_exp_abs_beta and scaling
  have h0 : Integrable (fun x => Real.exp (-|x| ^ beta)) volume :=
    integrable_exp_abs_beta beta hbeta
  have h1' :
      Integrable (fun x => Real.exp (-|x / alpha| ^ beta)) volume := by
    -- Use scaling: x ↦ x / alpha
    have h :=
      (MeasureTheory.Integrable.comp_div (g := fun x => Real.exp (-|x| ^ beta)) h0
        (by exact ne_of_gt halpha))
    simpa using h
  have h1 :
      Integrable (fun x => Real.exp (-(|x| / alpha) ^ beta)) volume := by
    simpa [abs_div, abs_of_nonneg (le_of_lt halpha)] using h1'
  -- Pull out the constant ggdC
  have h2 := h1.const_mul (ggdC beta alpha)
  -- unfold the definition to match the integrand
  unfold ggdDensity
  simpa using h2

/-- The GGD density is nonnegative. -/
theorem ggdDensity_nonneg {beta alpha : ℝ} (hbeta : 0 < beta) (halpha : 0 < alpha) :
  ∀ x, 0 ≤ ggdDensity beta alpha x := by
  intro x
  have hGammaPos : 0 < Real.Gamma (1 / beta) := by
    exact Real.Gamma_pos_of_pos (one_div_pos.mpr hbeta)
  have hden : 0 < 2 * alpha * Real.Gamma (1 / beta) := by
    have h2a : 0 < 2 * alpha := by nlinarith [halpha]
    exact mul_pos h2a hGammaPos
  have hCpos : 0 < ggdC beta alpha := by
    unfold ggdC
    exact div_pos hbeta hden
  have hCnonneg : 0 ≤ ggdC beta alpha := le_of_lt hCpos
  have hExp : 0 ≤ Real.exp (-(|x| / alpha) ^ beta) := by
    exact le_of_lt (Real.exp_pos _)
  unfold ggdDensity
  exact mul_nonneg hCnonneg hExp

/-- Normalization: integral of the density is one. -/
theorem ggd_integral_eq_one {beta alpha : ℝ} (hbeta : 0 < beta) (halpha : 0 < alpha) :
    (∫ x : ℝ, ggdDensity beta alpha x) = 1 := by
  unfold ggdDensity ggdC
  -- Strategy:
  -- 1. Use integral_const_mul to factor out C = β/(2α·Γ(1/β))
  -- 2. Change of variables: y = x / α (scale by α)
  --    Then ∫ exp(-(|x|/α)^β) dx = α · ∫ exp(-|y|^β) dy
  -- 3. Apply integral_exp_abs_beta: ∫ exp(-|y|^β) dy = (2/β) Γ(1/β)
  -- 4. Combine: C · α · (2/β) Γ(1/β) = [β/(2α·Γ(1/β))] · α · (2/β) Γ(1/β) = 1
  have hbeta0 : beta ≠ 0 := ne_of_gt hbeta
  have halpha0 : alpha ≠ 0 := ne_of_gt halpha
  have hGammaPos : 0 < Real.Gamma (1 / beta) := by
    exact Real.Gamma_pos_of_pos (one_div_pos.mpr hbeta)
  have hGamma0 : Real.Gamma (1 / beta) ≠ 0 := ne_of_gt hGammaPos
  have hscale :
      (∫ x : ℝ, Real.exp (-(|x| / alpha) ^ beta))
        = alpha * ∫ x : ℝ, Real.exp (-|x| ^ beta) := by
    -- scale x ↦ x / alpha
    have h :=
      (MeasureTheory.Measure.integral_comp_div
        (g := fun x : ℝ => Real.exp (-|x| ^ beta)) (a := alpha))
    -- |x|/alpha = |x/alpha| for alpha > 0
    simpa [abs_div, abs_of_nonneg (le_of_lt halpha), smul_eq_mul] using h
  have hbase :
      (∫ x : ℝ, Real.exp (-|x| ^ beta)) =
        (2 / beta) * Real.Gamma (1 / beta) :=
    integral_exp_abs_beta beta hbeta
  calc
    (∫ x : ℝ, beta / (2 * alpha * Real.Gamma (1 / beta)) *
        Real.exp (-(|x| / alpha) ^ beta))
        =
        (beta / (2 * alpha * Real.Gamma (1 / beta))) *
          (∫ x : ℝ, Real.exp (-(|x| / alpha) ^ beta)) := by
          simpa using
            (MeasureTheory.integral_const_mul
              (beta / (2 * alpha * Real.Gamma (1 / beta)))
              (fun x : ℝ => Real.exp (-(|x| / alpha) ^ beta)))
    _ = (beta / (2 * alpha * Real.Gamma (1 / beta))) *
          (alpha * (∫ x : ℝ, Real.exp (-|x| ^ beta))) := by
          simpa [hscale]
    _ = (beta / (2 * alpha * Real.Gamma (1 / beta))) *
          (alpha * ((2 / beta) * Real.Gamma (1 / beta))) := by
          simp [hbase]
    _ = 1 := by
          field_simp [hbeta0, halpha0, hGamma0]

/-- The GGD density is a probability density. -/
theorem ggd_isDensity {beta alpha : ℝ} (hbeta : 0 < beta) (halpha : 0 < alpha) :
  IsDensity (ggdDensity beta alpha) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact ggdDensity_nonneg hbeta halpha x
  · exact ggdDensity_integrable hbeta halpha
  · exact ggd_integral_eq_one hbeta halpha

/-- Absolute moment formula. -/
theorem ggd_abs_moment_integral
  {beta alpha p : ℝ} (hbeta : 0 < beta) (halpha : 0 < alpha) (hp : -1 < p) :
  (∫ x : ℝ, (|x|) ^ p * ggdDensity beta alpha x)
    = alpha ^ p * Real.Gamma ((p + 1) / beta) / Real.Gamma (1 / beta) := by
  unfold ggdDensity ggdC
  -- Strategy:
  -- 1. Factor out constant C
  -- 2. Rearrange: ∫ |x|^p · C · exp(-(|x|/α)^β) dx
  -- 3. Substitute y = x/α: |x| = α|y|, dx = α dy
  --    = C · α · ∫ (α|y|)^p · exp(-|y|^β) dy
  --    = C · α^(p+1) · ∫ |y|^p · exp(-|y|^β) dy
  -- 4. Apply integral_power_exp_abs_beta:
  --    ∫ |y|^p · exp(-|y|^β) dy = (2/β) Γ((p+1)/β)
  -- 5. Combine:
  --    C · α^(p+1) · (2/β) Γ((p+1)/β)
  --    = [β/(2α·Γ(1/β))] · α^(p+1) · (2/β) Γ((p+1)/β)
  --    = α^p · Γ((p+1)/β) / Γ(1/β)
  have hbeta0 : beta ≠ 0 := ne_of_gt hbeta
  have halpha0 : alpha ≠ 0 := ne_of_gt halpha
  have hGammaPos : 0 < Real.Gamma (1 / beta) := by
    exact Real.Gamma_pos_of_pos (one_div_pos.mpr hbeta)
  have hGamma0 : Real.Gamma (1 / beta) ≠ 0 := ne_of_gt hGammaPos
  have hscale :
      (∫ x : ℝ, (|x|) ^ p * Real.exp (-(|x| / alpha) ^ beta))
        =
        alpha ^ (p + 1) * ∫ x : ℝ, (|x|) ^ p * Real.exp (-|x| ^ beta) := by
    -- Use scaling x ↦ x / alpha, and pull out alpha^p
    have h :=
      (MeasureTheory.Measure.integral_comp_div
        (g := fun y : ℝ => (|alpha * y|) ^ p * Real.exp (-|y| ^ beta)) (a := alpha))
    -- rewrite |alpha * y|^p as alpha^p * |y|^p (alpha > 0)
    have h' :
        (∫ x : ℝ, (|x|) ^ p * Real.exp (-(|x| / alpha) ^ beta))
          =
          alpha * ∫ y : ℝ, (|alpha * y|) ^ p * Real.exp (-|y| ^ beta) := by
      -- simplify |alpha * (x/alpha)| and |x/alpha|
      have hsim :
          (fun x : ℝ =>
            (alpha * (|x| * alpha⁻¹)) ^ p * Real.exp (-(|x| * alpha⁻¹) ^ beta)) =
            fun x : ℝ => (|x|) ^ p * Real.exp (-(|x| / alpha) ^ beta) := by
        funext x
        have hmul : alpha * (|x| * alpha⁻¹) = |x| := by
          calc
            alpha * (|x| * alpha⁻¹) = |x| * (alpha * alpha⁻¹) := by ring
            _ = |x| := by simp [halpha0]
        simp [hmul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      simpa [abs_div, abs_of_nonneg (le_of_lt halpha), smul_eq_mul, div_eq_mul_inv, hsim] using h
    -- pull out alpha^p
    have h'' :
        (∫ y : ℝ, (|alpha * y|) ^ p * Real.exp (-|y| ^ beta))
          =
          alpha ^ p * ∫ y : ℝ, (|y|) ^ p * Real.exp (-|y| ^ beta) := by
      -- |alpha*y|^p = alpha^p * |y|^p for alpha ≥ 0
      have hα : 0 ≤ alpha := le_of_lt halpha
      have hαabs : |alpha| = alpha := abs_of_nonneg hα
      calc
        (∫ y : ℝ, (|alpha * y|) ^ p * Real.exp (-|y| ^ beta))
            = (∫ y : ℝ, (alpha ^ p * (|y| ^ p)) * Real.exp (-|y| ^ beta)) := by
                refine integral_congr_ae ?_
                refine MeasureTheory.ae_of_all volume ?_
                intro y
                have hmul :
                    (|alpha| * |y|) ^ p = alpha ^ p * |y| ^ p := by
                  -- use abs_mul and mul_rpow
                  calc
                    (|alpha| * |y|) ^ p = |alpha| ^ p * |y| ^ p := by
                      simpa using (Real.mul_rpow (x := |alpha|) (y := |y|) (z := p)
                        (by exact abs_nonneg alpha) (by exact abs_nonneg y))
                    _ = alpha ^ p * |y| ^ p := by simpa [hαabs]
                simp [abs_mul, hmul, mul_left_comm, mul_assoc, mul_comm]
        _ = alpha ^ p * ∫ y : ℝ, (|y|) ^ p * Real.exp (-|y| ^ beta) := by
              simpa [mul_left_comm, mul_assoc] using
                (MeasureTheory.integral_const_mul
                  (alpha ^ p)
                  (fun y : ℝ => (|y|) ^ p * Real.exp (-|y| ^ beta)))
    calc
      (∫ x : ℝ, (|x|) ^ p * Real.exp (-(|x| / alpha) ^ beta))
          = alpha * (alpha ^ p * ∫ y : ℝ, (|y|) ^ p * Real.exp (-|y| ^ beta)) := by
              simpa [h'] using congrArg (fun z => alpha * z) h''
      _ = alpha ^ (p + 1) * ∫ y : ℝ, (|y|) ^ p * Real.exp (-|y| ^ beta) := by
              -- use rpow_add to combine alpha * alpha^p
              have hαpos : 0 < alpha := halpha
              have hpow : alpha ^ p * alpha = alpha ^ (p + 1) := by
                have h := Real.rpow_add (x := alpha) (y := p) (z := 1) hαpos
                -- h : alpha^(p+1) = alpha^p * alpha^1
                simpa [Real.rpow_one, mul_comm, mul_left_comm, mul_assoc] using h.symm
              -- rearrange products
              calc
                alpha * (alpha ^ p * ∫ y : ℝ, (|y|) ^ p * Real.exp (-|y| ^ beta))
                    = (alpha ^ p * alpha) * ∫ y : ℝ, (|y|) ^ p * Real.exp (-|y| ^ beta) := by
                        ring
                _ = alpha ^ (p + 1) * ∫ y : ℝ, (|y|) ^ p * Real.exp (-|y| ^ beta) := by
                        simpa [hpow, mul_comm, mul_left_comm, mul_assoc]
  have hbase :
      (∫ x : ℝ, (|x|) ^ p * Real.exp (-|x| ^ beta)) =
        (2 / beta) * Real.Gamma ((p + 1) / beta) :=
    integral_power_exp_abs_beta beta p hbeta hp
  calc
    (∫ x : ℝ, (|x|) ^ p * (beta / (2 * alpha * Real.Gamma (1 / beta)) *
        Real.exp (-(|x| / alpha) ^ beta)))
        =
        (beta / (2 * alpha * Real.Gamma (1 / beta))) *
          (∫ x : ℝ, (|x|) ^ p * Real.exp (-(|x| / alpha) ^ beta)) := by
          simpa [mul_left_comm, mul_assoc, mul_comm] using
            (MeasureTheory.integral_const_mul
              (beta / (2 * alpha * Real.Gamma (1 / beta)))
              (fun x : ℝ => (|x|) ^ p * Real.exp (-(|x| / alpha) ^ beta)))
    _ = (beta / (2 * alpha * Real.Gamma (1 / beta))) *
          (alpha ^ (p + 1) *
            (∫ x : ℝ, (|x|) ^ p * Real.exp (-|x| ^ beta))) := by
          simp [hscale]
    _ = (beta / (2 * alpha * Real.Gamma (1 / beta))) *
          (alpha ^ (p + 1) * ((2 / beta) * Real.Gamma ((p + 1) / beta))) := by
          simp [hbase]
    _ = alpha ^ p * Real.Gamma ((p + 1) / beta) / Real.Gamma (1 / beta) := by
          have hαpos : 0 < alpha := halpha
          have hpow : alpha ^ (p + 1) = alpha * alpha ^ p := by
            have h := Real.rpow_add (x := alpha) (y := 1) (z := p) hαpos
            -- h : alpha^(1+p) = alpha^1 * alpha^p
            simpa [add_comm, Real.rpow_one, mul_comm, mul_left_comm, mul_assoc] using h
          field_simp [hbeta0, halpha0, hGamma0]
          simp [hpow, mul_comm, mul_left_comm, mul_assoc]

/-- Second moment (variance) formula. -/
theorem ggd_second_moment
  {beta alpha : ℝ} (hbeta : 0 < beta) (halpha : 0 < alpha) :
  (∫ x : ℝ, x ^ 2 * ggdDensity beta alpha x)
    = alpha ^ 2 * Real.Gamma (3 / beta) / Real.Gamma (1 / beta) := by
  -- This follows from ggd_abs_moment_integral with p = 2
  -- Since x^2 = |x|^2 for all x, we have:
  -- ∫ x^2 · f(x) dx = ∫ |x|^2 · f(x) dx
  --                 = α^2 · Γ(3/β) / Γ(1/β)
  have h := ggd_abs_moment_integral (beta := beta) (alpha := alpha) (p := 2)
      hbeta halpha (by linarith : (-1 : ℝ) < 2)
  -- Rewrite x^2 as |x|^2 inside the integral
  have h' :
      (∫ x : ℝ, x ^ 2 * ggdDensity beta alpha x) =
        ∫ x : ℝ, (|x|) ^ 2 * ggdDensity beta alpha x := by
    refine integral_congr_ae ?_
    refine MeasureTheory.ae_of_all volume ?_
    intro x
    simp [sq_abs, pow_two]
  have h3 : (2 + 1 : ℝ) = 3 := by norm_num
  simpa [h', h3] using h

end RateDistortion
